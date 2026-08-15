// One test per cases/<name>/props.json (dumped by Cases.lean), each mounting the
// widget on those props and comparing a stabilized screenshot of the diagram
// against baseline/<name>.png. See ./README.md for the settle protocol.
import { test, expect } from '@playwright/test';
import fs from 'fs';
import path from 'path';
import { fileURLToPath, pathToFileURL } from 'url';

const here = path.dirname(fileURLToPath(import.meta.url));
const casesDir = path.join(here, 'cases');
const outRoot = path.join(here, 'out');

const cases = fs.existsSync(casesDir)
  ? fs.readdirSync(casesDir).filter(c => fs.existsSync(path.join(casesDir, c, 'props.json'))).sort()
  : [];
if (cases.length === 0) {
  throw new Error('no render cases found — run: lake env lean tests/render/Cases.lean');
}

function pageHtml(props) {
  const json = JSON.stringify(props).replace(/</g, '\\u003c');
  return `<!DOCTYPE html>
<html>
<head><meta charset="utf-8"><title>spytial-render-case</title>
<!-- No font-family here on purpose: the captured region is the diagram SVG,
     whose typeface spytial-core sets itself (see ../../render/Dockerfile). -->
<style>body { margin: 8px; background: #ffffff; }</style>
</head>
<body>
<script>window.__CASE__ = ${json};</script>
<div id="root"></div>
<script src="../../../../render/dist/harness.js"></script>
</body>
</html>
`;
}

for (const name of cases) {
  test(name, async ({ page }) => {
    const props = JSON.parse(fs.readFileSync(path.join(casesDir, name, 'props.json'), 'utf8'));
    const outDir = path.join(outRoot, name);
    fs.mkdirSync(outDir, { recursive: true });
    const pagePath = path.join(outDir, 'page.html');
    fs.writeFileSync(pagePath, pageHtml(props));
    await page.goto(pathToFileURL(pagePath).href);

    await expect
      .poll(() => page.evaluate(() =>
        !!document.querySelector('.spytial-error') ||
        !!window.__spytialEvents?.some(e => e === 'layout-complete' ||
          e === 'constraint-error' || e === 'layout-generation-error')),
        { message: 'widget produced neither a layout event nor an error' })
      .toBe(true);
    const widgetError = await page.evaluate(
      () => document.querySelector('.spytial-error')?.textContent ?? null);
    expect(widgetError, 'widget rendered its error state').toBeNull();
    const events = await page.evaluate(() => window.__spytialEvents);
    expect(events).toContain('layout-complete');
    expect(events).not.toContain('constraint-error');
    expect(events).not.toContain('layout-generation-error');
    // This toast produced the first generation of false baselines; assert it
    // rather than hoping the crop catches it.
    const toastVisible = await page.evaluate(() => {
      const toast = document.querySelector('webcola-cnd-graph')?.shadowRoot?.querySelector('#loading');
      return !!toast && toast.classList.contains('visible');
    });
    expect(toastVisible, 'layout-progress toast still visible at settle').toBe(false);

    try {
      // Diagram SVG only (the locator pierces the shadow root): the toolbar's
      // native <select>s are the most machine-dependent paint on the page.
      // toHaveScreenshot waits for two identical frames, settling any tail.
      await expect(page.locator('webcola-cnd-graph svg')).toHaveScreenshot(`${name}.png`);
    } finally {
      // Best-effort: if the page died, its diagnostics are gone, and throwing
      // here would replace the assertion failure that is the actual finding.
      const dump = await page.evaluate(() => window.__spytialFinish()).catch(() => null);
      if (dump) {
        const { svg, ...metrics } = dump;
        if (svg) fs.writeFileSync(path.join(outDir, 'render.svg'), svg);
        fs.writeFileSync(path.join(outDir, 'metrics.json'), JSON.stringify(metrics, null, 1) + '\n');
      }
    }
  });
}
