// Image-snapshot tests: one test per cases/<name>/props.json (dumped by
// tests/render/Cases.lean), each mounting the real infoview widget on those
// props in headless Chrome and comparing a stabilized screenshot against
// baseline/<name>.png. `--update-snapshots` re-blesses baselines.
//
// The page under test is passive (entry.mjs just mounts the widget and
// records the graph element's lifecycle events); completion is detected by
// polling for its layout-complete CustomEvent from the node side — headless
// Chrome throttles in-page timers, CDP evaluates always run.
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
<style>body { margin: 8px; font-family: sans-serif; background: #ffffff; }</style>
</head>
<body>
<script>window.__CASE__ = ${json};</script>
<div id="root"></div>
<script src="../../dist/harness.js"></script>
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
        !!document.querySelector('.spytial-error') || window.__spytialEvents?.length > 0),
        { message: 'widget produced neither a layout event nor an error' })
      .toBe(true);
    const widgetError = await page.evaluate(
      () => document.querySelector('.spytial-error')?.textContent ?? null);
    expect(widgetError, 'widget rendered its error state').toBeNull();
    const events = await page.evaluate(() => window.__spytialEvents);
    expect(events).toContain('layout-complete');
    expect(events).not.toContain('constraint-error');
    expect(events).not.toContain('layout-generation-error');

    try {
      // toHaveScreenshot waits for two consecutive identical shots, so any
      // post-layout animation tail settles before the comparison.
      await expect(page).toHaveScreenshot(`${name}.png`);
    } finally {
      const { svg, ...metrics } = await page.evaluate(() => window.__spytialFinish());
      if (svg) fs.writeFileSync(path.join(outDir, 'render.svg'), svg);
      fs.writeFileSync(path.join(outDir, 'metrics.json'), JSON.stringify(metrics, null, 1) + '\n');
    }
  });
}
