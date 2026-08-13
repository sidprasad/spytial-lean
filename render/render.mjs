// Renders every <casesDir>/<name>/props.json to <outDir>/<name>.png inside
// ./Dockerfile's container. Error renders are captured too — the per-case
// report and metrics.json carry the widget's error signals.
//
//   node render.mjs [casesDir] [outDir]
//
// Both default to ./cases and ./out beside this script; pass absolute paths
// when the cases live in a downstream repo (see README.md).
import fs from 'fs';
import path from 'path';
import { fileURLToPath, pathToFileURL } from 'url';
import { chromium } from '@playwright/test';

const here = path.dirname(fileURLToPath(import.meta.url));
const casesDir = path.resolve(process.argv[2] ?? path.join(here, 'cases'));
const outRoot = path.resolve(process.argv[3] ?? path.join(here, 'out'));
const harnessJs = path.join(here, 'dist', 'harness.js');

if (!fs.existsSync(harnessJs)) {
  console.error(`missing ${harnessJs} — run: lake build renderHarnessJs`);
  process.exit(1);
}
const cases = fs.existsSync(casesDir)
  ? fs.readdirSync(casesDir).filter(c => fs.existsSync(path.join(casesDir, c, 'props.json'))).sort()
  : [];
if (cases.length === 0) {
  console.error(`no cases under ${casesDir} — run a #spytial_snapshot file via \`lake env lean\``);
  process.exit(1);
}

function pageHtml(props) {
  const json = JSON.stringify(props).replace(/</g, '\\u003c');
  return `<!DOCTYPE html>
<html>
<head><meta charset="utf-8"><title>spytial-render-case</title>
<!-- No font-family: the captured SVG's typeface comes from spytial-core. -->
<style>body { margin: 8px; background: #ffffff; }</style>
</head>
<body>
<script>window.__CASE__ = ${json};</script>
<div id="root"></div>
<script src="${pathToFileURL(harnessJs).href}"></script>
</body>
</html>
`;
}

const SETTLE_TIMEOUT_MS = 60_000;

/** Settle protocol (see README.md): poll the recorded widget events from the
    node side — headless Chromium throttles in-page timers, CDP evaluates run. */
async function settle(page) {
  const deadline = Date.now() + SETTLE_TIMEOUT_MS;
  while (Date.now() < deadline) {
    const done = await page.evaluate(() =>
      !!document.querySelector('.spytial-error') ||
      !!window.__spytialEvents?.some(e => e === 'layout-complete' ||
        e === 'constraint-error' || e === 'layout-generation-error'));
    if (done) return true;
    await new Promise(r => setTimeout(r, 250));
  }
  return false;
}

const browser = await chromium.launch({
  // Hinting, subpixel AA and Skia's SIMD paths vary with the host CPU, so
  // these pin rasterization to keep renders comparable across machines.
  args: [
    '--font-render-hinting=none',
    '--disable-lcd-text',
    '--disable-font-subpixel-positioning',
    '--disable-skia-runtime-opts',
    '--force-color-profile=srgb',
    '--hide-scrollbars',
  ],
});
const context = await browser.newContext({
  viewport: { width: 1280, height: 800 },
  deviceScaleFactor: 1,
});

let failures = 0;
for (const name of cases) {
  const props = JSON.parse(fs.readFileSync(path.join(casesDir, name, 'props.json'), 'utf8'));
  const outDir = path.join(outRoot, name);
  fs.mkdirSync(outDir, { recursive: true });
  const pagePath = path.join(outDir, 'page.html');
  fs.writeFileSync(pagePath, pageHtml(props));

  const page = await context.newPage();
  try {
    await page.goto(pathToFileURL(pagePath).href);
    const settled = await settle(page);

    const dump = await page.evaluate(() => window.__spytialFinish()).catch(() => null);
    if (dump) {
      const { svg, ...metrics } = dump;
      if (svg) fs.writeFileSync(path.join(outDir, 'render.svg'), svg);
      fs.writeFileSync(path.join(outDir, 'metrics.json'), JSON.stringify(metrics, null, 1) + '\n');
    }

    if (!settled) {
      failures++;
      console.error(`${name}: never settled (no layout event, no error) after ${SETTLE_TIMEOUT_MS}ms`);
      continue;
    }

    // A clean settle can still hide dropped constraints; report every
    // non-clean signal next to the image it explains.
    const notes = [];
    if (dump?.error) notes.push(`widget error: ${dump.error}`);
    for (const e of dump?.events ?? []) {
      if (e === 'constraint-error' || e === 'layout-generation-error') notes.push(e);
    }
    if (dump?.errorModal) notes.push('error modal open');
    const toastVisible = await page.evaluate(() => {
      const toast = document.querySelector('webcola-cnd-graph')?.shadowRoot?.querySelector('#loading');
      return !!toast && toast.classList.contains('visible');
    });
    if (toastVisible) notes.push('layout-progress toast still visible at settle');

    // Diagram SVG only: the toolbar's native <select>s are the most
    // machine-dependent paint on the page.
    const svgEl = page.locator('webcola-cnd-graph svg');
    if (await svgEl.count()) {
      await svgEl.screenshot({ path: path.join(outRoot, `${name}.png`) });
    } else {
      await page.screenshot({ path: path.join(outRoot, `${name}.png`) });
      notes.push('no diagram svg — captured the full page');
    }

    const stats = dump ? `${dump.nodes.length} nodes, ${dump.edges.length} edges` : 'no metrics';
    console.log(`${name}: ${notes.length ? 'rendered with warnings' : 'ok'} (${stats})`);
    for (const n of notes) console.log(`  - ${n}`);
  } finally {
    await page.close();
  }
}

await browser.close();
process.exit(failures ? 1 : 0);
