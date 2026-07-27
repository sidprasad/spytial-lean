import { defineConfig } from '@playwright/test';
import { spawnSync } from 'child_process';
import path from 'path';

// Playwright's bundled browsers don't run on NixOS; use the host Chrome
// (SPYTIAL_CHROME overrides). launchOptions needs an absolute path.
const chrome = (() => {
  const c = process.env.SPYTIAL_CHROME || 'google-chrome-stable';
  if (c.includes(path.sep)) return c;
  const found = spawnSync('which', [c], { encoding: 'utf8' }).stdout.trim();
  if (!found) throw new Error(`chrome not found on PATH: ${c} (set SPYTIAL_CHROME)`);
  return found;
})();

export default defineConfig({
  testDir: '.',
  testMatch: 'render.spec.mjs',
  outputDir: 'out/test-results',
  snapshotPathTemplate: '{testDir}/baseline/{arg}{ext}',
  fullyParallel: true,
  timeout: 60_000,
  expect: {
    timeout: 30_000,
    // Pixels allowed to differ — absorbs font antialiasing jitter, not
    // layout changes.
    toHaveScreenshot: { maxDiffPixels: 150 },
  },
  reporter: [['list'], ['html', { outputFolder: 'out/report', open: 'never' }]],
  use: {
    viewport: { width: 1280, height: 800 },
    launchOptions: { executablePath: chrome },
  },
});
