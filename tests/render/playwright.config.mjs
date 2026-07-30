// Runs inside ./Dockerfile's container, which supplies the browser and fonts;
// `just render` is the entry point.
import { defineConfig } from '@playwright/test';

export default defineConfig({
  testDir: '.',
  testMatch: 'render.spec.mjs',
  outputDir: 'out/test-results',
  snapshotPathTemplate: '{testDir}/baseline/{arg}{ext}',
  fullyParallel: true,
  timeout: 60_000,
  expect: {
    timeout: 30_000,
    // Absorbs antialiasing jitter, not layout changes.
    toHaveScreenshot: { maxDiffPixels: 150 },
  },
  reporter: [['list'], ['html', { outputFolder: 'out/report', open: 'never' }]],
  use: {
    viewport: { width: 1280, height: 800 },
    deviceScaleFactor: 1,
    launchOptions: {
      // Hinting, subpixel AA and Skia's SIMD paths vary with the host CPU, so
      // the image alone isn't enough to make baselines portable.
      args: [
        '--font-render-hinting=none',
        '--disable-lcd-text',
        '--disable-font-subpixel-positioning',
        '--disable-skia-runtime-opts',
        '--force-color-profile=srgb',
        '--hide-scrollbars',
      ],
    },
  },
});
