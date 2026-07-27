// Bundles the render-harness page (entry.mjs + the real widget component +
// react + the spytial-core virtual modules) into one self-contained IIFE that
// a file:// page can load with no network. Unlike the infoview bundle, react
// is NOT external here — headless Chrome has no infoview to provide it.
//
// Run from widget/ (where rollup lives): npx rollup --config ../tests/render/rollup.config.mjs
import path from 'path';
import { fileURLToPath } from 'url';
import { nodeResolve } from '@rollup/plugin-node-resolve';
import commonjs from '@rollup/plugin-commonjs';
import replace from '@rollup/plugin-replace';
import { cssNoop, spytialCoreVirtualModules } from '../../widget/rollup.virtual.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));

/** @type {import('rollup').RollupOptions} */
export default {
  input: path.join(here, 'entry.mjs'),
  output: {
    file: path.join(here, 'dist', 'harness.js'),
    format: 'iife',
    intro: 'const global = window;',
    sourcemap: false,
  },
  plugins: [
    cssNoop(),
    spytialCoreVirtualModules(),
    nodeResolve({ browser: true }),
    replace({
      'process.env.NODE_ENV': JSON.stringify('production'),
      preventAssignment: true
    }),
    commonjs(),
  ],
  onwarn(warning, warn) {
    if (warning.code === 'CIRCULAR_DEPENDENCY' || warning.code === 'THIS_IS_UNDEFINED') return;
    warn(warning);
  },
};
