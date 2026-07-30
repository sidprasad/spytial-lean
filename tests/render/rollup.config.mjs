// Bundles the harness page into one self-contained IIFE a file:// page can load
// with no network. Unlike the infoview bundle, react is NOT external — there's
// no infoview here to provide it.
//
// Build with `lake build renderHarnessJs` (rebuilds the widget first).
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
