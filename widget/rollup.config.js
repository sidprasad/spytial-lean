import { nodeResolve } from '@rollup/plugin-node-resolve';
import commonjs from '@rollup/plugin-commonjs';
import replace from '@rollup/plugin-replace';
import terser from '@rollup/plugin-terser';

const isProduction = process.env.NODE_ENV === 'production';

/** @type {import('rollup').RollupOptions} */
export default {
  input: 'dist/spytialWidget.js',
  output: {
    file: '../.lake/build/js/spytialWidget.js',
    inlineDynamicImports: true,
    format: 'es',
    intro: 'const global = window;',
    sourcemap: isProduction ? false : 'inline',
    plugins: isProduction ? [terser()] : [],
    compact: isProduction
  },
  external: [
    'react',
    'react-dom',
    'react/jsx-runtime',
    '@leanprover/infoview',
  ],
  plugins: [
    nodeResolve({ browser: true }),
    replace({
      'process.env.NODE_ENV': JSON.stringify(process.env.NODE_ENV || 'production'),
      preventAssignment: true
    }),
    commonjs()
  ],
};
