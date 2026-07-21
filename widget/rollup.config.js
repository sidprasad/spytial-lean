import { nodeResolve } from '@rollup/plugin-node-resolve';
import commonjs from '@rollup/plugin-commonjs';
import replace from '@rollup/plugin-replace';
import terser from '@rollup/plugin-terser';
import { cssNoop, spytialCoreVirtualModules } from './rollup.virtual.mjs';

const isProduction = process.env.NODE_ENV === 'production';

/** @type {import('rollup').RollupOptions} */
export default {
  input: 'dist/spytialWidget.js',
  output: {
    dir: '../.lake/build/js',
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
    cssNoop(),
    spytialCoreVirtualModules(),
    nodeResolve({ browser: true }),
    replace({
      'typeof window': JSON.stringify('object'),
      'process.env.NODE_ENV': JSON.stringify(process.env.NODE_ENV || 'production'),
      preventAssignment: true
    }),
    commonjs({
      ignore: [
        'process', 'events', 'stream', 'util', 'path', 'buffer', 'querystring', 'url',
        'string_decoder', 'punycode', 'http', 'https', 'os', 'assert', 'constants',
        'timers', 'console', 'vm', 'zlib', 'tty', 'domain', 'dns', 'dgram', 'child_process',
        'cluster', 'module', 'net', 'readline', 'repl', 'tls', 'fs', 'crypto', 'perf_hooks',
      ],
    })
  ],
};
