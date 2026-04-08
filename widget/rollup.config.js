import { nodeResolve } from '@rollup/plugin-node-resolve';
import commonjs from '@rollup/plugin-commonjs';
import replace from '@rollup/plugin-replace';
import terser from '@rollup/plugin-terser';
import virtual from '@rollup/plugin-virtual';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));

// Load the pre-built spytial-core IIFE bundle and re-export as ES module.
// The IIFE assigns to `var spytialcore = (function() { ... })()`,
// which becomes a module-scoped variable that we then export.
const spytialCorePath = path.resolve(__dirname, 'node_modules/spytial-core/dist/browser/spytial-core-complete.global.js');
let spytialCoreBundle = '';
try {
  spytialCoreBundle = fs.readFileSync(spytialCorePath, 'utf-8');
} catch (e) {
  console.warn(`Warning: spytial-core bundle not found at ${spytialCorePath}. Build spytial-core first.`);
}

// Load the components bundle (provides mountErrorMessageModal, ErrorAPI, globalErrorManager)
const componentsPath = path.resolve(__dirname, 'node_modules/spytial-core/dist/components/react-component-integration.global.js');
let componentsBundle = '';
try {
  componentsBundle = fs.readFileSync(componentsPath, 'utf-8');
} catch (e) {
  console.warn(`Warning: spytial-core components bundle not found at ${componentsPath}. Build spytial-core first.`);
}

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
    // Handle CSS imports from spytial-core source as no-ops
    // (we inject equivalent styles in the widget itself)
    {
      name: 'css-noop',
      resolveId(source) {
        if (source.endsWith('.css')) return source;
        return null;
      },
      load(id) {
        if (id.endsWith('.css')) return '';
        return null;
      }
    },
    virtual({
      'spytial-core': `
        // Guard against duplicate customElements.define calls —
        // the IIFE bundle registers webcola-cnd-graph on load, and
        // if the module is re-evaluated we get a fatal error.
        var _origDefine = typeof customElements !== 'undefined' ? customElements.define.bind(customElements) : undefined;
        if (typeof customElements !== 'undefined') {
          customElements.define = function(name, ctor, opts) {
            if (!customElements.get(name)) _origDefine(name, ctor, opts);
          };
        }
        ${spytialCoreBundle}
        if (typeof customElements !== 'undefined' && _origDefine) {
          customElements.define = _origDefine;
        }
        export default typeof spytialcore !== 'undefined' ? spytialcore : {};
      `,
      'spytial-core-components': `
        ${componentsBundle}
        export default typeof IntegratedDemo !== 'undefined' ? IntegratedDemo : {};
      `
    }),
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
