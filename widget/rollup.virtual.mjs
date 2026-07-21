// spytial-core virtual-module + CSS-noop helpers, factored out of
// rollup.config.js. spytial-core ships as pre-built IIFE bundles that can't be
// imported as ordinary ES modules, so we wrap each in a virtual module that
// runs the IIFE and re-exports the global it assigns.
import virtual from '@rollup/plugin-virtual';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const widgetDir = path.dirname(fileURLToPath(import.meta.url));

function readBundle(rel) {
  const p = path.resolve(widgetDir, rel);
  try {
    return fs.readFileSync(p, 'utf-8');
  } catch (e) {
    console.warn(`Warning: bundle not found at ${p}. Build spytial-core first.`);
    return '';
  }
}

/** Handle CSS imports from spytial-core source as no-ops
    (equivalent styles are injected at runtime by the widget itself). */
export function cssNoop() {
  return {
    name: 'css-noop',
    resolveId(source) {
      if (source.endsWith('.css')) return source;
      return null;
    },
    load(id) {
      if (id.endsWith('.css')) return '';
      return null;
    }
  };
}

/** Virtual modules wrapping the pre-built spytial-core IIFE bundles.
    The IIFE assigns to `var spytialcore = (function() { ... })()`,
    which becomes a module-scoped variable that we then export. */
export function spytialCoreVirtualModules() {
  const spytialCoreBundle = readBundle('node_modules/spytial-core/dist/browser/spytial-core-complete.global.js');
  const componentsBundle = readBundle('node_modules/spytial-core/dist/components/react-component-integration.global.js');
  return virtual({
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
  });
}
