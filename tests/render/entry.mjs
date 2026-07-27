// Render-harness page entry: mounts the real infoview widget component
// (widget/dist/spytialWidget.js — the same tsc output the infoview bundle is
// built from) on the case props injected as `window.__CASE__`, records the
// graph element's lifecycle events, and exposes a serialization hook. All
// waiting/asserting lives in render.spec.mjs on the node side — headless
// Chrome throttles in-page timers, so the page stays passive.
import * as React from 'react';
import { createRoot } from 'react-dom/client';
import SpytialWidget from '../../widget/dist/spytialWidget.js';

// webcola-cnd-graph dispatches these on itself; layout-complete does not
// bubble, but capture-phase listeners on document still see it.
window.__spytialEvents = [];
for (const type of ['layout-complete', 'constraints-satisfied',
                    'constraint-error', 'layout-generation-error']) {
  document.addEventListener(type, () => window.__spytialEvents.push(type), true);
}

function round(x) {
  return Math.round(x * 100) / 100;
}

// Geometry read back from the live SVG with real layout APIs — the part no
// jsdom-style harness can see. Selectors match webcola-cnd-graph's DOM
// vocabulary: g.node / path[data-link-id] / rect.group.
function metricsOf(svg) {
  const nodes = [...svg.querySelectorAll('g.node, g.error-node')].map(g => {
    const r = g.getBoundingClientRect();
    const rect = g.querySelector('rect');
    return {
      label: (g.querySelector('.label')?.textContent ?? '').trim(),
      x: round(r.x + r.width / 2),
      y: round(r.y + r.height / 2),
      w: round(r.width),
      h: round(r.height),
      fill: rect ? (rect.style.fill || rect.getAttribute('fill')) : null,
    };
  });
  const edges = [...svg.querySelectorAll('path[data-link-id]')].map(p => {
    const id = p.getAttribute('data-link-id');
    // Paths with no `d` (getPointAtLength throws on them) still count as
    // edges — a non-null straightness is the signal the edge was routed.
    const len = p.getAttribute('d') ? p.getTotalLength() : 0;
    if (len === 0) return { id, len: 0, straightness: null };
    const a = p.getPointAtLength(0);
    const b = p.getPointAtLength(len);
    const chord = Math.hypot(b.x - a.x, b.y - a.y);
    return { id, len: round(len), straightness: round(chord / len) };
  });
  const groups = [...svg.querySelectorAll('rect.group')].map(r => ({
    label: r.getAttribute('data-group-label') ?? null,
    w: round(r.getBoundingClientRect().width),
    h: round(r.getBoundingClientRect().height),
  }));
  return { nodes, edges, groups };
}

// Full serialization, taken by the spec once layout-complete has fired.
window.__spytialFinish = () => {
  const svg = document.querySelector('webcola-cnd-graph')?.shadowRoot?.querySelector('svg') ?? null;
  const errorEl = document.querySelector('.spytial-error');
  const modal = document.getElementById('error-message-modal');
  return {
    events: window.__spytialEvents,
    error: errorEl ? errorEl.textContent : null,
    errorModal: modal ? modal.textContent.slice(0, 500) : null,
    svg: svg ? svg.outerHTML : null,
    ...(svg ? metricsOf(svg) : { nodes: [], edges: [], groups: [] }),
  };
};

createRoot(document.getElementById('root')).render(
  React.createElement(SpytialWidget, window.__CASE__));
