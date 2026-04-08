import * as React from 'react';
import { useRpcSession } from '@leanprover/infoview';
// @ts-ignore — virtual module created by rollup from the IIFE bundle
import spytialcore from 'spytial-core';

const { JSONDataInstance, LayoutInstance, parseLayoutSpec, SGraphQueryEvaluator } = spytialcore;

const SPYTIAL_CORE_VERSION = '2.3.0';
const CDN_BASE = `https://cdn.jsdelivr.net/npm/spytial-core@${SPYTIAL_CORE_VERSION}`;

let cssInjected = false;
function injectCss() {
  if (cssInjected) return;
  cssInjected = true;
  const style = document.createElement('style');
  style.textContent = `
    webcola-cnd-graph {
      display: block;
      width: 100%;
      height: 100%;
    }
    webcola-cnd-graph svg {
      width: 100%;
      height: 100%;
    }
    .spytial-loading {
      padding: 8px;
      color: var(--vscode-descriptionForeground);
    }
    .spytial-error {
      padding: 8px;
      color: var(--vscode-errorForeground);
    }
    .spytial-container {
      position: relative;
      overflow: hidden;
      border: 1px solid var(--vscode-panel-border, #333);
      border-radius: 4px;
    }
    .spytial-resize-handle {
      position: absolute;
      bottom: 0;
      right: 0;
      width: 16px;
      height: 16px;
      cursor: nwse-resize;
      opacity: 0.4;
    }
    .spytial-resize-handle:hover {
      opacity: 0.8;
    }
    .spytial-resize-handle::after {
      content: '';
      position: absolute;
      bottom: 3px;
      right: 3px;
      width: 8px;
      height: 8px;
      border-right: 2px solid var(--vscode-foreground);
      border-bottom: 2px solid var(--vscode-foreground);
    }
    .spytial-toolbar {
      display: flex;
      justify-content: flex-end;
      gap: 4px;
      padding: 4px 8px;
      background: var(--vscode-editorWidget-background, #252526);
      border-bottom: 1px solid var(--vscode-panel-border, #333);
    }
    .spytial-btn {
      background: var(--vscode-button-background, #0e639c);
      color: var(--vscode-button-foreground, #fff);
      border: none;
      padding: 3px 10px;
      border-radius: 3px;
      font-size: 11px;
      cursor: pointer;
      font-family: var(--vscode-font-family);
    }
    .spytial-btn:hover {
      background: var(--vscode-button-hoverBackground, #1177bb);
    }
  `;
  document.head.appendChild(style);
}

interface SpytialWidgetProps {
  dataInstance: {
    atoms: Array<{ id: string; type: string; label: string }>;
    relations: Array<{
      id: string;
      name: string;
      types: string[];
      tuples: Array<{ atoms: string[]; types: string[] }>;
    }>;
  };
  cndSpec?: string;
}

/**
 * Generate a self-contained HTML file that loads spytial-core from CDN
 * and renders the diagram. Follows the pattern from spytial-py's
 * visualizer_template.html.
 */
function generateHtml(dataInstance: any, cndSpec: string): string {
  const jsonData = JSON.stringify(dataInstance, null, 2);
  // Escape backticks and backslashes in the YAML spec for template literal embedding
  const escapedSpec = (cndSpec || '').replace(/\\/g, '\\\\').replace(/`/g, '\\`').replace(/\$/g, '\\$');

  return `<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Spytial Visualization</title>
  <script src="${CDN_BASE}/dist/browser/spytial-core-complete.global.js"><\/script>
  <script src="${CDN_BASE}/dist/components/react-component-integration.global.js"><\/script>
  <link rel="stylesheet" href="${CDN_BASE}/dist/components/react-component-integration.css" />
  <style>
    body {
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
      margin: 0; padding: 0;
      background: white;
      height: 100vh;
      display: flex;
      flex-direction: column;
    }
    .container {
      position: relative;
      border: 1px solid #e1e5e9;
      border-radius: 6px;
      overflow: hidden;
      background: white;
      flex: 1;
      display: flex;
      flex-direction: column;
    }
    .graph-wrapper {
      position: relative;
      min-height: 400px;
      flex: 1;
      display: flex;
    }
    #graph-container {
      width: 100%;
      height: 100%;
      min-height: 400px;
      display: block;
      flex: 1;
    }
    #error-message div {
      color: red; padding: 10px;
      border: 1px solid red;
      background-color: #ffe6e6;
      margin: 10px;
    }
  </style>
</head>
<body>
  <div class="container">
    <div class="graph-wrapper">
      <webcola-cnd-graph
        id="graph-container"
        width="1200"
        height="800"
        layoutFormat="default">
      </webcola-cnd-graph>
    </div>
  </div>
  <div id="error-message"></div>

  <script>
    const cndSpec = \`${escapedSpec}\`;
    const jsonData = ${jsonData};

    function getSpytialCore() {
      return [window.spytialcore, window.CndCore, window.CnDCore]
        .find(c => c && typeof c.JSONDataInstance === 'function' && typeof c.parseLayoutSpec === 'function');
    }

    async function loadGraph() {
      const core = getSpytialCore();
      if (!core) {
        document.getElementById('error-message').innerHTML =
          '<div><h3>Error</h3><p>spytial-core failed to load.</p></div>';
        return;
      }
      try {
        const dataInstance = new core.JSONDataInstance(jsonData);
        const evaluator = new core.SGraphQueryEvaluator();
        evaluator.initialize({ sourceData: dataInstance });
        const layoutSpec = core.parseLayoutSpec(cndSpec);
        const layoutInstance = new core.LayoutInstance(layoutSpec, evaluator, 0, true);
        const layoutResult = layoutInstance.generateLayout(dataInstance);

        if (layoutResult.error) {
          console.error('Layout error:', layoutResult.error);
        }

        const graphElement = document.getElementById('graph-container');
        await graphElement.renderLayout(layoutResult.layout);
      } catch (error) {
        console.error('Error rendering graph:', error);
        document.getElementById('error-message').innerHTML =
          '<div><h3>Error</h3><p>' + error.message + '</p></div>';
      }
    }

    window.addEventListener('load', loadGraph);
  <\/script>
</body>
</html>`;
}

const MIN_HEIGHT = 200;
const DEFAULT_HEIGHT = 500;

export default function SpytialWidget(props: SpytialWidgetProps) {
  const containerRef = React.useRef<HTMLDivElement>(null);
  const [error, setError] = React.useState<string | null>(null);
  const [loading, setLoading] = React.useState(true);
  const [height, setHeight] = React.useState(DEFAULT_HEIGHT);

  React.useEffect(() => { injectCss(); }, []);

  const onResizeStart = React.useCallback((e: React.MouseEvent) => {
    e.preventDefault();
    const startY = e.clientY;
    const startH = height;
    const onMove = (ev: MouseEvent) => {
      setHeight(Math.max(MIN_HEIGHT, startH + ev.clientY - startY));
    };
    const onUp = () => {
      document.removeEventListener('mousemove', onMove);
      document.removeEventListener('mouseup', onUp);
    };
    document.addEventListener('mousemove', onMove);
    document.addEventListener('mouseup', onUp);
  }, [height]);

  const openInBrowser = React.useCallback(() => {
    const html = generateHtml(props.dataInstance, props.cndSpec || '');
    const blob = new Blob([html], { type: 'text/html' });
    const url = URL.createObjectURL(blob);
    window.open(url, '_blank');
  }, [props.dataInstance, props.cndSpec]);

  React.useEffect(() => {
    if (!containerRef.current) return;
    setLoading(true);
    setError(null);

    const render = async () => {
      try {
        // Wait briefly for custom element registration from the IIFE bundle
        if (typeof customElements !== 'undefined' && !customElements.get('webcola-cnd-graph')) {
          await new Promise(resolve => setTimeout(resolve, 200));
        }

        const instance = new JSONDataInstance(props.dataInstance);
        const spec = parseLayoutSpec(props.cndSpec || '');
        const evaluator = new SGraphQueryEvaluator();
        const layoutInstance = new LayoutInstance(spec, evaluator);
        const result = layoutInstance.generateLayout(instance);

        const container = containerRef.current;
        if (!container) return;
        container.innerHTML = '';

        const graphEl = document.createElement('webcola-cnd-graph');
        container.appendChild(graphEl);
        await (graphEl as any).renderLayout(result.layout);
        setLoading(false);
      } catch (e: any) {
        console.error('SpytialWidget render error:', e);
        setError(e.message || String(e));
        setLoading(false);
      }
    };

    render();

    return () => {
      if (containerRef.current) containerRef.current.innerHTML = '';
    };
  }, [props.dataInstance, props.cndSpec]);

  return (
    <details open={true}>
      <summary className="mv2 pointer">Spytial Diagram</summary>
      <div className="ml1">
        <div className="spytial-toolbar">
          <button className="spytial-btn" onClick={openInBrowser}>
            Open in Browser
          </button>
        </div>
        {loading && <div className="spytial-loading">Loading diagram...</div>}
        {error && <div className="spytial-error">Error: {error}</div>}
        <div className="spytial-container" style={{ height }}>
          <div ref={containerRef} style={{ width: '100%', height: '100%' }} />
          <div className="spytial-resize-handle" onMouseDown={onResizeStart} />
        </div>
      </div>
    </details>
  );
}
