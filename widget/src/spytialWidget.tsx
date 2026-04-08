import * as React from 'react';
import { useRpcSession } from '@leanprover/infoview';
// @ts-ignore — virtual module created by rollup from the IIFE bundle
import spytialcore from 'spytial-core';

const { JSONDataInstance, LayoutInstance, parseLayoutSpec, SGraphQueryEvaluator } = spytialcore;

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

  React.useEffect(() => {
    if (!containerRef.current) return;
    setLoading(true);
    setError(null);

    const render = async () => {
      try {
        if (typeof customElements !== 'undefined' && !customElements.get('webcola-cnd-graph')) {
          await new Promise(resolve => setTimeout(resolve, 200));
        }

        const instance = new JSONDataInstance(props.dataInstance);
        const spec = parseLayoutSpec(props.cndSpec || '');
        const evaluator = new SGraphQueryEvaluator();
        evaluator.initialize({ sourceData: instance });
        const layoutInstance = new LayoutInstance(spec, evaluator, 0, true);
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
