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

    /* Error / IIS report */
    .spytial-unsat-banner {
      background: var(--vscode-inputValidation-warningBackground, #352a05);
      border: 1px solid var(--vscode-inputValidation-warningBorder, #9d8515);
      border-radius: 4px;
      padding: 8px 12px;
      margin-bottom: 4px;
      font-size: 12px;
    }
    .spytial-unsat-title {
      font-weight: bold;
      color: var(--vscode-editorWarning-foreground, #cca700);
      margin-bottom: 6px;
    }
    .spytial-unsat-detail {
      color: var(--vscode-foreground);
      font-size: 11px;
      line-height: 1.5;
    }
    .spytial-conflict-table {
      width: 100%;
      border-collapse: collapse;
      font-size: 11px;
      margin-top: 6px;
    }
    .spytial-conflict-table th {
      text-align: left;
      padding: 4px 8px;
      border-bottom: 1px solid var(--vscode-panel-border, #333);
      color: var(--vscode-descriptionForeground);
      font-weight: 600;
    }
    .spytial-conflict-table td {
      padding: 4px 8px;
      border-bottom: 1px solid var(--vscode-panel-border, #222);
      vertical-align: top;
    }
    .spytial-conflict-source {
      color: var(--vscode-editorWarning-foreground, #cca700);
      font-family: var(--vscode-editor-font-family, monospace);
    }
    .spytial-conflict-detail {
      color: var(--vscode-foreground);
    }
    .spytial-selector-errors {
      margin-top: 6px;
      padding: 6px 8px;
      background: var(--vscode-inputValidation-errorBackground, #5a1d1d);
      border: 1px solid var(--vscode-inputValidation-errorBorder, #be1100);
      border-radius: 4px;
      font-size: 11px;
      color: var(--vscode-errorForeground, #f48771);
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

interface LayoutError {
  type: string;
  message: string;
  errorMessages?: {
    conflictingConstraint?: string;
    conflictingSourceConstraint?: string;
    minimalConflictingConstraints?: Map<string, string[]> | Record<string, string[]>;
  };
  overlappingNodes?: any[];
}

interface SelectorError {
  selector: string;
  context: string;
  errorMessage: string;
}

/** Render the IIS conflict table from errorMessages */
function ConflictReport({ error, selectorErrors }: { error: LayoutError; selectorErrors: SelectorError[] }) {
  const msgs = error.errorMessages;

  // Extract conflict entries from the Map or object
  let conflictEntries: Array<[string, string[]]> = [];
  if (msgs?.minimalConflictingConstraints) {
    const mcc = msgs.minimalConflictingConstraints;
    if (mcc instanceof Map) {
      conflictEntries = Array.from(mcc.entries());
    } else if (typeof mcc === 'object') {
      conflictEntries = Object.entries(mcc);
    }
  }

  return (
    <div className="spytial-unsat-banner">
      <div className="spytial-unsat-title">
        {error.type === 'group-overlap'
          ? 'Group Overlap'
          : error.type === 'hidden-node-conflict'
          ? 'Hidden Node Conflict'
          : 'Unsatisfiable Constraints'}
        {' \u2014 showing counterfactual diagram (best-effort)'}
      </div>

      <div className="spytial-unsat-detail">
        {error.message && <div dangerouslySetInnerHTML={{ __html: error.message }} />}

        {conflictEntries.length > 0 && (
          <details open={true} style={{ marginTop: 4 }}>
            <summary style={{ cursor: 'pointer', fontWeight: 600 }}>
              Irreducible Infeasible Subsystem ({conflictEntries.length} constraint{conflictEntries.length > 1 ? 's' : ''})
            </summary>
            <table className="spytial-conflict-table">
              <thead>
                <tr>
                  <th>Source constraint</th>
                  <th>Conflicts with</th>
                </tr>
              </thead>
              <tbody>
                {conflictEntries.map(([source, conflicts], i) => (
                  <tr key={i}>
                    <td className="spytial-conflict-source"
                        dangerouslySetInnerHTML={{ __html: source }} />
                    <td className="spytial-conflict-detail">
                      {conflicts.map((c, j) => (
                        <div key={j} dangerouslySetInnerHTML={{ __html: c }} />
                      ))}
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
          </details>
        )}
      </div>

      {selectorErrors.length > 0 && (
        <div className="spytial-selector-errors">
          <div style={{ fontWeight: 600, marginBottom: 4 }}>Selector errors:</div>
          {selectorErrors.map((se, i) => (
            <div key={i}>
              <code>{se.selector}</code> ({se.context}): {se.errorMessage}
            </div>
          ))}
        </div>
      )}
    </div>
  );
}

const MIN_HEIGHT = 200;
const DEFAULT_HEIGHT = 500;

export default function SpytialWidget(props: SpytialWidgetProps) {
  const containerRef = React.useRef<HTMLDivElement>(null);
  const [error, setError] = React.useState<string | null>(null);
  const [layoutError, setLayoutError] = React.useState<LayoutError | null>(null);
  const [selectorErrors, setSelectorErrors] = React.useState<SelectorError[]>([]);
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
    setLayoutError(null);
    setSelectorErrors([]);

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

        // Capture errors before rendering
        if (result.error) {
          console.warn('Spytial layout error (showing counterfactual):', result.error);
          setLayoutError(result.error);
        }
        if (result.selectorErrors && result.selectorErrors.length > 0) {
          console.warn('Spytial selector errors:', result.selectorErrors);
          setSelectorErrors(result.selectorErrors);
        }

        const container = containerRef.current;
        if (!container) return;
        container.innerHTML = '';

        const graphEl = document.createElement('webcola-cnd-graph');
        container.appendChild(graphEl);

        // Mark unsatisfiable so the web component shows error indicators
        if (result.error) {
          graphEl.setAttribute('unsat', '');
        }

        // Render the counterfactual layout (MFS — best effort)
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
        {(layoutError || selectorErrors.length > 0) && (
          <ConflictReport
            error={layoutError || { type: '', message: '' }}
            selectorErrors={selectorErrors}
          />
        )}
        <div className="spytial-container" style={{ height }}>
          <div ref={containerRef} style={{ width: '100%', height: '100%' }} />
          <div className="spytial-resize-handle" onMouseDown={onResizeStart} />
        </div>
      </div>
    </details>
  );
}
