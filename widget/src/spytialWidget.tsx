import * as React from 'react';
import { useRpcSession } from '@leanprover/infoview';
// @ts-ignore — virtual module created by rollup from the IIFE bundle
import spytialcore from 'spytial-core';
// @ts-ignore — virtual module for components bundle (provides mountErrorMessageModal, ErrorAPI)
import spytialComponents from 'spytial-core-components';
import {
  initialInspectionMode, inspectionData, withLeanScalarTypes,
  type InspectedValue, type InspectionMode, type RelationalData,
} from './inspection';

const { JSONDataInstance, LayoutInstance, parseLayoutSpec, SGraphQueryEvaluator } = spytialcore;
const { isPositionalConstraintError, isGroupOverlapError, isHiddenNodeConflictError } =
  spytialcore.Layout;
const { CnDCore } = spytialComponents;

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
    .spytial-inspection-controls { display: flex; gap: 6px; margin: 8px 0; }
    .spytial-inspection-controls button {
      cursor: pointer; padding: 4px 8px;
      color: var(--vscode-button-secondaryForeground, #222);
      background: var(--vscode-button-secondaryBackground, #eee);
      border: 1px solid var(--vscode-panel-border, #bbb); border-radius: 3px;
    }
    .spytial-inspection-controls button[aria-pressed="true"] {
      color: var(--vscode-button-foreground, white);
      background: var(--vscode-button-background, #245b9e);
    }
    .spytial-inspection-note { font-size: 12px; margin: 6px 0; }
    .spytial-facts { margin: 8px 0; font-size: 12px; }
    .spytial-facts code { white-space: pre-wrap; overflow-wrap: anywhere; }
    .spytial-facts li { margin: 5px 0; }
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

    /* ErrorMessageModal styles (adapted from spytial-core for VS Code infoview) */
    #error-message-modal {
      border: 2px solid var(--vscode-inputValidation-warningBorder, #cca700);
      border-radius: 8px;
      padding: 12px;
      margin-bottom: 8px;
      background: var(--vscode-inputValidation-warningBackground, #352a05);
      overflow-x: auto;
      font-size: 12px;
    }
    #error-message-modal h4 {
      color: var(--vscode-editorWarning-foreground, #cca700);
      margin: 0 0 6px 0;
      font-size: 13px;
    }
    #error-message-modal p {
      margin: 0 0 8px 0;
      color: var(--vscode-foreground);
    }
    #error-message-modal code {
      font-family: var(--vscode-editor-font-family, monospace);
      font-size: 11px;
    }

    /* Constraint relationship table */
    .constraint-relationship-table {
      width: 100%;
      margin-bottom: 8px;
    }
    .constraint-relationship-table table {
      width: 100%;
      border-collapse: collapse;
    }
    .constraint-relationship-table th {
      text-align: left;
      padding: 6px 8px;
      border-bottom: 2px solid var(--vscode-panel-border, #444);
      color: var(--vscode-descriptionForeground);
      font-size: 11px;
      font-weight: 600;
    }
    .constraint-relationship-table td {
      padding: 0;
      vertical-align: top;
      border-bottom: 1px solid var(--vscode-panel-border, #333);
    }
    .constraint-item {
      padding: 6px 8px;
      border-bottom: 1px solid var(--vscode-panel-border, #222);
      transition: background 0.15s;
      cursor: default;
    }
    .constraint-item:last-child {
      border-bottom: none;
    }
    .constraint-item.highlight-source {
      background-color: rgba(255, 193, 7, 0.25);
      border-radius: 3px;
    }
    .constraint-item.highlight-diagram {
      background-color: rgba(255, 193, 7, 0.5);
      border-radius: 3px;
    }

    /* Error card (parse/generic/group errors) */
    .error-card {
      border: 1px solid var(--vscode-panel-border, #444);
      border-radius: 4px;
      overflow: hidden;
    }
    .error-card .card-header {
      padding: 6px 10px;
      background: var(--vscode-editorWidget-background, #252526);
      border-bottom: 1px solid var(--vscode-panel-border, #444);
      font-size: 11px;
    }
    .error-card .card-body {
      padding: 8px 10px;
    }

    /* Selector error list */
    .error-card .list-unstyled {
      list-style: none;
      padding: 0;
      margin: 0;
    }
    .error-card .list-unstyled li {
      padding: 6px 8px;
      margin-bottom: 4px;
      background: var(--vscode-editorWidget-background, #1e1e1e);
      border-radius: 4px;
      font-size: 11px;
    }
    .text-danger {
      color: var(--vscode-errorForeground, #f48771);
    }

    /* Bootstrap utility classes used by ErrorMessageModal */
    .mt-3 { margin-top: 0; }
    .mb-0 { margin-bottom: 0; }
    .mb-2 { margin-bottom: 8px; }
    .p-0 { padding: 0; }
    .p-2 { padding: 8px; }
    .p-3 { padding: 12px; }
    .d-flex { display: flex; }
    .flex-column { flex-direction: column; }
    .h-100 { height: 100%; }
    .bg-light { background: var(--vscode-editorWidget-background, #252526); }
    .rounded { border-radius: 4px; }
    .border { border: 1px solid var(--vscode-panel-border, #444); }
    .border-danger { border-color: var(--vscode-inputValidation-warningBorder, #cca700); }
    .border-2 { border-width: 2px; }
    .table-bordered th, .table-bordered td {
      border: 1px solid var(--vscode-panel-border, #333);
    }
    #hover-instructions {
      font-style: italic;
      font-size: 11px;
      color: var(--vscode-descriptionForeground);
    }
  `;
  document.head.appendChild(style);
}

interface SpytialWidgetProps {
  dataInstance: RelationalData;
  cndSpec?: string;
  inspection?: InspectedValue;
}

const MIN_HEIGHT = 200;
const DEFAULT_HEIGHT = 500;

export default function SpytialWidget(props: SpytialWidgetProps) {
  const containerRef = React.useRef<HTMLDivElement>(null);
  const errorMountRef = React.useRef<HTMLDivElement>(null);
  const [error, setError] = React.useState<string | null>(null);
  const [loading, setLoading] = React.useState(true);
  const [height, setHeight] = React.useState(DEFAULT_HEIGHT);
  const errorMountedRef = React.useRef(false);
  const [mode, setMode] = React.useState<InspectionMode>(() =>
    initialInspectionMode(props.inspection));
  const data = inspectionData(props.dataInstance, props.inspection, mode);

  React.useEffect(() => {
    setMode(initialInspectionMode(props.inspection));
  }, [props.inspection]);

  React.useEffect(() => { injectCss(); }, []);

  // Mount the error modal into the DOM container (same pattern as sterling-ts / spytial-py)
  React.useEffect(() => {
    if (errorMountRef.current && !errorMountedRef.current) {
      const id = 'spytial-lean-error-' + Math.random().toString(36).slice(2, 8);
      errorMountRef.current.id = id;
      if (CnDCore.mountErrorMessageModal) {
        CnDCore.mountErrorMessageModal(id);
        errorMountedRef.current = true;
      }
    }
  }, []);

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
    if (CnDCore.ErrorAPI) CnDCore.ErrorAPI.clearAllErrors();
    let cancelled = false;

    const render = async () => {
      try {
        if (typeof customElements !== 'undefined' && !customElements.get('webcola-cnd-graph')) {
          await new Promise(resolve => setTimeout(resolve, 200));
        }

        if (cancelled) return;
        const instance = new JSONDataInstance(withLeanScalarTypes(data));
        const spec = parseLayoutSpec(props.cndSpec || '');
        const evaluator = new SGraphQueryEvaluator();
        evaluator.initialize({ sourceData: instance });
        const layoutInstance = new LayoutInstance(spec, evaluator, 0, true);
        const result = layoutInstance.generateLayout(instance);

        // Dispatch errors via ErrorAPI (same pattern as sterling-ts / spytial-py)
        if (result.error && CnDCore.ErrorAPI) {
          const err = result.error;
          if (isHiddenNodeConflictError(err)) {
            CnDCore.ErrorAPI.showHiddenNodeConflict(err.errorMessages);
          } else if (isPositionalConstraintError(err) && err.errorMessages) {
            CnDCore.ErrorAPI.showConstraintError(err.errorMessages);
          } else if (isGroupOverlapError(err)) {
            CnDCore.ErrorAPI.showGroupOverlapError(err.message);
          } else {
            CnDCore.ErrorAPI.showGeneralError(err.message || 'Layout error');
          }
        } else if (result.selectorErrors && result.selectorErrors.length > 0 && CnDCore.ErrorAPI) {
          CnDCore.ErrorAPI.showSelectorErrors(result.selectorErrors);
        }

        const container = containerRef.current;
        if (!container || cancelled) return;
        container.innerHTML = '';

        const graphEl = document.createElement('webcola-cnd-graph');
        container.appendChild(graphEl);

        if (result.error) {
          graphEl.setAttribute('unsat', '');
        }

        await (graphEl as any).renderLayout(result.layout);
        if (!cancelled) setLoading(false);
      } catch (e: any) {
        if (cancelled) return;
        console.error('SpytialWidget render error:', e);
        setError(e.message || String(e));
        setLoading(false);
      }
    };

    render();

    return () => {
      cancelled = true;
      if (containerRef.current) containerRef.current.innerHTML = '';
    };
  }, [data, props.cndSpec]);

  return (
    <details open={true}>
      <summary className="mv2 pointer">Spytial Diagram</summary>
      <div className="ml1">
        {props.inspection && <>
          <div className="spytial-inspection-note">
            Inspecting <code>{props.inspection.term}</code>
          </div>
          {props.inspection.hasStructure && props.inspection.facts.length > 0 &&
            <div className="spytial-inspection-controls" aria-label="Inspection view">
              <button type="button" aria-pressed={mode === 'value'}
                onClick={() => setMode('value')}>Selected value</button>
              <button type="button" aria-pressed={mode === 'context'}
                onClick={() => setMode('context')}>Value and context</button>
            </div>}
          {mode === 'context' && props.inspection.hasStructure &&
            <div className="spytial-inspection-note">
              Supporting context may include earlier structures, not just the selected value.
            </div>}
        </>}
        {loading && <div className="spytial-loading">Loading diagram...</div>}
        {error && <div className="spytial-error">Error: {error}</div>}
        <div ref={errorMountRef} />
        <div className="spytial-container" style={{ height }}>
          <div ref={containerRef} style={{ width: '100%', height: '100%' }} />
          <div className="spytial-resize-handle" onMouseDown={onResizeStart} />
        </div>
        {props.inspection && props.inspection.facts.length > 0 &&
          <details className="spytial-facts" open>
            <summary>Context facts ({props.inspection.facts.length})</summary>
            <ul>{props.inspection.facts.map((fact, index) =>
              <li key={index}><code>{fact}</code></li>)}</ul>
          </details>}
      </div>
    </details>
  );
}
