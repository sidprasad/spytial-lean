import * as React from 'react';
// @ts-ignore — virtual module created by rollup from the IIFE bundle
import spytialcore from 'spytial-core';
// @ts-ignore — virtual module for components bundle (provides mountErrorMessageModal, ErrorAPI)
import spytialComponents from 'spytial-core-components';
import {
  withLeanScalarTypes, pointTitle, correspondingAtoms, continuityOptions,
  type InspectionPoint, type LayoutState,
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
    .spytial-inspection-note { font-size: 12px; margin: 6px 0; }
    .spytial-explorer { margin: 8px 0; }
    .spytial-toolbar { display: flex; gap: 8px; flex-wrap: wrap; align-items: center; }
    .spytial-toolbar strong { overflow-wrap: anywhere; margin-right: auto; }
    .spytial-toolbar button, .spytial-point-header select {
      color: var(--vscode-foreground); background: var(--vscode-editorWidget-background);
      border: 1px solid var(--vscode-panel-border, #777); border-radius: 4px; padding: 4px 8px;
    }
    .spytial-toolbar button[aria-pressed=true] { outline: 1px solid var(--vscode-focusBorder, #007acc); }
    .spytial-toolbar button:disabled { opacity: .4; }
    .spytial-panes { display: grid; grid-template-columns: repeat(auto-fit, minmax(min(100%, 300px), 1fr)); gap: 12px; }
    .spytial-point-header { display: flex; align-items: center; gap: 8px; margin-top: 10px; }
    .spytial-point-header select { max-width: 100%; min-width: 0; }
    .spytial-context { font-size: 12px; margin-top: 8px; }
    .spytial-context code { white-space: pre-wrap; overflow-wrap: anywhere; }
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

interface SpytialWidgetProps extends Partial<InspectionPoint> {
  explorer?: { name: string; points: InspectionPoint[] };
}

const MIN_HEIGHT = 200;
const DEFAULT_HEIGHT = 500;

export default function SpytialWidget(props: SpytialWidgetProps) {
  if (props.explorer) return <InspectionExplorer key={props.explorer.name} {...props.explorer} />;
  if (!props.dataInstance) return <div>No inspection data.</div>;
  return <DiagramWidget {...props as InspectionPoint} />;
}

interface SettledInspection { point: InspectionPoint; state?: LayoutState }

function InspectionExplorer({ name, points }: { name: string; points: InspectionPoint[] }) {
  const [mode, setMode] = React.useState('compare');
  const [left, setLeft] = React.useState(0);
  const [right, setRight] = React.useState(points.length - 1);
  const [step, setStep] = React.useState(0);
  const [anchor, setAnchor] = React.useState<SettledInspection>();
  const [stepPrior, setStepPrior] = React.useState<SettledInspection>();
  const history = React.useRef<SettledInspection>();
  React.useEffect(() => { injectCss(); }, []);
  // A refreshed Lean payload invalidates every settled position and selection.
  React.useEffect(() => {
    setLeft(0); setRight(points.length - 1); setStep(0);
    setAnchor(undefined); setStepPrior(undefined); history.current = undefined;
  }, [points]);
  if (!points.length) return <div>No proof inspections.</div>;
  const multiple = points.length > 1;
  const selected = !multiple ? [0] : mode === 'compare' ? [left, right] :
    mode === 'all' ? points.map((_, i) => i) : [step];
  // Until the reset effect runs, an updated theorem may have fewer points.
  const visible = selected.filter(i => points[i] !== undefined);
  const first = points[visible[0]];
  const anchorReady = anchor?.point === first;
  const choose = (index: number, slot: number) => {
    if (mode === 'step') { setStepPrior(history.current); setStep(index); }
    else if (slot === 0) setLeft(index);
    else setRight(index);
  };
  return <section className="spytial-explorer" aria-label="Theorem inspection explorer">
    <div className="spytial-toolbar">
      <strong>{name}</strong>
      <span>{points.length} inspection {multiple ? 'points' : 'point'}</span>
      {multiple && <div role="group" aria-label="Inspection view mode">
        {([['step', 'Step through'], ['compare', 'Side by side'], ['all', 'All points']]).map(([key, label]) =>
          <button key={key} type="button" aria-pressed={mode === key}
            onClick={() => setMode(key)}>{label}</button>)}
      </div>}
    </div>
    <p className="spytial-inspection-note">Proof inspections in source order. These are proof views;
      different goals and case branches have independent layouts.</p>
    {multiple && mode === 'step' && <div className="spytial-toolbar">
      <button type="button" disabled={step === 0} onClick={() => choose(step - 1, 0)}>Previous</button>
      <span aria-live="polite">{step + 1} / {points.length}</span>
      <button type="button" disabled={step === points.length - 1}
        onClick={() => choose(step + 1, 0)}>Next</button>
    </div>}
    <div className="spytial-panes">
      {visible.map((index, slot) => {
        const point = points[index];
        const prior = mode === 'step' ? stepPrior : slot > 0 && anchorReady ? anchor : undefined;
        const matches = prior && prior.point !== point ? correspondingAtoms(prior.point, point) : [];
        // Followers wait for settled anchor positions, as in Cope and Drag's
        // temporal panes, rather than copying a pre-solve layout.
        const waiting = mode !== 'step' && slot > 0 && !anchorReady;
        return <section key={slot} aria-label={pointTitle(point)}>
          <div className="spytial-point-header">
            {multiple && mode !== 'all' ? <select
              aria-label={mode === 'step' ? 'Inspection point' : slot === 0 ? 'Left inspection point' : 'Right inspection point'}
              value={index} onChange={e => choose(Number(e.target.value), slot)}>
              {points.map((p, i) => <option key={i} value={i}
                disabled={mode === 'compare' && i === (slot === 0 ? right : left)}>
                {i + 1}. {pointTitle(p)} (line {p.point?.line ?? '?'})
              </option>)}
            </select> : <strong>{pointTitle(point)}</strong>}
            <span>Line {point.point?.line ?? '?'}</span>
          </div>
          {point.point?.branch && <p className="spytial-inspection-note">Case {point.point.branch}</p>}
          {!waiting ? <DiagramWidget {...point} prior={prior?.point !== point ? prior : undefined}
            onSettled={slot === 0 ? state => {
              const settled = { point, state };
              history.current = settled;
              setAnchor(previous => previous?.point === point ? previous : settled);
            } : undefined} /> : <div className="spytial-loading">Waiting for comparison layout…</div>}
          {(slot > 0 || mode === 'step' && prior) && !waiting && <p className="spytial-inspection-note" role="status">
            {matches.length && prior?.state ? `Stability hints for ${matches.length} shared Lean identities; layout constraints still apply.` :
              'Independent layout: no reliable correspondence in the same proof goal.'}
          </p>}
        </section>;
      })}
    </div>
  </section>;
}

function DiagramWidget(props: InspectionPoint & {
  prior?: SettledInspection; onSettled?: (state?: LayoutState) => void;
}) {
  const containerRef = React.useRef<HTMLDivElement>(null);
  const graphRef = React.useRef<any>();
  const errorMountRef = React.useRef<HTMLDivElement>(null);
  const [error, setError] = React.useState<string | null>(null);
  const [loading, setLoading] = React.useState(true);
  const [height, setHeight] = React.useState(DEFAULT_HEIGHT);
  const errorMountedRef = React.useRef(false);
  const data = props.dataInstance;
  const onSettledRef = React.useRef(props.onSettled);
  onSettledRef.current = props.onSettled;
  // The prior snapshot is consumed once per selected payload, never on a
  // callback-driven rerender of that same diagram.
  const priorRef = React.useRef(props.prior);
  priorRef.current = props.prior;

  React.useEffect(() => { injectCss(); }, []);

  // Switching between one, two, and all panes resizes retained graphs. Wait
  // for core's own resize handling before fitting the new pane dimensions.
  React.useEffect(() => {
    if (!containerRef.current) return;
    let timer: ReturnType<typeof setTimeout>;
    const observer = new ResizeObserver(() => {
      clearTimeout(timer);
      timer = setTimeout(() => graphRef.current?.resetViewToFitContent?.(), 100);
    });
    observer.observe(containerRef.current);
    return () => { observer.disconnect(); clearTimeout(timer); };
  }, []);

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
        graphRef.current = graphEl;
        container.appendChild(graphEl);

        if (result.error) {
          graphEl.setAttribute('unsat', '');
        }

        graphEl.addEventListener('layout-complete', () => {
          if (!cancelled) {
            // A new shape can exceed the anchor's viewport, even though the
            // positions are valid hints. Frame the pane's own settled graph.
            (graphEl as any).resetViewToFitContent?.();
            onSettledRef.current?.((graphEl as any).getLayoutState());
          }
        }, { once: true });
        const prior = priorRef.current;
        const options = prior?.state && continuityOptions(spytialcore, prior.point, props, prior.state);
        await (graphEl as any).renderLayout(result.layout, options);
        if (!cancelled && result.error) onSettledRef.current?.(undefined);
        if (!cancelled) setLoading(false);
      } catch (e: any) {
        if (cancelled) return;
        console.error('SpytialWidget render error:', e);
        setError(e.message || String(e));
        setLoading(false);
        onSettledRef.current?.(undefined);
      }
    };

    render();

    return () => {
      cancelled = true;
      graphRef.current = undefined;
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
        {!!props.observations?.length && <p className="spytial-inspection-note">
          Observing: <code>{props.observations.join(', ')}</code></p>}
        {!!props.localContext?.length && <details className="spytial-context">
          <summary>Local context ({props.localContext.length})</summary>
          <ul>{props.localContext.map((local, i) => <li key={i}><code>
            {local.name} : {local.type}{local.value != null ? ` := ${local.value}` : ''}
          </code></li>)}</ul>
        </details>}
      </div>
    </details>
  );
}
