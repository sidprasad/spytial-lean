import * as React from 'react';
// @ts-ignore — virtual module created by rollup from the IIFE bundle
import spytialcore from 'spytial-core';
// @ts-ignore — virtual module for components bundle (provides mountErrorMessageModal, ErrorAPI)
import spytialComponents from 'spytial-core-components';
import {
  withLeanScalarTypes, pointTitle, inspectionDisplayData, correspondingAtoms, continuityOptions,
  compareFacts,
  type InspectionPoint, type InspectionEntry, type ConflictPoint, type LayoutState,
} from './inspection';
import { ContextPane } from './ContextPane';
import { CounterfactualPanel } from './CounterfactualPanel';
import { renderedFactHighlights, type FactGraph, type FactHighlight } from './factHighlights';

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
    .spytial-counterfactual { min-width: 0; }
    .spytial-counterfactual p { margin: .6em 0; }
    .spytial-conflict-proof pre {
      margin: .3em 0 .7em; padding: .5em .8em; white-space: pre-wrap; overflow-wrap: anywhere;
      border-inline-start: 2px solid var(--vscode-editorWarning-foreground, #b48b26);
      background: var(--vscode-textCodeBlock-background, #8881);
    }
    .spytial-replay-choices { margin: .8em 0; padding: 0; border: 0; min-width: 0; }
    .spytial-replay-choices legend { padding: 0; font-weight: 600; }
    .spytial-replay-group { display: flex; flex-wrap: wrap; align-items: baseline; gap: .4em .8em; margin-top: .4em; }
    .spytial-replay-group label { display: inline-flex; align-items: baseline; gap: .35em; cursor: pointer; }
    .spytial-replay-group input { margin: 0; accent-color: var(--vscode-focusBorder, #087aba); }
    .spytial-replay-group small { color: var(--vscode-descriptionForeground); }
    .spytial-replay-group code, .spytial-replay-command { white-space: pre-wrap; overflow-wrap: anywhere; }
    .spytial-explorer { margin: 8px 0; }
    .spytial-explorer-summary { cursor: pointer; margin: 6px 0; }
    .spytial-toolbar { display: flex; gap: 8px; flex-wrap: wrap; align-items: center; }
    .spytial-toolbar strong { overflow-wrap: anywhere; margin-right: auto; }
    .spytial-toolbar button, .spytial-point-select {
      color: var(--vscode-foreground); background: var(--vscode-editorWidget-background);
      border: 1px solid var(--vscode-panel-border, #777); border-radius: 4px; padding: 4px 8px;
    }
    .spytial-toolbar button[aria-pressed=true] { outline: 1px solid var(--vscode-focusBorder, #007acc); }
    .spytial-toolbar button:disabled { opacity: .4; }
    .spytial-panes { display: grid; grid-template-columns: repeat(auto-fit, minmax(min(100%, 300px), 1fr)); gap: 12px; }
    .spytial-point-header { display: flex; align-items: center; gap: 8px; margin-top: 10px; }
    .spytial-point-select { max-width: 100%; min-width: 0; }
    .spytial-pair-selectors { display: flex; flex-wrap: wrap; gap: 6px 12px; margin: 8px 0; }
    .spytial-pair-selectors label { flex: 1 1 12em; min-width: 0; display: grid; gap: 2px; }
    .spytial-split { height: min(72vh, 680px); display: grid; min-width: 0; }
    .spytial-divider {
      position: relative; cursor: row-resize; touch-action: none; outline-offset: -2px;
    }
    .spytial-divider::after {
      content: ''; display: block; width: 36px; height: 3px; border-radius: 2px;
      margin: 4px auto; background: var(--vscode-descriptionForeground, #888);
    }
    .spytial-divider:hover::after, .spytial-divider:focus-visible::after {
      background: var(--vscode-focusBorder, #087aba);
    }
    .spytial-context-pane { min-height: 0; min-width: 0; display: flex; flex-direction: column; font-size: 12px; }
    .spytial-context-pane header {
      display: flex; flex-wrap: wrap; align-items: center; gap: 3px 8px; padding: 3px 6px;
      border-bottom: 1px solid var(--vscode-panel-border, #8886);
    }
    .spytial-context-pane header span, .spytial-context-pane small { color: var(--vscode-descriptionForeground); }
    .spytial-context-pane header small, .spytial-context-pane header button { margin-inline-start: auto; }
    .spytial-context-scroll { min-height: 0; overflow: auto; overscroll-behavior: contain; scrollbar-gutter: stable; }
    .spytial-context-pane code { white-space: pre-wrap; overflow-wrap: anywhere; }
    .spytial-context-decl { padding: 2px 0; border-bottom: 1px solid var(--vscode-panel-border, #8883); }
    .spytial-context-text, .spytial-context-fact, .spytial-context-decl summary { padding: 3px 6px; }
    .spytial-context-decl summary { cursor: pointer; }
    .spytial-context-decl summary small, .spytial-context-fact small { margin-inline-start: .5em; }
    .spytial-derived { margin: 2px 0 2px 1em; border-inline-start: 1px solid var(--vscode-panel-border, #888); }
    .spytial-context-fact {
      display: block; width: 100%; text-align: start; font: inherit; color: inherit; cursor: pointer;
      border: 0; border-inline-start: 2px solid transparent; background: transparent;
    }
    .spytial-context-fact[data-active=true] { background: var(--vscode-list-hoverBackground, #8882);
      border-inline-start-color: var(--vscode-focusBorder, #087aba); }
    .spytial-context-pane :focus-visible, .spytial-divider:focus-visible {
      outline: 1px solid var(--vscode-focusBorder, #087aba); outline-offset: -1px;
    }
    [data-spytial-compare-side=left] {
      --spytial-difference: var(--vscode-editorGutter-deletedBackground, #c74e39);
      --spytial-difference-line: var(--vscode-diffEditor-removedLineBackground);
      --spytial-difference-active: var(--vscode-diffEditor-removedTextBackground);
    }
    [data-spytial-compare-side=right] {
      --spytial-difference: var(--vscode-editorGutter-addedBackground, #43854a);
      --spytial-difference-line: var(--vscode-diffEditor-insertedLineBackground);
      --spytial-difference-active: var(--vscode-diffEditor-insertedTextBackground);
    }
    .spytial-only-here {
      border-inline-start: 3px solid var(--spytial-difference);
      background-color: var(--spytial-difference-line, color-mix(in srgb, var(--spytial-difference) 14%, transparent));
    }
    .spytial-context-fact.spytial-only-here[data-active=true] {
      border-inline-start-color: var(--spytial-difference);
      background-color: var(--spytial-difference-active, color-mix(in srgb, var(--spytial-difference) 27%, transparent));
    }
    .spytial-context-pane header .spytial-only-here { padding-inline: 4px; color: inherit; }
    .spytial-sr-only { position: absolute; width: 1px; height: 1px; overflow: hidden; clip-path: inset(50%); }
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
  diagnosis?: ConflictPoint['diagnosis'];
  explorer?: { name: string; points: InspectionEntry[] };
}

const MIN_HEIGHT = 200;
const DEFAULT_HEIGHT = 500;

export default function SpytialWidget(props: SpytialWidgetProps) {
  React.useEffect(injectCss, []);
  if (props.explorer) return <InspectionExplorer key={props.explorer.name} {...props.explorer} />;
  if (props.diagnosis) return <CounterfactualPanel diagnosis={props.diagnosis} renderDiagram={renderPreviewDiagram} />;
  if (!props.dataInstance) return <div>No inspection data.</div>;
  return <DiagramWidget {...props as InspectionPoint} />;
}

function renderPreviewDiagram(view: InspectionPoint) {
  return <DiagramWidget {...view} />;
}

interface SettledInspection { point: InspectionPoint; state?: LayoutState }

function InspectionExplorer({ name, points }: { name: string; points: InspectionEntry[] }) {
  const [expanded, setExpanded] = React.useState(false);
  const [mode, setMode] = React.useState('compare');
  const [left, setLeft] = React.useState(0);
  const [right, setRight] = React.useState(points.length - 1);
  const [step, setStep] = React.useState(0);
  const [anchor, setAnchor] = React.useState<SettledInspection>();
  const [stepPrior, setStepPrior] = React.useState<SettledInspection>();
  const history = React.useRef<SettledInspection>();
  // A refreshed Lean payload invalidates every settled position and selection.
  React.useEffect(() => {
    setLeft(0); setRight(points.length - 1); setStep(0);
    setAnchor(undefined); setStepPrior(undefined); history.current = undefined;
  }, [points]);
  const onlyHere = React.useMemo(() => {
    const a = points[left], b = points[right];
    if (expanded && mode === 'compare' && points.length > 1 && a && b &&
        !('diagnosis' in a) && !('diagnosis' in b)) return compareFacts(a, b);
  }, [expanded, mode, points, left, right]);
  if (!points.length) return <div>No proof inspections.</div>;
  const multiple = points.length > 1;
  const selected = !multiple ? [0] : mode === 'compare' ? [left, right] :
    mode === 'all' ? points.map((_, i) => i) : [step];
  // Until the reset effect runs, an updated theorem may have fewer points.
  const visible = selected.filter(i => points[i] !== undefined);
  const first = points[visible[0]];
  const anchorReady = anchor?.point === first;
  const comparing = multiple && mode === 'compare' && visible.length === 2;
  const choose = (index: number, slot: number) => {
    if (mode === 'step') { setStepPrior(history.current); setStep(index); }
    else if (slot === 0) setLeft(index);
    else setRight(index);
  };
  const shiftPair = (delta: number) => {
    setLeft(left + delta);
    setRight(right + delta);
  };
  const pointSelect = (index: number, slot: number, label: string) =>
    <select className="spytial-point-select" aria-label={label} value={index}
      onChange={e => choose(Number(e.target.value), slot)}>
      {points.map((p, i) => <option key={i} value={i}>
        {i + 1}. {pointTitle(p)} (line {p.point?.line ?? '?'})
      </option>)}
    </select>;
  return <details className="spytial-theorem-inspections" open={expanded} onToggle={event => {
    const open = event.currentTarget.open;
    setExpanded(open);
    if (!open) {
      setAnchor(undefined); setStepPrior(undefined); history.current = undefined;
    }
  }}>
    <summary className="spytial-explorer-summary">Spytial inspections ({points.length})</summary>
    {expanded && <section className="spytial-explorer" aria-label="Spytial inspection explorer">
    <div className="spytial-toolbar">
      <strong>{name}</strong>
      <span>{points.length} inspection {multiple ? 'points' : 'point'}</span>
      {multiple && <div role="group" aria-label="Inspection view mode">
        {([['step', 'Step through'], ['compare', 'Side by side'], ['all', 'All points']]).map(([key, label]) =>
          <button key={key} type="button" aria-pressed={mode === key}
            onClick={() => setMode(key)}>{label}</button>)}
      </div>}
    </div>
    {comparing && <>
      <div className="spytial-pair-selectors">
        <label>Left point{pointSelect(left, 0, 'Left inspection point')}</label>
        <label>Right point{pointSelect(right, 1, 'Right inspection point')}</label>
      </div>
      {points.length > 2 && <div className="spytial-toolbar" role="group" aria-label="Move both inspection points">
        <button type="button" disabled={Math.min(left, right) === 0}
          onClick={() => shiftPair(-1)}>Previous pair</button>
        <button type="button" disabled={Math.max(left, right) === points.length - 1}
          onClick={() => shiftPair(1)}>Next pair</button>
      </div>}
    </>}
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
        const diagram = !('diagnosis' in point);
        const matches = diagram && prior && prior.point !== point ? correspondingAtoms(prior.point, point) : [];
        // Followers wait for settled anchor positions, as in Cope and Drag's
        // temporal panes, rather than copying a pre-solve layout.
        const waiting = diagram && mode !== 'step' && slot > 0 && first && !('diagnosis' in first) && !anchorReady;
        return <section key={slot} aria-label={pointTitle(point)}
          data-spytial-compare-side={comparing ? (slot === 0 ? 'left' : 'right') : undefined}>
          <div className="spytial-point-header">
            {multiple && mode === 'step' ? pointSelect(index, slot, 'Inspection point') :
              <strong>{multiple && `${index + 1}. `}<span>{pointTitle(point)}</span></strong>}
            <span>Line {point.point?.line ?? '?'}</span>
          </div>
          {point.point?.branch && <p className="spytial-inspection-note">Case {point.point.branch}</p>}
          {!diagram ? <CounterfactualPanel diagnosis={point.diagnosis} renderDiagram={renderPreviewDiagram} /> : !waiting ? <DiagramWidget {...point} pointNumber={multiple ? index + 1 : undefined}
            onlyHere={onlyHere?.[slot]}
            prior={prior?.point !== point ? prior : undefined}
            onSettled={slot === 0 ? state => {
              const settled = { point, state };
              history.current = settled;
              setAnchor(previous => previous?.point === point ? previous : settled);
            } : undefined} /> : <div className="spytial-loading">Waiting for comparison layout…</div>}
          {diagram && (slot > 0 || mode === 'step' && prior) && prior?.point !== point && !waiting && <p className="spytial-inspection-note" role="status">
            {matches.length && prior?.state ? `Stability hints for ${matches.length} shared Lean identities; layout constraints still apply.` :
              'Independent layout: no shared bindings established for these points.'}
          </p>}
        </section>;
      })}
    </div>
    </section>}
  </details>;
}

function DiagramWidget(props: InspectionPoint & {
  onlyHere?: ReadonlySet<number>;
  pointNumber?: number; prior?: SettledInspection; onSettled?: (state?: LayoutState) => void;
}) {
  const containerRef = React.useRef<HTMLDivElement>(null);
  const graphRef = React.useRef<any>();
  const errorMountRef = React.useRef<HTMLDivElement>(null);
  const [error, setError] = React.useState<string | null>(null);
  const [loading, setLoading] = React.useState(true);
  const [height, setHeight] = React.useState(DEFAULT_HEIGHT);
  const [share, setShare] = React.useState(62);
  const [factHighlights, setFactHighlights] = React.useState<FactHighlight[]>();
  const split = !!(props.onlyHere || props.localContext?.length || props.inspection?.facts.length);
  const errorMountedRef = React.useRef(false);
  const data = props.dataInstance;
  const onSettledRef = React.useRef(props.onSettled);
  onSettledRef.current = props.onSettled;
  // The prior snapshot is consumed once per selected payload, never on a
  // callback-driven rerender of that same diagram.
  const priorRef = React.useRef(props.prior);
  priorRef.current = props.prior;


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
    setFactHighlights(undefined);
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
        const displayData = inspectionDisplayData(data, props.inspection, props.pointNumber);
        const displayInstance = displayData === data ? instance :
          new JSONDataInstance(withLeanScalarTypes(displayData));
        const result = layoutInstance.generateLayout(displayInstance);

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

        const graphEl = document.createElement('webcola-cnd-graph') as FactGraph;
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
            const targets = props.inspection?.factTargets;
            if (targets?.length) setFactHighlights(renderedFactHighlights(graphEl, displayData, targets,
              displayInstance.generateGraph(false, false), layoutInstance));
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
  }, [data, props.cndSpec, props.inspection, props.pointNumber]);

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
        <div className={split ? 'spytial-split' : undefined} style={split ? {
          gridTemplateRows: `minmax(0, ${share}fr) 12px minmax(0, ${100 - share}fr)`,
        } : undefined}>
          <div className="spytial-container" style={split ? undefined : { height }}>
            <div ref={containerRef} style={{ width: '100%', height: '100%' }} />
            {!split && <div className="spytial-resize-handle" onMouseDown={onResizeStart} />}
          </div>
          {split && <>
            <div className="spytial-divider" role="separator" tabIndex={0} aria-orientation="horizontal"
              aria-label="Diagram height" aria-valuemin={25} aria-valuemax={80} aria-valuenow={share}
              aria-valuetext={`${share}%`}
              onPointerDown={e => { if (e.button === 0) e.currentTarget.setPointerCapture(e.pointerId); }}
              onPointerMove={e => {
                if (!e.currentTarget.hasPointerCapture(e.pointerId)) return;
                const bounds = e.currentTarget.parentElement!.getBoundingClientRect();
                setShare(Math.max(25, Math.min(80, Math.round(100 * (e.clientY - bounds.top) / bounds.height))));
              }}
              onKeyDown={e => {
                const next = { ArrowUp: share - 5, ArrowDown: share + 5, Home: 25, End: 80 }[e.key];
                if (next === undefined) return;
                e.preventDefault(); setShare(Math.max(25, Math.min(80, next)));
              }} />
            <ContextPane key={props.pointNumber ?? props.point?.line} point={props}
              highlights={factHighlights} onlyHere={props.onlyHere} />
          </>}
        </div>
        {!!props.observations?.length && <p className="spytial-inspection-note">
          Observing: <code>{props.observations.join(', ')}</code></p>}
      </div>
    </details>
  );
}
