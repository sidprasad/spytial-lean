import * as React from 'react';
import type { LayoutErrorDetail, LayoutState, SystemError, Translators } from 'spytial-core';
import { ErrorMessageModal } from 'spytial-core/react';
import { ContextPane } from './ContextPane';
import { prepareDiagram } from './diagramLayout';
import { continuityOptions, type InspectionPoint } from './inspection';
import type { FactHighlight } from './factHighlights';

export interface SettledInspection {
  point: InspectionPoint;
  state?: LayoutState;
}

interface DiagramProps {
  point: InspectionPoint;
  onlyHere?: ReadonlySet<number>;
  pointNumber?: number;
  prior?: SettledInspection;
  waitingForAnchor?: boolean;
  onSettled?: (point: InspectionPoint, state?: LayoutState) => void;
}

export function DiagramWidget({ point, onlyHere, pointNumber, prior, waitingForAnchor, onSettled }: DiagramProps) {
  const graphId = React.useId();
  const containerRef = React.useRef<HTMLDivElement>(null);
  const graphRef = React.useRef<Translators.WebColaCnDGraph>();
  const dragStart = React.useRef<{ y: number; height: number }>();
  const [error, setError] = React.useState<string>();
  const [layoutError, setLayoutError] = React.useState<SystemError>();
  const [loading, setLoading] = React.useState(true);
  const [height, setHeight] = React.useState(500);
  const [share, setShare] = React.useState(62);
  const [factHighlights, setFactHighlights] = React.useState<FactHighlight[]>();
  const [pinnedFact, setPinnedFact] = React.useState<number>();
  const split = !!(onlyHere || point.localContext?.length || point.inspection?.facts.length);

  // Core resizes its viewport first, then we fit the settled graph to the new pane.
  React.useEffect(() => {
    const container = containerRef.current;
    if (!container) return;
    let timer: ReturnType<typeof setTimeout>;
    const observer = new ResizeObserver(() => {
      clearTimeout(timer);
      timer = setTimeout(() => graphRef.current?.resetViewToFitContent(), 100);
    });
    observer.observe(container);
    return () => { observer.disconnect(); clearTimeout(timer); };
  }, []);

  React.useEffect(() => {
    const container = containerRef.current;
    if (!container || waitingForAnchor) return;
    const controller = new AbortController();
    const { signal } = controller;
    setLoading(true);
    setError(undefined);
    setFactHighlights(undefined);

    async function render(container: HTMLDivElement) {
      try {
        await customElements.whenDefined('webcola-cnd-graph');
        if (signal.aborted) return;

        const diagram = prepareDiagram(point, pointNumber);
        setLayoutError(diagram.diagnostic);
        const graph = document.createElement('webcola-cnd-graph') as Translators.WebColaCnDGraph;
        graph.id = graphId;
        graph.toggleAttribute('unsat', diagram.hasConflict);
        graphRef.current = graph;
        container.appendChild(graph);
        graph.addEventListener('layout-complete', () => {
          graph.resetViewToFitContent();
          onSettled?.(point, graph.getLayoutState());
          setFactHighlights(diagram.factHighlights(graph));
        }, { once: true, signal });
        // Core reports fatal renderer errors as events. Release panes waiting for this layout.
        graph.addEventListener('layout-error', event => {
          if ((event as CustomEvent<LayoutErrorDetail>).detail.fatal) onSettled?.(point);
        }, { signal });
        const options = prior?.state && continuityOptions(prior.point, point, prior.state);
        await graph.renderLayout(diagram.layout, options);
      } catch (error) {
        if (signal.aborted) return;
        console.error('SpytialWidget render error:', error);
        setLayoutError(undefined);
        setError(error instanceof Error ? error.message : String(error));
        onSettled?.(point);
      } finally {
        if (!signal.aborted) setLoading(false);
      }
    }
    void render(container);
    return () => {
      controller.abort();
      graphRef.current?.remove();
      graphRef.current = undefined;
    };
  }, [point, pointNumber, prior, waitingForAnchor, onSettled, graphId]);

  return (
    <details open={true}>
      <summary className="mv2 pointer">Spytial Diagram</summary>
      <div className="ml1">
        {point.inspection && <div className="spytial-inspection-note">
          Inspecting <code>{point.inspection.term}</code>
        </div>}
        {(loading || waitingForAnchor) && <div className="spytial-loading">
          {waitingForAnchor ? 'Waiting for comparison layout…' : 'Loading diagram...'}
        </div>}
        {error && <div className="spytial-error">Error: {error}</div>}
        {layoutError && <div className="spytial-layout-error">
          {/* Core clears graph highlights when a constraint hover ends. A pin owns that highlight. */}
          <ErrorMessageModal systemError={layoutError} graphElementId={pinnedFact === undefined ? graphId : undefined} />
        </div>}
        <div className={split ? 'spytial-split' : undefined} style={split ? {
          gridTemplateRows: `minmax(0, ${share}fr) 12px minmax(0, ${100 - share}fr)`,
        } : undefined}>
          <div className="spytial-container" style={split ? undefined : { height }}>
            <div ref={containerRef} style={{ width: '100%', height: '100%' }} />
            {!split && <div className="spytial-resize-handle" onPointerDown={e => {
              if (e.button !== 0) return;
              dragStart.current = { y: e.clientY, height };
              e.currentTarget.setPointerCapture(e.pointerId);
            }}
              onPointerMove={e => {
                if (e.currentTarget.hasPointerCapture(e.pointerId) && dragStart.current)
                  setHeight(Math.max(200, dragStart.current.height + e.clientY - dragStart.current.y));
              }}
              onLostPointerCapture={() => { dragStart.current = undefined; }} />}
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
            <ContextPane key={pointNumber ?? point.point?.line} point={point}
              highlights={factHighlights} onlyHere={onlyHere} pin={pinnedFact} setPin={setPinnedFact} />
          </>}
        </div>
        {!!point.observations?.length && <p className="spytial-inspection-note">
          Observing: <code>{point.observations.join(', ')}</code></p>}
      </div>
    </details>
  );
}
