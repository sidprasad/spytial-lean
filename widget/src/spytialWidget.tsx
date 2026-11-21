import * as React from 'react';
import type { LayoutState } from 'spytial-core';
import { compareFacts, correspondingAtoms, pointTitle, type InspectionEntry, type InspectionPoint } from './inspection';
import { DiagramWidget, type SettledInspection } from './DiagramWidget';
import { CounterfactualPanel } from './CounterfactualPanel';
import { injectWidgetStyles } from './widgetStyles';

interface ExplorerProps {
  name: string;
  points: InspectionEntry[];
}

export default function SpytialWidget(props: InspectionEntry | { explorer: ExplorerProps }) {
  React.useEffect(injectWidgetStyles, []);
  if ('explorer' in props && props.explorer)
    return <InspectionExplorer key={props.explorer.name} {...props.explorer} />;
  if ('diagnosis' in props && props.diagnosis) return <CounterfactualPanel diagnosis={props.diagnosis} />;
  if ('dataInstance' in props && props.dataInstance) return <DiagramWidget point={props} />;
  return <div>No inspection data.</div>;
}

function InspectionExplorer({ name, points }: ExplorerProps) {
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
  const onAnchorSettled = React.useCallback((point: InspectionPoint, state?: LayoutState) => {
    const settled = { point, state };
    history.current = settled;
    setAnchor(previous => previous?.point === point ? previous : settled);
  }, []);
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
          {!diagram ? <CounterfactualPanel diagnosis={point.diagnosis} /> :
            <DiagramWidget key={index} point={point} pointNumber={multiple ? index + 1 : undefined}
              waitingForAnchor={waiting} onlyHere={onlyHere?.[slot]} prior={prior?.point !== point ? prior : undefined}
              onSettled={slot === 0 ? onAnchorSettled : undefined} />}
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
