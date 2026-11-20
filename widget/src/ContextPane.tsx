import * as React from 'react';
import { factsInContext, type InspectionPoint } from './inspection';
import type { FactHighlight } from './factHighlights';

export function ContextPane({ point, highlights, onlyHere }: {
  point: InspectionPoint; highlights?: FactHighlight[]; onlyHere?: ReadonlySet<number>;
}) {
  const [hover, setHover] = React.useState<number>();
  const [focus, setFocus] = React.useState<number>();
  const [pin, setPin] = React.useState<number>();
  const active = pin ?? hover ?? focus;
  const facts = point.inspection?.facts ?? [];
  const context = point.localContext ?? [];
  const { locals, other } = React.useMemo(() => factsInContext(point),
    [point.localContext, point.factSources, point.inspection]);

  const clear = () => { setPin(undefined); setFocus(undefined); setHover(undefined); };
  React.useEffect(clear, [point.inspection]);
  React.useLayoutEffect(() => {
    if (active !== undefined) return highlights?.[active]?.();
  }, [highlights, active]);

  function factRow(index: number, content: React.ReactNode) {
    const linked = !!highlights?.[index];
    const unique = onlyHere?.has(index);
    const className = (linked ? 'spytial-context-fact' : 'spytial-context-text') + (unique ? ' spytial-only-here' : '');
    const row = <>{content}{unique && <span className="spytial-sr-only"> (only at this point)</span>}</>;
    return linked ? <button key={index} type="button" className={className}
      data-active={active === index} aria-pressed={pin === index}
      onMouseEnter={() => setHover(index)} onMouseLeave={() => setHover(undefined)}
      onFocus={() => { setHover(undefined); setFocus(index); }} onBlur={() => setFocus(undefined)}
      onClick={() => { if (pin === index) clear(); else setPin(index); }}>
      {row}
    </button> : <div key={index} className={className}
      title={highlights && 'No visible diagram element for this fact'}>{row}</div>;
  }
  function derivedRow(i: number) {
    const sources = point.factSources?.[i] ?? [];
    return factRow(i, <><code>{facts[i]}</code>{sources.length > 1 &&
      <small>from {sources.map(s => context[s]?.name).join(', ')}</small>}</>);
  }

  return <section className="spytial-context-pane" aria-label="Local context"
    onKeyDown={e => { if (e.key === 'Escape') clear(); }}>
    <header><strong>Local context</strong>
      <span>{facts.length} {facts.length === 1 ? 'fact' : 'facts'}</span>
      {onlyHere && facts.length > 0 && <span className={onlyHere.size ? 'spytial-only-here' : undefined}>
        {onlyHere.size ? `${onlyHere.size} only here` : 'All shared'}
      </span>}
      {pin !== undefined ? <button type="button" onClick={clear}>Clear pin</button> :
        highlights?.some(Boolean) && <small>Hover to highlight · Click to pin</small>}
    </header>
    <div className="spytial-context-scroll" tabIndex={0} role="region" aria-label="Context declarations and facts">
      {context.map((local, i) => {
        const { direct, derived } = locals[i];
        const uniqueDerived = onlyHere ? derived.filter(index => onlyHere.has(index)).length : 0;
        const decl = <><code><b>{local.name}</b> : {local.type}{local.value != null && ` := ${local.value}`}</code>
          {local.excluded && <small> (omitted from this inspection)</small>}</>;
        return <div key={i} className="spytial-context-decl">
          {direct !== undefined ? factRow(direct, decl) : !derived.length &&
            <div className="spytial-context-text">{decl}</div>}
          {derived.length > 0 && <details open={uniqueDerived > 0} onToggle={e => {
            if (!e.currentTarget.open && active !== undefined && derived.includes(active)) clear();
          }}>
            <summary>{direct === undefined && decl}
              <small>{derived.length} derived {derived.length === 1 ? 'fact' : 'facts'}
                {uniqueDerived > 0 && ` · ${uniqueDerived} only here`}</small>
            </summary>
            <div className="spytial-derived">{derived.map(derivedRow)}</div>
          </details>}
        </div>;
      })}
      {other.length > 0 && <div className="spytial-context-decl"><strong>Other retained facts</strong>
        {other.map(derivedRow)}</div>}
    </div>
  </section>;
}
