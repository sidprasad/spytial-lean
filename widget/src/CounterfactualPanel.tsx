import * as React from 'react';
import type { ConflictPoint, CounterfactualPreview, InspectionPoint } from './inspection';

/** Group only identical diagram inputs. Each command keeps its own context, facts and warnings. */
function groupByDiagram(previews: CounterfactualPreview[]) {
  const groups: CounterfactualPreview[][] = [];
  const diagrams = new Map<string, CounterfactualPreview[]>();
  for (const preview of previews) {
    if ('error' in preview) {
      groups.push([preview]);
      continue;
    }
    const { dataInstance, cndSpec, inspection } = preview.view;
    const key = JSON.stringify([dataInstance, cndSpec, inspection?.root]);
    const existing = diagrams.get(key);
    if (existing) existing.push(preview);
    else {
      const group = [preview];
      diagrams.set(key, group);
      groups.push(group);
    }
  }
  return groups;
}

function diagramCaption(group: CounterfactualPreview[]) {
  const preview = group[0];
  if (!('view' in preview)) return;
  const { atoms, relations } = preview.view.dataInstance;
  if (atoms.length === 1 && relations.every(r => r.tuples.length === 0)) {
    return <>Shows <code>{atoms[0].label}</code></>;
  }
  if (group.length > 1) return 'Same diagram';
}

export function CounterfactualPanel({ diagnosis, renderDiagram }: ConflictPoint & {
  renderDiagram: (view: InspectionPoint) => React.ReactNode;
}) {
  const radioName = React.useId();
  const [command, setCommand] = React.useState<string>();
  const groups = React.useMemo(() => groupByDiagram(diagnosis.previews), [diagnosis.previews]);
  const preview = diagnosis.previews.find(p => p.command === command) ??
    diagnosis.previews.find(p => 'view' in p) ?? diagnosis.previews[0];
  return <section className="spytial-counterfactual" aria-label={`Contradictory evidence for ${diagnosis.term}`}>
    <p>Could not draw a diagram because the context exposed contradictory facts.</p>
    {diagnosis.conflicts.map((sources, i) => <div className="spytial-conflict-proof" key={i}>
      {sources.length ? <>
        <span>Lean {i > 0 && 'also '}derived <code>False</code> from</span>
        <pre><code>{sources.join('\n')}</code></pre>
      </> : <p>Lean derived <code>False</code> without a named local hypothesis.</p>}
    </div>)}
    {diagnosis.previews.length > 1 && <fieldset className="spytial-replay-choices">
      <legend>Choose hypotheses to omit</legend>
      {groups.map(group => <div key={group[0].command} className="spytial-replay-group">
        {group.map(p => <label key={p.command}>
          <input type="radio" name={radioName} checked={p === preview}
            aria-label={p.omitted ? `Omit ${p.omitted.join(', ')}` : p.command}
            onChange={() => setCommand(p.command)} />
          <code>{p.omitted?.join(', ') ?? p.command}</code>
        </label>)}
        <small>{diagramCaption(group)}</small>
      </div>)}
    </fieldset>}
    {preview && 'view' in preview ? <>
      <p><strong>This is what you might see if you ran <code className="spytial-replay-command">{preview.command}</code>.</strong></p>
      {preview.truncated && <p>Context preparation reached a limit. This diagram may be incomplete.</p>}
      <React.Fragment key={preview.command}>{renderDiagram(preview.view)}</React.Fragment>
    </> : preview ? <div>
      <p>Could not draw the preview for <code className="spytial-replay-command">{preview.command}</code>.</p>
      <p role="status">{preview.error}</p>
    </div> : <p>No counterfactual preview found.</p>}
    {diagnosis.limited && <p>Counterfactual search reached its limit. Other omissions may be possible.</p>}
  </section>;
}
