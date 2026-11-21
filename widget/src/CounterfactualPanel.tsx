import * as React from 'react';
import { DiagramWidget } from './DiagramWidget';
import type { ConflictPoint, CounterfactualPreview } from './inspection';

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
    return `Shows ${atoms[0].label}`;
  }
  if (group.length > 1) return 'Same diagram';
}

export function CounterfactualPanel({ diagnosis }: ConflictPoint) {
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
    {diagnosis.previews.length > 1 && <>
      <p><strong>What would the diagram of <code>{diagnosis.term}</code> show if we set aside some hypotheses?</strong></p>
      <label className="spytial-replay-choices">
        Hypotheses to omit
        <select value={preview.command} onChange={event => setCommand(event.target.value)}>
          {groups.map(group => {
            const options = group.map(p =>
              <option key={p.command} value={p.command}>{p.omitted?.join(', ') || p.command}</option>);
            const caption = diagramCaption(group);
            return caption ? <optgroup key={group[0].command} label={caption}>{options}</optgroup> : options;
          })}
        </select>
      </label>
    </>}
    {preview && 'view' in preview ? <>
      {diagnosis.previews.length === 1 && <p><strong>
        {preview.omitted?.length
          ? <>Here’s what the diagram of <code>{diagnosis.term}</code> shows with <code>{preview.omitted.join(', ')}</code> set aside.</>
          : <>Here’s the counterfactual diagram of <code>{diagnosis.term}</code>.</>}
      </strong></p>}
      <p>Showing <code className="spytial-replay-command">{preview.command}</code></p>
      {preview.truncated && <p>Context preparation reached a limit. This diagram may be incomplete.</p>}
      <DiagramWidget key={preview.command} point={preview.view} />
    </> : preview ? <div>
      <p>Could not draw the preview for <code className="spytial-replay-command">{preview.command}</code>.</p>
      <p role="status">{preview.error}</p>
    </div> : <p>No counterfactual preview found.</p>}
    {diagnosis.limited && <p>Counterfactual search reached its limit. Other omissions may be possible.</p>}
  </section>;
}
