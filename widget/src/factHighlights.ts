import type { DiagramLabelTarget, LayoutInstance, Translators } from 'spytial-core';
import type { FactTargets, RelationalData } from './inspection';

interface SourceGraph {
  edge(source: string, target: string, edgeId: string): string | undefined;
}

export type FactHighlight = (() => () => void) | undefined;
const tupleKey = (relation: string, atoms: string[]) => JSON.stringify([relation, atoms]);

/** Highlight only direct correspondences. Atoms identify nodes and tuples identify
 * edge captions or attribute lines. Tags are computed by selectors. */
export function renderedFactHighlights(graph: Translators.WebColaCnDGraph,
  data: RelationalData, facts: FactTargets[],
  sourceGraph: SourceGraph, layout: Pick<LayoutInstance, 'isAttributeField'>): FactHighlight[] {
  const nodes = new Map<string, Element>();
  type NodeGroup = SVGGElement & { __data__?: { id: string } };
  for (const node of (graph.shadowRoot ?? graph).querySelectorAll<NodeGroup>('g.node, g.error-node')) {
    if (node.__data__) nodes.set(node.__data__.id, node);
  }
  const relations = new Map(data.relations.map(r => [r.id, r]));
  // JSONDataInstance renders the first copy of each (relation name, ordered tuple).
  const edges = new Map<string, string>();
  for (const r of data.relations) r.tuples.forEach((tuple, i) => {
    const k = tupleKey(r.name, tuple.atoms);
    if (!edges.has(k)) edges.set(k, `${r.id}_${i}`);
  });

  return facts.map(fact => {
    const ids = fact.atoms.filter(id => nodes.has(id));
    const labels: DiagramLabelTarget[] = [];
    for (const { relation, atoms } of fact.tuples) {
      const r = relations.get(relation);
      if (!r || !atoms.length) continue;
      const edgeId = edges.get(tupleKey(r.name, atoms));
      if (edgeId === undefined) continue;
      const from = atoms[0], to = atoms[atoms.length - 1];
      if (layout.isAttributeField(r.name, from, to)) {
        const key = sourceGraph.edge(from, to, edgeId);
        if (key !== undefined) labels.push({ kind: 'attribute', nodeId: from, key });
      } else {
        labels.push({ kind: 'edge', edgeId });
      }
    }
    const visible = labels.filter(label => graph.hasLabel(label));
    if (!ids.length && !visible.length) return;
    return () => {
      const addedNodes = ids.map(id => nodes.get(id)!).filter(node => !node.classList.contains('highlighted'));
      if (ids.length) graph.highlightNodes(ids);
      const release = graph.highlightLabels(visible);
      return () => {
        release();
        // Core's clearNodeHighlights also clears the constraint inspector's nodes and badges.
        addedNodes.forEach(node => node.classList.remove('highlighted'));
      };
    };
  });
}
