import type { DiagramLabelTarget, IEvaluator, LayoutInstance, LayoutSpec } from 'spytial-core';
import type { FactTargets, RelationalData } from './inspection';

interface SourceGraph {
  edge(source: string, target: string, edgeId: string): string | undefined;
  node(id: string): { label?: string } | undefined;
}

export interface FactGraph extends HTMLElement {
  highlightNodes(ids: string[]): boolean;
  hasLabel(target: DiagramLabelTarget): boolean;
  highlightLabels(targets: readonly DiagramLabelTarget[]): () => void;
}

export type FactHighlight = (() => () => void) | undefined;
const tupleKey = (relation: string, atoms: string[]) => JSON.stringify([relation, atoms]);

/** Associate tags with the relation and ordered tuple that supplied their
 * value. Two predicates can tag the same owner with the same endpoint. */
function tagTargets(sourceGraph: SourceGraph, evaluator: IEvaluator,
  tags: LayoutSpec['directives']['tags'], tagRelations: string[][]) {
  const byTuple = new Map<string, DiagramLabelTarget[]>();
  tags.forEach((tag, i) => {
    const relations = tagRelations[i];
    if (!relations?.length) return;
    let owners: Set<string>;
    let tuples: string[][];
    try {
      owners = new Set(evaluator.evaluate(tag.toTag, { instanceIndex: 0 }).selectedAtoms());
      const value = evaluator.evaluate(tag.value, { instanceIndex: 0 });
      tuples = value.maxArity() > 1 ? value.selectedTuplesAll() : value.selectedAtoms().map(id => [id]);
    } catch { return; } // Core already reports selector failures during layout.
    for (const atoms of tuples) {
      const nodeId = atoms[0];
      if (!owners.has(nodeId)) continue;
      const middle = atoms.slice(1, -1).map(id => sourceGraph.node(id)?.label || id);
      const key = middle.length ? `${tag.name}[${middle.join(',')}]` : tag.name;
      const target: DiagramLabelTarget = { kind: 'tag', nodeId, key };
      for (const relation of relations) {
        const k = tupleKey(relation, atoms);
        const targets = byTuple.get(k);
        if (targets) targets.push(target);
        else byTuple.set(k, [target]);
      }
    }
  });
  return byTuple;
}

/** Resolve fact provenance into core's semantic diagram targets once per layout. */
export function renderedFactHighlights(graph: FactGraph, data: RelationalData, facts: FactTargets[],
  sourceGraph: SourceGraph, layout: Pick<LayoutInstance, 'isAttributeField'>, evaluator: IEvaluator,
  tags: LayoutSpec['directives']['tags'], tagRelations: string[][] = []): FactHighlight[] {
  const nodes = new Map<string, Element>();
  type NodeGroup = SVGGElement & { __data__?: { id: string } };
  for (const node of (graph.shadowRoot ?? graph).querySelectorAll<NodeGroup>('g.node, g.error-node')) {
    if (node.__data__) nodes.set(node.__data__.id, node);
  }
  const tagsByTuple = tagTargets(sourceGraph, evaluator, tags, tagRelations);
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
      labels.push(...tagsByTuple.get(tupleKey(relation, atoms)) ?? []);
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
