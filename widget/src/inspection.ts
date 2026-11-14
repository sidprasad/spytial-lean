export interface RelationalData {
  atoms: Array<{ id: string; type: string; label: string }>;
  relations: Array<{
    id: string;
    name: string;
    types: string[];
    tuples: Array<{ atoms: string[]; types: string[] }>;
  }>;
}

export interface InspectedValue {
  root: string;
  term: string;
  facts: string[];
}

export interface InspectionPoint {
  dataInstance: RelationalData;
  cndSpec?: string;
  inspection?: InspectedValue;
  identities?: Array<{ atom: string; identity: string }>;
  localContext?: Array<{ name: string; type: string; value?: string | null }>;
  observations?: string[];
  point?: { title?: string | null; line?: number; scope: string; branch: string };
}

export interface LayoutState {
  positions: Array<{ id: string; x: number; y: number }>;
  transform: { k: number; x: number; y: number };
}

export function pointTitle(point: InspectionPoint): string {
  return point.point?.title ?? point.inspection?.term ?? 'Inspection';
}

/** Bijection supported by exact Lean identities in the same goal. Never infer
 * identity from labels, source order, or traversal-local atom IDs. */
export function correspondingAtoms(previous: InspectionPoint, current: InspectionPoint) {
  if (!previous.point?.scope || previous.point.scope !== current.point?.scope) return [];
  const candidates = new Map<string, Set<string>>();
  const previousTypes = new Map(previous.dataInstance.atoms.map(a => [a.id, a.type]));
  const currentTypes = new Map(current.dataInstance.atoms.map(a => [a.id, a.type]));
  for (const a of previous.identities ?? []) {
    for (const b of current.identities ?? []) {
      if (a.identity !== b.identity || !previousTypes.has(a.atom) ||
          previousTypes.get(a.atom) !== currentTypes.get(b.atom)) continue;
      const options = candidates.get(a.atom) ?? new Set<string>();
      options.add(b.atom);
      candidates.set(a.atom, options);
    }
  }
  const reverse = new Map<string, Set<string>>();
  for (const [a, bs] of candidates) for (const b of bs) {
    const options = reverse.get(b) ?? new Set<string>();
    options.add(a);
    reverse.set(b, options);
  }
  return [...candidates].flatMap(([a, bs]) => {
    const b = [...bs][0];
    return bs.size === 1 && reverse.get(b)?.size === 1 ? [{ previous: a, current: b }] : [];
  });
}

/** Reuse core's policy gateway, passing only remapped, evidenced position hints.
 * The mask also excludes core's short-lived ID memory: its traversal-local IDs
 * may refer to completely different Lean terms in another inspection. */
export function continuityOptions(core: any, previous: InspectionPoint,
  current: InspectionPoint, state: LayoutState) {
  const matches = correspondingAtoms(previous, current);
  const ids = new Map(matches.map(m => [m.previous, m.current]));
  const positions = state.positions.flatMap(p => {
    const id = ids.get(p.id);
    return id === undefined ? [] : [{ ...p, id }];
  });
  if (!positions.length || typeof core.getSequencePolicy !== 'function') return undefined;
  const stability = core.getSequencePolicy('stability');
  if (!stability || stability.name !== 'stability') return undefined;
  const allowed = new Set(positions.map(p => p.id));
  return {
    policy: {
      name: 'lean-identity-stability',
      apply(context: any) {
        const result = stability.apply(context);
        return { ...result, effectivePriorState: result.effectivePriorState && {
          ...result.effectivePriorState,
          positions: result.effectivePriorState.positions.filter((p: { id: string }) =>
            allowed.has(p.id)),
        } };
      },
    },
    prevInstance: new core.JSONDataInstance(withLeanScalarTypes(previous.dataInstance)),
    currInstance: new core.JSONDataInstance(withLeanScalarTypes(current.dataInstance)),
    priorPositions: { ...state, positions },
    // Local IDs are not animation identities. Each pane renders its own graph.
    transitionMode: 'replace',
  };
}

/** Supply Lean's scalar classification to core's existing built-in hiding
 * policy. Core still decides visibility, after attributes and inferred edges;
 * neither datum is pruned or rewritten by this adapter. */
export function withLeanScalarTypes(data: RelationalData) {
  const builtins = new Set(['Nat', 'String', 'Float']);
  const names = new Set([
    ...data.atoms.map(a => a.type),
    ...data.relations.flatMap(r => r.types),
  ]);
  return {
    ...data,
    types: [...names].map(name => ({
      id: name,
      types: [name],
      atoms: data.atoms.filter(a => a.type === name),
      isBuiltin: builtins.has(name),
    })),
  };
}
