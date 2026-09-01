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
