import assert from 'node:assert/strict';
import { test } from 'node:test';
import { withLeanScalarTypes } from '../dist/inspection.js';

const selected = {
  atoms: [{ id: 't', type: 'Tree', label: 'node' }, { id: 'h', type: 'Nat', label: '3' }],
  relations: [{ id: 'height', name: 'height', types: ['Tree', 'Nat'],
    tuples: [{ atoms: ['t', 'h'], types: ['Tree', 'Nat'] }] }],
};
test('Lean scalar metadata delegates orphan hiding to core without pruning data', () => {
  const before = JSON.stringify(selected);
  const enriched = withLeanScalarTypes(selected);
  assert.equal(enriched.atoms, selected.atoms);
  assert.equal(enriched.relations, selected.relations);
  assert.deepEqual(enriched.types.find(t => t.id === 'Nat'), {
    id: 'Nat', types: ['Nat'], atoms: [selected.atoms[1]], isBuiltin: true,
  });
  assert.equal(enriched.types.find(t => t.id === 'Tree').isBuiltin, false);
  assert.equal(JSON.stringify(selected), before);
});

test('empty context-only relation declarations keep their type vocabulary', () => {
  const data = { atoms: [], relations: [
    { id: 'lt', name: 'lt', types: ['Nat', 'Nat'], tuples: [] },
  ] };
  assert.deepEqual(withLeanScalarTypes(data).types, [
    { id: 'Nat', types: ['Nat'], atoms: [], isBuiltin: true },
  ]);
});
