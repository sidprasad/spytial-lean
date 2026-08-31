import assert from 'node:assert/strict';
import { test } from 'node:test';
import {
  initialInspectionMode, inspectionData, withLeanScalarTypes,
} from '../dist/inspection.js';

const selected = {
  atoms: [{ id: 't', type: 'Tree', label: 'node' }, { id: 'h', type: 'Nat', label: '3' }],
  relations: [{ id: 'height', name: 'height', types: ['Tree', 'Nat'],
    tuples: [{ atoms: ['t', 'h'], types: ['Tree', 'Nat'] }] }],
};
const full = { ...selected, atoms: [...selected.atoms, { id: 'old', type: 'Tree', label: 'node' }] };
const inspection = { root: 't', term: 'after', hasStructure: true,
  data: selected, facts: ['height old > 3'] };

test('structured inspections default to the selected value; scalars retain context', () => {
  assert.equal(initialInspectionMode(inspection), 'value');
  assert.equal(initialInspectionMode({ ...inspection, hasStructure: false }), 'context');
  assert.equal(initialInspectionMode(), 'context');
});

test('switching views preserves the original data and identities', () => {
  const before = JSON.stringify({ full, inspection });
  assert.equal(inspectionData(full, inspection, 'value'), selected);
  assert.equal(inspectionData(full, inspection, 'context'), full);
  assert.equal(inspectionData(full, undefined, 'value'), full);
  assert.equal(JSON.stringify({ full, inspection }), before);
});

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
