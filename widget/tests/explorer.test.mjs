import assert from 'node:assert/strict';
import { test } from 'node:test';
import { getSequencePolicy, parseLayoutSpec } from 'spytial-core';
import { compareFacts, correspondingAtoms, continuityOptions, factsInContext,
  inspectionDisplayData, pointTitle } from '../dist/inspection.js';

function point(ids = ['atom_0', 'atom_1'], scope = 'goal', identities = ['a', 'b']) {
  return { point: { scope }, inspection: { term: 'input' },
    dataInstance: { atoms: ids.map(id => ({ id, type: 'Tree', label: 'same label' })), relations: [] },
    identities: ids.map((atom, i) => ({ atom, identity: identities[i] })) };
}

test('titles use authored captions, otherwise the actual Lean expression', () => {
  assert.equal(pointTitle(point()), 'input');
  assert.equal(pointTitle({ ...point(), point: { title: 'After repaint' } }), 'After repaint');
});

test('facts stay in declaration order with one row per fact, including multi-source derivations', () => {
  const inspection = { facts: ['P x', 'Q x', 'R x', 'S x'] };
  const localContext = [{ type: 'Nat' }, { type: 'P x' }, { type: 'T x' }];
  assert.deepEqual(factsInContext({ inspection, localContext, factSources: [[1], [1, 2], [1], []] }), {
    locals: [{ derived: [], direct: undefined }, { derived: [2], direct: 0 },
      { derived: [1], direct: undefined }], other: [3],
  });
  assert.deepEqual(factsInContext({ inspection }), { locals: [], other: [0, 1, 2, 3] });
});

test('fact comparisons use proposition identity even when different locals print alike', () => {
  const left = { inspection: { facts: ['P x', 'Q x'] }, factIds: [0, 1] };
  const right = { inspection: { facts: ['Q y', 'P x'] }, factIds: [1, 2] };
  assert.deepEqual(compareFacts(left, right), [new Set([0]), new Set([1])]);
  assert.deepEqual(compareFacts(left, left), [new Set(), new Set()]);
  assert.deepEqual(compareFacts({}, right), [new Set(), new Set([0, 1])]);
  assert.deepEqual(compareFacts({ inspection: left.inspection }, right), [new Set([1]), new Set([0])]);
  const repeated = { inspection: { facts: ['P x', 'P x', 'P x'] }, factIds: [0, 2, 0] };
  assert.deepEqual(compareFacts(repeated, right), [new Set([0, 2]), new Set([0])]);
});

test('inspection numbers qualify generated names and their symbolic references', () => {
  const data = { atoms: ['¿x?', '¿x??', '(max ¿x? ¿x??) + 1', 'x', '¿x?', '¿x₁?']
    .map((label, i) => ({ id: `atom_${i}`, type: 'Nat', label })), relations: [] };
  const inspection = {
    generatedAtoms: ['atom_0', 'atom_1', 'atom_2', 'atom_5'],
    placeholders: ['¿x?', '¿x??', '¿x₁?'],
  };
  const display = inspectionDisplayData(data, inspection, 12);
  assert.deepEqual(display.atoms.map(a => a.label), [
    '¿x?₁₂', '¿x??₁₂', '(max ¿x?₁₂ ¿x??₁₂) + 1', 'x', '¿x?', '¿x₁?₁₂',
  ]);
  assert.deepEqual(display.atoms.map(a => a.id), data.atoms.map(a => a.id));
  assert.equal(display.relations, data.relations);
  assert.equal(data.atoms[0].label, '¿x?');
  assert.equal(inspectionDisplayData(data, inspection), data);
  assert.equal(inspectionDisplayData(data, {}, 12), data);
});

test('rotated subtree b follows its Lean identity despite changed traversal IDs', () => {
  const a = point(['atom_2', 'atom_5']);
  const b = point(['atom_4', 'atom_3']);
  assert.deepEqual(correspondingAtoms(a, b), [
    { previous: 'atom_2', current: 'atom_4' }, { previous: 'atom_5', current: 'atom_3' },
  ]);
  assert.deepEqual(correspondingAtoms(a, point(undefined, 'siblingGoal')), []);
  assert.deepEqual(correspondingAtoms(a, point(undefined, 'goal', ['other', 'unrelated'])), []);
  assert.deepEqual(correspondingAtoms({ ...a, identities: [] }, b), []);
});

test('ambiguous aliases and incompatible atom types do not imply correspondence', () => {
  const a = point(undefined, 'goal', ['alias', 'alias']);
  assert.deepEqual(correspondingAtoms(a, point(undefined, 'goal', ['alias', 'b'])), []);
  const b = point();
  b.dataInstance.atoms[0].type = 'Other';
  assert.deepEqual(correspondingAtoms(point(), b), [{ previous: 'atom_1', current: 'atom_1' }]);
});

test('only positions backed by Lean identity survive the core stability policy', () => {
  const previous = point(['atom_0', 'atom_5']);
  const current = point(['atom_8', 'atom_2']);
  const state = { positions: [{ id: 'atom_5', x: 12, y: 34 }, { id: 'unmatched', x: 1, y: 2 }],
    transform: { k: 1, x: 0, y: 0 } };
  const options = continuityOptions(previous, current, state);
  const context = { prevInstance: options.prevInstance, currInstance: options.currInstance,
    spec: parseLayoutSpec(''), priorState: options.priorPositions };
  const matched = { id: 'atom_2', x: 12, y: 34 };
  assert.deepEqual(context.priorState.positions, [matched]);

  // A previous render remembered atom_8, but this point has no evidence for its position.
  const stability = getSequencePolicy('stability');
  const stale = { id: 'atom_8', x: 99, y: 99 };
  stability.apply({ ...context, priorState: { ...state, positions: [stale] } });
  assert.ok(stability.apply(context).effectivePriorState.positions.some(p => p.id === stale.id),
    'the core policy would reuse the stale position without the Lean identity filter');
  assert.deepEqual(options.policy.apply(context).effectivePriorState.positions, [matched]);
  assert.equal(options.transitionMode, 'replace');
  assert.equal(continuityOptions(previous, point(undefined, 'other'), state), undefined);
  assert.equal(state.positions[0].id, 'atom_5');
});
