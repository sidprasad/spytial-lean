import assert from 'node:assert/strict';
import { test } from 'node:test';
import { correspondingAtoms, continuityOptions, pointTitle } from '../dist/inspection.js';

function point(ids = ['atom_0', 'atom_1'], scope = 'goal', identities = ['a', 'b']) {
  return { point: { scope }, inspection: { term: 'input' },
    dataInstance: { atoms: ids.map(id => ({ id, type: 'Tree', label: 'same label' })), relations: [] },
    identities: ids.map((atom, i) => ({ atom, identity: identities[i] })) };
}

test('titles use authored captions, otherwise the actual Lean expression', () => {
  assert.equal(pointTitle(point()), 'input');
  assert.equal(pointTitle({ ...point(), point: { title: 'After repaint' } }), 'After repaint');
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

test('only evidenced positions reach core stability; stale ID memory is masked', () => {
  const previous = point(['atom_0', 'atom_5']);
  const current = point(['atom_8', 'atom_2']);
  let calls = 0;
  const core = { JSONDataInstance: class { constructor(data) { this.data = data; } },
    getSequencePolicy: name => ({ name, apply: context => {
      calls++;
      return { effectivePriorState: { ...context.priorState, positions: [
        ...context.priorState.positions, { id: 'unrelated', x: 99, y: 99 },
      ] }, useReducedIterations: true };
    } }) };
  const state = { positions: [{ id: 'atom_5', x: 12, y: 34 }, { id: 'unmatched', x: 1, y: 2 }],
    transform: { k: 1, x: 0, y: 0 } };
  const options = continuityOptions(core, previous, current, state);
  assert.deepEqual(options.priorPositions.positions, [{ id: 'atom_2', x: 12, y: 34 }]);
  assert.deepEqual(options.policy.apply({ priorState: options.priorPositions })
    .effectivePriorState.positions, [{ id: 'atom_2', x: 12, y: 34 }]);
  assert.equal(calls, 1);
  assert.equal(options.transitionMode, 'replace');
  assert.equal(continuityOptions(core, previous, point(undefined, 'other'), state), undefined);
  assert.equal(continuityOptions({}, previous, current, state), undefined);
  assert.equal(state.positions[0].id, 'atom_5');
});
