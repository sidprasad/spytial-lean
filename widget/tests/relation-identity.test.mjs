import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { test } from 'node:test';
import { JSONDataInstance, SGraphQueryEvaluator } from 'spytial-core';
import { withLeanScalarTypes } from '../dist/inspection.js';

test('Lean atom unions and products parse in the bundled browser evaluator', () => {
  // Consume the exact output pinned by Lean's lowering tests.
  const golden = readFileSync(new URL(
    '../../SpytialTests/SelectorLoweringTest.golden.tsv', import.meta.url), 'utf8');
  const selectors = new Map(golden.trim().split('\n').map(line => line.split('\t')));
  const instance = new JSONDataInstance({
    atoms: [0, 1, 2].map(n => ({ id: `atom_${n}`, type: 'Tree', label: 'node' })),
    // An atom literal must select its ID, even when a relation has that name.
    relations: [{ id: 'atom_0', name: 'atom_0', types: ['Tree'],
      tuples: [{ atoms: ['atom_2'], types: ['Tree'] }] }],
  });
  const evaluator = new SGraphQueryEvaluator();
  evaluator.initialize({ sourceData: instance });
  assert.deepEqual(evaluator.evaluate('atom_0').selectedAtoms(), ['atom_2']);
  assert.deepEqual(evaluator.evaluate(selectors.get('atoms.union')).selectedAtoms().sort(),
    ['atom_0', 'atom_1']);
  assert.deepEqual(evaluator.evaluate(selectors.get('atoms.product')).selectedTuplesAll(),
    [['atom_0', 'atom_1']]);
});

test('Lean payload preserves relation IDs while selectors union matching names', () => {
  const tuple = (owner, child) => ({ atoms: [owner, child], types: ['Cell', 'Nat'] });
  const data = {
    atoms: [
      { id: 'a', type: 'Cell', label: 'mk' },
      { id: 'b', type: 'Cell', label: 'mk' },
      { id: 'one', type: 'Nat', label: '1' },
      { id: 'two', type: 'Nat', label: '2' },
    ],
    relations: [
      { id: 'A:value', name: 'value', types: ['Cell', 'Nat'],
        tuples: [tuple('a', 'one')] },
      { id: 'B:value', name: 'value', types: ['Cell', 'Nat'],
        tuples: [tuple('a', 'one'), tuple('b', 'two')] },
      { id: 'Ternary:value', name: 'value', types: ['Cell', 'Nat', 'Nat'],
        tuples: [{ atoms: ['a', 'one', 'two'], types: ['Cell', 'Nat', 'Nat'] }] },
      { id: 'Empty:value', name: 'value', types: ['Cell', 'Nat'], tuples: [] },
    ],
  };
  const before = JSON.stringify(data);
  // Use the same adapter and evaluator initialization as SpytialWidget.
  const instance = new JSONDataInstance(withLeanScalarTypes(data));
  const evaluator = new SGraphQueryEvaluator();
  evaluator.initialize({ sourceData: instance });

  assert.deepEqual(instance.getRelations(), data.relations);
  assert.deepEqual(evaluator.evaluate('value').selectedTuplesAll().sort(),
    [['a', 'one'], ['a', 'one', 'two'], ['b', 'two']]);
  assert.equal(evaluator.evaluate('#value').prettyPrint(), '3');
  assert.deepEqual(evaluator.evaluate('b.value').selectedAtoms(), ['two']);
  const received = new JSONDataInstance(JSON.stringify(instance.reify()));
  assert.deepEqual(received.getRelations(), data.relations);
  assert.equal(JSON.stringify(data), before);
});

test('existing Lean payloads with relation ID equal to name still query normally', () => {
  const instance = new JSONDataInstance(withLeanScalarTypes({
    atoms: [
      { id: 'cell', type: 'Cell', label: 'mk' },
      { id: 'one', type: 'Nat', label: '1' },
    ],
    relations: [{ id: 'value', name: 'value', types: ['Cell', 'Nat'],
      tuples: [{ atoms: ['cell', 'one'], types: ['Cell', 'Nat'] }] }],
  }));
  const evaluator = new SGraphQueryEvaluator();
  evaluator.initialize({ sourceData: instance });
  assert.deepEqual(evaluator.evaluate('value').selectedTuplesAll(), [['cell', 'one']]);
});
