// Optional downstream check against the user's CLRS-Lean fork. The original
// checkout is read only; only a generated proof excerpt under .lake is edited.
// node render/clrs-explorer-test.mjs /absolute/path/to/CLRS-Lean
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { chromium } from '@playwright/test';
import { leanDocument, browserPage, settled } from './infoview-test.mjs';
import { correspondingAtoms, continuityOptions } from '../widget/dist/inspection.js';

const downstream = path.resolve(process.argv[2]);
const sourcePath = path.join(downstream,
  'src/CLRSLean/FourthEdition/Chapter_13/Section_13_1_Red_Black_Trees.lean');
const original = fs.readFileSync(sourcePath, 'utf8');
const theorem = 'redBlackShape_repaint_rotateLeft_red_red';
const start = original.indexOf(`theorem ${theorem}`);
const proofStart = original.indexOf(' := by', start) + ' := by'.length;
const proofEnd = original.indexOf('  rcases ha', proofStart);
assert.ok(start >= 0 && proofStart > start && proofEnd > proofStart);
const end = original.indexOf('\n/-', proofEnd);
const inspections = `
  let input := node .red a x (node .red b y c)
  let rotated := rotateLeft input
  let repaired := repaintRoot .black rotated
  spytial input observing [blackHeight] with [
    .., attribute blackHeight,
    hideField RootBlack, hideField NoRedRed, hideField BalancedBlackHeight]
  spytial rotated observing [blackHeight] with [
    .., attribute blackHeight,
    hideField RootBlack, hideField NoRedRed, hideField BalancedBlackHeight]
    titled "After rotation"
  spytial repaired observing [blackHeight] with [
    .., attribute blackHeight,
    hideField RootBlack, hideField NoRedRed, hideField BalancedBlackHeight]
    titled "After repaint"
`;
// This excerpt needs only Mathlib's tactic-linter command, rather than the
// entire library imported by the much larger downstream chapter.
const text = (original.slice(0, proofStart) + inspections + original.slice(proofEnd, end) +
  '\nend RBTree\nend Chapter13\nend CLRS\n').replace('import Mathlib\n',
    'import Mathlib.Tactic.Linter.UnusedTactic\n');
const file = '.lake/ExplorerCLRS.lean';
fs.writeFileSync(file, text);
// Lake prepends this feature checkout's own imports, then the downstream's
// existing Mathlib cache. No dependency or file in CLRS-Lean is changed.
process.env.LEAN_PATH = execFileSync('lake', ['env', 'printenv', 'LEAN_PATH'],
  { cwd: downstream, encoding: 'utf8' }).trim();
const doc = await leanDocument(file, text);
let browser;
try {
  const lines = text.split('\n');
  const headerLine = lines.findIndex(l => l.includes(`theorem ${theorem}`));
  const [widget] = await doc.widgets(headerLine);
  assert.ok(widget?.props.explorer, JSON.stringify(doc.diagnostics));
  fs.writeFileSync('.lake/clrs-explorer-props.json', JSON.stringify(widget.props, null, 2));
  const points = widget.props.explorer.points;
  assert.deepEqual(points.map(p => p.inspection.term), ['input', 'rotated', 'repaired']);
  assert.deepEqual(points.map(p => p.point.title), [null, 'After rotation', 'After repaint']);
  const bAtoms = points.map(p => p.dataInstance.atoms.find(a => a.label === 'b').id);
  assert.notEqual(bAtoms[0], bAtoms[2], 'fixture demonstrates traversal-local IDs');
  for (let i = 1; i < points.length; i++) assert.ok(correspondingAtoms(points[0], points[i])
    .some(m => m.previous === bAtoms[0] && m.current === bAtoms[i]));
  assert.ok(points.every(p => p.inspection.facts.some(f => f.includes('blackHeight')) &&
    p.localContext.some(d => d.name === 'hab') && p.cndSpec.includes('orientation')));
  for (const fragment of ['spytial input', 'spytial rotated', 'spytial repaired']) {
    assert.equal((await doc.widgets(lines.findIndex(l => l.includes(fragment)))).length, 1);
  }
  browser = await chromium.launch({ headless: true });
  const { page, errors } = await browserPage(browser, widget.props);
  await settled(page, 2);
  await page.getByLabel('Right inspection point').selectOption('1');
  await settled(page, 2);
  await page.getByRole('button', { name: 'All points', exact: true }).click();
  await settled(page, 3);
  await page.screenshot({ path: '.lake/clrs-explorer.png', fullPage: true });
  assert.deepEqual(await page.evaluate(() => window.__spytialEvents.filter(e =>
    ['constraint-error', 'layout-generation-error'].includes(e))), []);
  const states = await page.locator('webcola-cnd-graph').evaluateAll(graphs => graphs.map(g => ({
    layout: g.getLayoutState(), seed: g.getLastSeedState?.(),
  })));
  for (let i = 0; i < points.length; i++) {
    const pos = new Map(states[i].layout.positions.map(p => [p.id, p]));
    for (const relation of points[i].dataInstance.relations.filter(r =>
      ['node_1', 'node_3'].includes(r.name))) for (const { atoms: [parent, child] } of relation.tuples) {
      if (!pos.has(parent) || !pos.has(child)) continue;
      assert.ok(pos.get(child).y > pos.get(parent).y, `${relation.name} stays below its parent`);
      assert.ok(relation.name === 'node_1' ? pos.get(child).x < pos.get(parent).x :
        pos.get(child).x > pos.get(parent).x, `${relation.name} keeps left/right order`);
    }
  }
  const expectedHint = states[0].layout.positions.find(p => p.id === bAtoms[0]);
  const actualHint = states[1].seed.positions.find(p => p.id === bAtoms[1]);
  assert.equal(actualHint.x, expectedHint.x);
  assert.equal(actualHint.y, expectedHint.y);
  assert.deepEqual(errors, []);
  assert.deepEqual(doc.diagnostics.flatMap(d => d.diagnostics).filter(d => d.severity === 1), []);
  fs.writeFileSync('.lake/clrs-explorer-props.json', JSON.stringify(widget.props, null, 2));
  await page.screenshot({ path: '.lake/clrs-explorer.png', fullPage: true });
  assert.equal(fs.readFileSync(sourcePath, 'utf8'), original, 'downstream source stays unchanged');
  console.log(`CLRS infoview and browser passed: b ${bAtoms.join(' → ')}; exact identity hints, three actual terms, captions, line widgets, proof facts, and parent/child constraints.`);
} finally { await browser?.close(); doc.close(); }
