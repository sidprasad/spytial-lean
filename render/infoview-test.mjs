// Exercise the same RPC used when a cursor moves in the Lean infoview, then
// render those exact props with the production widget in Chromium.
// Run from the repository root after `lake build SpytialTests renderHarnessJs`.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { spawn } from 'node:child_process';
import { pathToFileURL } from 'node:url';
import { chromium } from '@playwright/test';

export async function leanDocument(file, text = fs.readFileSync(file, 'utf8')) {
  const root = process.cwd();
  const uri = pathToFileURL(path.resolve(file)).href;
  const server = spawn('lake', ['env', 'lean', '--server'], { cwd: root });
  const pending = new Map();
  const diagnostics = [];
  let buffer = Buffer.alloc(0), nextId = 0;
  server.stderr.on('data', data => process.stderr.write(data));
  server.stdout.on('data', data => {
    buffer = Buffer.concat([buffer, data]);
    while (true) {
      const end = buffer.indexOf('\r\n\r\n');
      if (end < 0) return;
      const length = Number(/Content-Length: (\d+)/i.exec(buffer.subarray(0, end).toString())[1]);
      if (buffer.length < end + 4 + length) return;
      const message = JSON.parse(buffer.subarray(end + 4, end + 4 + length).toString());
      buffer = buffer.subarray(end + 4 + length);
      if (message.method && message.id !== undefined) {
        send({ id: message.id, result: null });
      } else if (pending.has(message.id)) {
        const { resolve, reject, timeout } = pending.get(message.id);
        pending.delete(message.id); clearTimeout(timeout);
        message.error ? reject(new Error(JSON.stringify(message.error))) : resolve(message.result);
      } else if (message.method === 'textDocument/publishDiagnostics') {
        diagnostics.push(message.params);
      }
    }
  });
  server.on('exit', code => {
    for (const p of pending.values()) { clearTimeout(p.timeout); p.reject(new Error(`Lean exited: ${code}`)); }
    pending.clear();
  });
  function send(message) {
    const body = JSON.stringify({ jsonrpc: '2.0', ...message });
    server.stdin.write(`Content-Length: ${Buffer.byteLength(body)}\r\n\r\n${body}`);
  }
  function request(method, params) {
    const id = ++nextId;
    return new Promise((resolve, reject) => {
      const timeout = setTimeout(() => { pending.delete(id); reject(new Error(`Timed out: ${method}`)); },
        Number(process.env.SPYTIAL_RPC_TIMEOUT_MS ?? 60_000));
      pending.set(id, { resolve, reject, timeout });
      send({ id, method, params });
    });
  }
  try {
    await request('initialize', { processId: process.pid, rootUri: pathToFileURL(root).href,
      capabilities: {} });
    send({ method: 'initialized', params: {} });
    send({ method: 'textDocument/didOpen', params: { textDocument: {
      uri, languageId: 'lean4', version: 1, text,
    } } });
    const { sessionId } = await request('$/lean/rpc/connect', { uri });
    const keepAlive = setInterval(() => send({ method: '$/lean/rpc/keepAlive',
      params: { uri, sessionId } }), 10_000);
    const rpc = (method, params, position) => request('$/lean/rpc/call', {
      textDocument: { uri }, position, sessionId, method, params,
    });
    return {
      diagnostics,
      widgets: async line => (await rpc('Lean.Widget.getWidgets', { line, character: 0 },
        { line, character: 0 })).widgets.filter(w => w.id === 'SpytialLean.SpytialWidget'),
      source: async (widget, line) => (await rpc('Lean.Widget.getWidgetSource', {
        hash: widget.javascriptHash, pos: { line, character: 0 },
      }, { line, character: 0 })).sourcetext,
      change(newText) {
        send({ method: 'textDocument/didChange', params: { textDocument: { uri, version: 2 },
          contentChanges: [{ text: newText }] } });
      },
      close: () => { clearInterval(keepAlive); server.kill(); },
    };
  } catch (error) { server.kill(); throw error; }
}

export async function browserPage(browser, props) {
  const page = await browser.newPage({ viewport: { width: 1300, height: 1000 } });
  const errors = [];
  page.on('pageerror', error => errors.push(error.stack ?? error.message));
  await page.setContent('<html><body><div id="root"></div></body></html>');
  await page.evaluate(props => { window.__CASE__ = props; }, props);
  await page.addScriptTag({ path: path.resolve('render/dist/harness.js') });
  return { page, errors };
}

export async function expandExplorer(page, pointCount) {
  const disclosure = page.locator('details.spytial-theorem-inspections');
  await disclosure.waitFor({ state: 'visible' });
  assert.equal(await disclosure.evaluate(el => el.open), false, 'theorem inspections start collapsed');
  assert.equal(await page.locator('webcola-cnd-graph').count(), 0, 'closed inspections do not mount diagrams');
  assert.equal(await page.getByLabel('Inspection view mode').count(), 0, 'controls wait for expansion');
  await page.getByText(`Spytial inspections (${pointCount})`, { exact: true }).click();
}

export async function settled(page, count) {
  try {
    await page.waitForFunction(count =>
      [...document.querySelectorAll('webcola-cnd-graph[data-layout-settled=true]')]
        .filter(g => g.shadowRoot?.querySelector('svg') || g.querySelector('svg')).length === count &&
      !document.querySelector('.spytial-loading, .spytial-error'), count, { timeout: 60_000 });
    // View fitting animates after the solver settles. This also catches a
    // retained graph whose viewport was not updated when the pane count changed.
    await page.waitForFunction(() => [...document.querySelectorAll('webcola-cnd-graph')].every(g => {
      const bounds = g.getBoundingClientRect();
      return [...(g.shadowRoot ?? g).querySelectorAll('g.node')].every(n => {
        const r = n.getBoundingClientRect();
        return !r.width || (r.left >= bounds.left - 2 && r.right <= bounds.right + 2 &&
          r.top >= bounds.top - 2 && r.bottom <= bounds.bottom + 2);
      });
    }), undefined, { timeout: 15_000 });
  } catch (error) {
    console.error(await page.evaluate(() => ({ text: document.body.innerText,
      events: window.__spytialEvents, graphs: [...document.querySelectorAll('webcola-cnd-graph')]
        .map(g => ({ settled: g.dataset.layoutSettled, svg: !!g.querySelector('svg'),
          shadowSvg: !!g.shadowRoot?.querySelector('svg') })) })));
    await page.screenshot({ path: '.lake/explorer-failure.png', fullPage: true });
    throw error;
  }
}

// Read the text actually covered in SVG coordinates so a misplaced marker
// (or a marker painted on top of the glyphs) fails the interaction test.
async function markedLines(graph) {
  return graph.locator('.label-highlight-marker').evaluateAll(marks => marks.map(mark => {
    const box = mark.getBBox();
    const label = mark.parentElement.querySelector('text.linklabel, text.label');
    if (!(mark.compareDocumentPosition(label) & Node.DOCUMENT_POSITION_FOLLOWING)) return null;
    const edge = label.matches('.linklabel');
    const candidates = edge ? [label] : [...label.querySelectorAll('tspan')];
    const line = candidates.find(line => {
      const r = line.getBBox();
      return box.x <= r.x && box.x + box.width >= r.x + r.width &&
        box.y <= r.y + r.height / 2 && r.y + r.height / 2 <= box.y + box.height;
    });
    return [edge ? 'edge' : label.querySelector('.main-label-tspan').textContent, line?.textContent];
  }).sort());
}

async function main() {
  const file = 'SpytialTests/ExplorerTest.lean';
  const text = fs.readFileSync(file, 'utf8');
  const lines = text.split('\n');
  const lineOf = fragment => { const i = lines.findIndex(l => l.includes(fragment)); assert.ok(i >= 0); return i; };
  const doc = await leanDocument(file, text);
  let browser;
  try {
    const headerLine = lineOf('theorem explorerThree');
    const [header] = await doc.widgets(headerLine);
    assert.ok(header?.props.explorer, 'theorem name exposes the explorer');
    fs.writeFileSync('.lake/explorer-props.json', JSON.stringify(header.props, null, 2));
    const points = header.props.explorer.points;
    assert.equal(points.length, 3);
    assert.deepEqual(points.map(p => p.inspection.term), ['input', 'rotated', 'repaired']);
    assert.deepEqual(points.map(p => p.point.title), [null, 'After rotation', 'After repaint']);
    assert.deepEqual(points.map(p => p.point.line), [9, 10, 11]);
    assert.equal(new Set(points.map(p => p.point.scope)).size, 1);
    assert.ok(points.every(p => p.localContext.some(d => d.name === 'h') &&
      p.observations.some(o => o.endsWith('List.length')) && p.inspection.facts.length));
    for (const p of points) {
      const generated = p.dataInstance.atoms.find(a => a.label === '¿x?');
      assert.ok(p.inspection.generatedAtoms.includes(generated?.id));
      assert.ok(p.inspection.placeholders.includes(generated.label));
    }
    for (let i = 0; i < points.length; i++) {
      const widgets = await doc.widgets(lineOf(['spytial input', 'spytial rotated', 'spytial repaired'][i]));
      assert.equal(widgets.length, 1, 'one ordinary widget at each proof line');
      assert.deepEqual(widgets[0].props, points[i]);
    }
    assert.equal(await doc.source(header, headerLine),
      fs.readFileSync('.lake/build/js/spytialWidget.js', 'utf8'), 'infoview serves current bundle');
    const [single] = await doc.widgets(lineOf('theorem explorerSingle'));
    assert.equal(single.props.explorer.points.length, 1);
    const [exclusion] = await doc.widgets(lineOf('theorem explorerExclusion'));
    const [omitted, restored] = exclusion.props.explorer.points;
    assert.deepEqual(omitted.inspection.facts, []);
    assert.ok(restored.inspection.facts.length > 0);
    assert.deepEqual(omitted.dataInstance.atoms.map(a => a.label), ['x']);
    assert.ok(restored.dataInstance.atoms.some(a => a.label === '7'));
    assert.equal(omitted.localContext.find(d => d.name === 'h').excluded, true);
    assert.ok(!restored.localContext.find(d => d.name === 'h').excluded);
    const [termExclusion] = await doc.widgets(lineOf('def termExclusion'));
    assert.deepEqual(termExclusion.props.explorer.points[0].dataInstance, omitted.dataInstance);
    const [branches] = await doc.widgets(lineOf('theorem explorerBranches'));
    assert.equal(branches.props.explorer.points.length, 2);
    assert.notEqual(...branches.props.explorer.points.map(p => p.point.scope));
    const [rollback] = await doc.widgets(lineOf('theorem explorerRollback'));
    assert.deepEqual(rollback.props.explorer.points.map(p => p.point.title), ['Retained']);
    assert.equal((await doc.widgets(lineOf('theorem explorerWithoutInspections'))).length, 0);
    assert.equal((await doc.widgets(lineOf('theorem qualified')))[0].props.explorer.points.length, 1);

    const [functionHeader] = await doc.widgets(lineOf('def swapFirstTwo'));
    const sites = functionHeader.props.explorer.points;
    assert.deepEqual(sites.map(p => p.point.title), ['New tail', 'Result', 'Short list']);
    for (const p of sites) {
      const [lineWidget] = await doc.widgets(p.point.line - 1);
      assert.deepEqual(lineWidget.props, p);
    }
    assert.ok(sites[0].point.scope);
    assert.equal(sites[0].point.scope, sites[1].point.scope);
    assert.notEqual(sites[0].point.scope, sites[2].point.scope);
    const tailIdentity = p => {
      const atom = p.dataInstance.atoms.find(a => a.label === 'tail');
      assert.ok(atom);
      const evidence = p.identities.find(i => i.atom === atom.id);
      assert.ok(evidence);
      return evidence.identity;
    };
    assert.equal(tailIdentity(sites[0]), tailIdentity(sites[1]));
    const [guarded] = await doc.widgets(lineOf('def guardedTail'));
    const [empty, nonempty] = guarded.props.explorer.points;
    assert.notEqual(empty.point.scope, nonempty.point.scope);
    assert.ok(empty.localContext.some(d => d.name === 'h'));
    assert.notDeepEqual(empty.factIds, nonempty.factIds);
    const [factChanges] = await doc.widgets(lineOf('theorem explorerFactChanges'));
    const [pq, r, all] = factChanges.props.explorer.points;
    assert.deepEqual(pq.inspection.facts, ['P x', 'Q x']);
    assert.deepEqual(r.inspection.facts, ['R x']);
    assert.deepEqual(pq.factSources.map(s => s.map(i => pq.localContext[i].name)), [['hpq'], ['hpq']]);
    assert.deepEqual(all.factIds, [...pq.factIds, ...r.factIds]);
    const [heights] = await doc.widgets(lineOf('def explorerHeightContext'));
    const [heightPoint] = heights.props.explorer.points;
    const heightsFact = heightPoint.inspection.factTargets[heightPoint.inspection.facts.indexOf('a.length < b.length')];
    const names = new Map(heightPoint.dataInstance.atoms.map(a => [a.id, a.label]));
    assert.deepEqual(heightsFact.tuples.filter(t =>
      heightPoint.dataInstance.relations.find(r => r.id === t.relation)?.name === 'length')
      .map(t => names.get(t.atoms[0])).sort(), ['a', 'b']);
    const [branchFacts] = await doc.widgets(lineOf('theorem explorerBranchFacts'));
    const [branchA, branchB] = branchFacts.props.explorer.points;
    assert.deepEqual(branchA.inspection.facts, branchB.inspection.facts);
    assert.notDeepEqual(branchA.factIds, branchB.factIds, 'same spelling, distinct branch locals');
    const [delayed] = await doc.widgets(lineOf('def mapIdentity'));
    assert.equal(delayed.props.explorer.points.length, 1);
    const [resolved] = await doc.widgets(lineOf('List.map (spytial id)'));
    assert.deepEqual(resolved.props, delayed.props.explorer.points[0]);

    // Check the serialized diagrams as well as the inferred Lean definitions.
    for (const [name, site, local, atomType] of [
      ['inferredElement', 'fun x => spytial x', { name: 'x', type: 'Nat', value: null }, 'Nat'],
      ['inferredList', 'let ys := spytial xs', { name: 'xs', type: 'List Nat', value: '[]' }, 'List'],
      ['inferredLocalType', 'let head := spytial', { name: 'xs', type: 'List Nat', value: '[]' }, 'Nat'],
      ['inferredLocalValue', 'let result := spytial', { name: 'n', type: 'Nat', value: '3' }, 'Nat'],
    ]) {
      const [header] = await doc.widgets(lineOf(`def ${name}`));
      const widgets = await doc.widgets(lineOf(site));
      assert.equal(widgets.length, 1, name);
      const point = widgets[0].props;
      assert.deepEqual(header?.props.explorer.points, [point], name);
      assert.deepEqual(point.localContext.find(d => d.name === local.name), local, name);
      assert.equal(point.dataInstance.atoms.find(a => a.id === point.inspection.root)?.type,
        atomType, name);
    }

    browser = await chromium.launch({ headless: true });
    const { page, errors } = await browserPage(browser, header.props);
    const unknownLabels = () => page.locator('webcola-cnd-graph').evaluateAll(graphs =>
      graphs.map(g => Array.from((g.shadowRoot ?? g).querySelectorAll('g.node .label'),
        n => n.textContent.trim()).filter(label => label.startsWith('¿'))));
    await expandExplorer(page, 3);
    await settled(page, 2);
    assert.deepEqual(await unknownLabels(), [['¿x?₁'], ['¿x?₃']]);
    assert.deepEqual(errors, [], 'opening the explorer');
    assert.equal(await page.getByLabel('Left inspection point').inputValue(), '0');
    assert.equal(await page.getByLabel('Right inspection point').inputValue(), '2');
    await page.getByLabel('Right inspection point').selectOption('1');
    await settled(page, 2);
    assert.deepEqual(errors, [], 'changing the right inspection');
    await page.getByLabel('Left inspection point').selectOption('2');
    await settled(page, 2);
    assert.deepEqual(await unknownLabels(), [['¿x?₃'], ['¿x?₂']]);
    assert.deepEqual(errors, [], 'changing the left inspection');
    const summary = page.getByText('Spytial inspections (3)', { exact: true });
    await summary.click();
    await page.waitForFunction(() => document.querySelectorAll('webcola-cnd-graph').length === 0);
    await summary.click();
    await settled(page, 2);
    assert.deepEqual(errors, [], 'closing and reopening the explorer');
    assert.equal(await page.getByLabel('Left inspection point').inputValue(), '2');
    assert.equal(await page.getByLabel('Right inspection point').inputValue(), '1');
    await page.getByRole('button', { name: 'Step through', exact: true }).click();
    await settled(page, 1);
    assert.deepEqual(await unknownLabels(), [['¿x?₁']]);
    assert.deepEqual(errors, [], 'switching to stepping');
    await page.getByRole('button', { name: 'Next', exact: true }).click();
    assert.equal(await page.getByLabel('Inspection point', { exact: true }).inputValue(), '1');
    await page.getByRole('button', { name: 'Previous', exact: true }).click();
    assert.equal(await page.getByLabel('Inspection point', { exact: true }).inputValue(), '0');
    await page.getByRole('button', { name: 'All points', exact: true }).click();
    await settled(page, 3);
    assert.deepEqual(await unknownLabels(), [['¿x?₁'], ['¿x?₂'], ['¿x?₃']]);
    assert.equal(await page.getByText('After rotation', { exact: true }).count(), 1);
    assert.equal(await page.getByText('After repaint', { exact: true }).count(), 1);
    assert.deepEqual(errors, []);
    await page.screenshot({ path: '.lake/explorer-all.png', fullPage: true });
    await page.close();
    const facts = await browserPage(browser, factChanges.props);
    await expandExplorer(facts.page, 3);
    const leftSelect = facts.page.getByLabel('Left inspection point', { exact: true });
    const rightSelect = facts.page.getByLabel('Right inspection point', { exact: true });
    const contexts = facts.page.getByRole('region', { name: 'Context declarations and facts' });
    const uniqueRows = pane => pane.locator('.spytial-only-here code').allTextContents();
    await rightSelect.selectOption('1');
    await settled(facts.page, 2);
    assert.deepEqual(await uniqueRows(contexts.nth(0)), ['P x', 'Q x']);
    assert.deepEqual(await uniqueRows(contexts.nth(1)), ['hr : R x']);
    const leftTint = 'rgba(110, 68, 150, 0.2)', rightTint = 'rgba(39, 125, 145, 0.2)';
    await facts.page.addStyleTag({ content: `:root {
      --vscode-diffEditor-removedLineBackground: ${leftTint};
      --vscode-diffEditor-insertedLineBackground: ${rightTint};
    }` });
    const tints = rows => rows.evaluateAll(els => els.map(el => getComputedStyle(el).backgroundColor));
    assert.deepEqual(await tints(contexts.locator('.spytial-only-here')), [leftTint, leftTint, rightTint]);
    assert.deepEqual(await tints(facts.page.locator('header .spytial-only-here')), [leftTint, rightTint]);
    const q = contexts.nth(0).getByRole('button', { name: 'Q x (only at this point)' });
    assert.ok(await q.isVisible(), 'a hypothesis with unique derived facts starts expanded');
    await q.focus();
    const diagrams = facts.page.locator('webcola-cnd-graph');
    assert.deepEqual(await markedLines(diagrams.nth(0)), [['edge', 'Q']]);
    assert.deepEqual(await markedLines(diagrams.nth(1)), []);
    await facts.page.getByRole('button', { name: 'Next pair' }).click();
    await settled(facts.page, 2);
    assert.deepEqual([await leftSelect.inputValue(), await rightSelect.inputValue()], ['1', '2']);
    assert.deepEqual(await uniqueRows(contexts.nth(0)), []);
    assert.deepEqual(await uniqueRows(contexts.nth(1)), ['P x', 'Q x']);
    for (const pane of [contexts.nth(0), contexts.nth(1)]) {
      assert.ok(await pane.getByRole('button', { name: 'hr : R x', exact: true }).isVisible());
    }
    await facts.page.getByRole('button', { name: 'Previous pair' }).click();
    await leftSelect.selectOption('1');
    await settled(facts.page, 2);
    assert.equal(await rightSelect.inputValue(), '1', 'both selectors can use the same point');
    assert.equal(await contexts.locator('.spytial-only-here').count(), 0);
    assert.equal(await facts.page.getByText('All shared', { exact: true }).count(), 2);
    await rightSelect.selectOption('2');
    await settled(facts.page, 2);
    await facts.page.getByRole('button', { name: 'Step through' }).click();
    await settled(facts.page, 1);
    assert.equal(await facts.page.locator('.spytial-only-here').count(), 0, 'single points have no comparison marks');
    const source = facts.page.locator('.spytial-context-decl details');
    assert.match(await source.locator('summary').innerText(), /hpq : P x ∧ Q x/);
    await source.locator('summary').click();
    assert.deepEqual(await source.getByRole('button').allTextContents(), ['P x', 'Q x']);
    const pFact = source.getByRole('button', { name: 'P x', exact: true });
    const factGraph = facts.page.locator('webcola-cnd-graph');
    const strokes = () => factGraph.locator('path[data-link-id]').evaluateAll(paths =>
      paths.map(path => [getComputedStyle(path).stroke, getComputedStyle(path).strokeWidth]));
    const originalStrokes = await strokes();
    assert.ok(await factGraph.getByText('Q witness x', { exact: true }).isVisible());
    await source.getByRole('button', { name: 'Q x', exact: true }).hover();
    assert.deepEqual(await markedLines(factGraph), [['edge', 'Q']]);
    await pFact.focus();
    assert.equal(await pFact.getAttribute('data-active'), 'true');
    assert.deepEqual(await markedLines(factGraph), [['edge', 'P']]);
    assert.deepEqual(await factGraph.locator('g.highlighted .main-label-tspan').allTextContents(), ['x']);
    assert.deepEqual(await strokes(), originalStrokes);
    await pFact.press('Enter');
    assert.equal(await pFact.getAttribute('aria-pressed'), 'true');
    await pFact.press('Escape');
    assert.equal(await factGraph.locator('.highlighted, .label-highlight-marker').count(), 0);
    assert.deepEqual(facts.errors, []);
    await facts.page.close();
    const heightView = await browserPage(browser, heightPoint);
    await heightView.page.setViewportSize({ width: 420, height: 520 });
    // Other proof information below the widget makes the infoview itself scrollable.
    await heightView.page.evaluate(() => { document.body.style.minHeight = '200vh'; });
    await settled(heightView.page, 1);
    const divider = heightView.page.getByRole('separator', { name: 'Diagram height' });
    await divider.press('End');
    assert.equal(await divider.getAttribute('aria-valuenow'), '80');
    const declarations = heightView.page.getByRole('region', { name: 'Context declarations and facts' });
    const graph = heightView.page.locator('webcola-cnd-graph');
    await declarations.scrollIntoViewIfNeeded();
    const graphY = (await graph.boundingBox()).y;
    await declarations.hover();
    await heightView.page.mouse.wheel(0, 800);
    await heightView.page.waitForFunction(() => document.querySelector('.spytial-context-scroll').scrollTop > 0);
    await heightView.page.mouse.wheel(0, 800);
    await heightView.page.evaluate(() => new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve))));
    assert.equal((await graph.boundingBox()).y, graphY);
    const outer = declarations.getByRole('button', { name: 'outer : a.length < b.length' });
    await outer.hover();
    assert.ok(await graph.getByText('Observed length a.length', { exact: true }).isVisible());
    const lengthLines = [['a', 'length: a.length'], ['b', 'length: b.length']];
    const markedNodeLines = async () => (await markedLines(graph)).filter(([kind]) => kind !== 'edge');
    assert.deepEqual(await markedNodeLines(), lengthLines);
    assert.deepEqual((await graph.locator('g.highlighted .main-label-tspan').allTextContents())
      .filter(name => ['a', 'b', 'c'].includes(name)).sort(), ['a', 'b']);
    await outer.click();
    await graph.hover();
    assert.deepEqual(await markedNodeLines(), lengthLines);
    await heightView.page.getByRole('button', { name: 'Clear pin' }).click();
    assert.equal(await graph.locator('.highlighted, .label-highlight-marker').count(), 0);
    // Fact previews share the graph with core's constraint inspector.
    await graph.evaluate(g => {
      const node = [...g.shadowRoot.querySelectorAll('g.node')].find(n => n.__data__.label === 'a');
      g.highlightNodes([node.__data__.id]);
    });
    await outer.focus();
    await outer.press('Escape');
    assert.deepEqual(await graph.locator('g.highlighted .main-label-tspan').allTextContents(), ['a']);
    assert.deepEqual(heightView.errors, []);
    await heightView.page.close();
    const one = await browserPage(browser, single.props);
    await expandExplorer(one.page, 1);
    await settled(one.page, 1);
    assert.equal(await one.page.getByRole('button', { name: 'Side by side' }).count(), 0);
    await one.page.close();
    const branchPage = await browserPage(browser, branches.props);
    await expandExplorer(branchPage.page, 2);
    await settled(branchPage.page, 2);
    assert.ok(await branchPage.page.getByRole('status').textContent().then(s => s.includes('Independent layout')));
    await branchPage.page.close();
    const linePage = await browserPage(browser, omitted);
    await settled(linePage.page, 1);
    assert.equal(await linePage.page.getByLabel('Spytial inspection explorer').count(), 0);
    assert.match(await linePage.page.getByLabel('Context declarations and facts').innerText(),
      /h : x = 7\s+\(omitted from this inspection\)/);
    await linePage.page.close();

    const fn = await browserPage(browser, functionHeader.props);
    await expandExplorer(fn.page, sites.length);
    await fn.page.getByLabel('Right inspection point').selectOption('1');
    await settled(fn.page, 2);
    assert.match(await fn.page.getByRole('status').innerText(), /Stability hints/);
    assert.deepEqual(fn.errors, []);
    await fn.page.close();

    doc.change(text.replace('After repaint', 'Repainted caption'));
    const [updated] = await doc.widgets(headerLine);
    assert.equal(updated.props.explorer.points.length, 3, 'edits do not accumulate stale points');
    assert.equal(updated.props.explorer.points[2].point.title, 'Repainted caption');
    assert.deepEqual(doc.diagnostics.flatMap(d => d.diagnostics).filter(d => d.severity === 1), []);
    fs.writeFileSync('.lake/explorer-props.json', JSON.stringify(header.props, null, 2));
    console.log('Infoview RPC + Chromium passed: point selection, fact comparisons, context scrolling, keyboard and pinned highlights, native node highlights, edge captions and attribute markers, branch isolation, rollback and edits.');
  } finally { await browser?.close(); doc.close(); }
}

if (process.argv[1] === new URL(import.meta.url).pathname) await main();
