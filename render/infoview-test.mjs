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
    for (let i = 0; i < points.length; i++) {
      const widgets = await doc.widgets(lineOf(['spytial input', 'spytial rotated', 'spytial repaired'][i]));
      assert.equal(widgets.length, 1, 'one ordinary widget at each proof line');
      assert.deepEqual(widgets[0].props, points[i]);
    }
    assert.equal(await doc.source(header, headerLine),
      fs.readFileSync('.lake/build/js/spytialWidget.js', 'utf8'), 'infoview serves current bundle');
    const [single] = await doc.widgets(lineOf('theorem explorerSingle'));
    assert.equal(single.props.explorer.points.length, 1);
    const [branches] = await doc.widgets(lineOf('theorem explorerBranches'));
    assert.equal(branches.props.explorer.points.length, 2);
    assert.notEqual(...branches.props.explorer.points.map(p => p.point.scope));
    const [rollback] = await doc.widgets(lineOf('theorem explorerRollback'));
    assert.deepEqual(rollback.props.explorer.points.map(p => p.point.title), ['Retained']);
    assert.equal((await doc.widgets(lineOf('theorem explorerWithoutInspections'))).length, 0);
    assert.equal((await doc.widgets(lineOf('theorem qualified')))[0].props.explorer.points.length, 1);

    browser = await chromium.launch({ headless: true });
    const { page, errors } = await browserPage(browser, header.props);
    await expandExplorer(page, 3);
    await settled(page, 2);
    assert.deepEqual(errors, [], 'opening the explorer');
    assert.equal(await page.getByLabel('Left inspection point').inputValue(), '0');
    assert.equal(await page.getByLabel('Right inspection point').inputValue(), '2');
    await page.getByLabel('Right inspection point').selectOption('1');
    await settled(page, 2);
    assert.deepEqual(errors, [], 'changing the right inspection');
    await page.getByLabel('Left inspection point').selectOption('2');
    await settled(page, 2);
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
    assert.deepEqual(errors, [], 'switching to stepping');
    await page.getByRole('button', { name: 'Next', exact: true }).click();
    assert.equal(await page.getByLabel('Inspection point', { exact: true }).inputValue(), '1');
    await page.getByRole('button', { name: 'Previous', exact: true }).click();
    assert.equal(await page.getByLabel('Inspection point', { exact: true }).inputValue(), '0');
    await page.getByRole('button', { name: 'All points', exact: true }).click();
    await settled(page, 3);
    assert.equal(await page.getByText('After rotation', { exact: true }).count(), 1);
    assert.equal(await page.getByText('After repaint', { exact: true }).count(), 1);
    assert.deepEqual(errors, []);
    await page.screenshot({ path: '.lake/explorer-all.png', fullPage: true });
    await page.close();
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
    const linePage = await browserPage(browser, points[0]);
    await settled(linePage.page, 1);
    assert.equal(await linePage.page.getByLabel('Theorem inspection explorer').count(), 0);
    await linePage.page.close();

    doc.change(text.replace('After repaint', 'Repainted caption'));
    const [updated] = await doc.widgets(headerLine);
    assert.equal(updated.props.explorer.points.length, 3, 'edits do not accumulate stale points');
    assert.equal(updated.props.explorer.points[2].point.title, 'Repainted caption');
    assert.deepEqual(doc.diagnostics.flatMap(d => d.diagnostics).filter(d => d.severity === 1), []);
    fs.writeFileSync('.lake/explorer-props.json', JSON.stringify(header.props, null, 2));
    console.log('Infoview RPC + Chromium: collapsed theorem disclosure, lazy diagrams, reopen selections, line widgets, captions, comparisons, stepping, all points, single point, branch isolation, rollback and edits passed.');
  } finally { await browser?.close(); doc.close(); }
}

if (process.argv[1] === new URL(import.meta.url).pathname) await main();
