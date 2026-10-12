import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { renderCompanion, validateCompanion } from './lean-mirror.mjs';

const fixture = JSON.parse(fs.readFileSync(new URL('../examples/paper-bridge/blest-bound.json', import.meta.url)));
const options = { url: (p) => '/' + p, api: (m) => '/api/' + m + '.html', source: 'https://example.test/source/', mirrorSource: 'https://example.test/library/', sha: 'a'.repeat(40) };

test('the checked companion renders formulas and local definition links', () => {
  const html = renderCompanion(fixture, options);
  assert(html.includes('class="katex"'));
  for (const key of ['nu', 'rho', 'copula', 'cdf', 'probability']) {
    assert(html.includes(`href="#def-${key}"`));
    assert(html.includes(`id="def-${key}"`));
  }
});

test('missing definition dependencies cannot disappear silently', () => {
  const data = structuredClone(fixture);
  data.definitions = data.definitions.filter((d) => d.key !== 'cdf');
  assert.throws(() => validateCompanion(data), /Missing definition dependency/);
});

test('notation cannot link outside the declared definition closure', () => {
  for (const href of ['#def-invented', 'https://example.test/', 'javascript:alert(1)']) {
    const data = structuredClone(fixture);
    data.statement.formula = `\\href{${href}}{\\nu(C)}`;
    assert.throws(() => renderCompanion(data, options), /Unknown mathematical definition link/);
  }
});

test('invalid notation fails publication instead of rendering a broken formula', () => {
  const data = structuredClone(fixture);
  data.statement.formula = '\\unknownCommand{C}';
  assert.throws(() => renderCompanion(data, options));
});
