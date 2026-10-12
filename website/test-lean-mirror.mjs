import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import { renderCompanion, validateCompanion } from './lean-mirror.mjs';
import {fullArticle,renderFullArticle} from './article-companion.mjs';

const fixture = JSON.parse(fs.readFileSync(new URL('../examples/paper-bridge/blest-bound.json', import.meta.url)));
const options = { url: (p) => '/' + p, api: (m) => '/api/' + m + '.html', source: 'https://example.test/source/', mirrorSource: 'https://example.test/library/', sha: 'a'.repeat(40) };
const articleRoot=new URL('../examples/paper-bridge/',import.meta.url);
const articleRead=p=>fs.readFileSync(new URL(p,articleRoot),'utf8');
const articleEvidence=JSON.parse(articleRead('article-evidence.json'));
const articleInputs={source:articleRead('source/article.tex'),bibliography:articleRead('source/exact-blest-regions.bbl'),
  mapping:articleRead('article-map.json'),evidence:articleEvidence,
  assetBytes:Object.fromEntries(Object.keys(articleEvidence.assets).map(p=>[p,fs.readFileSync(new URL(p,articleRoot))]))};

test('the full original article retains all results, proof environments, figures and references',()=>{
  const data=fullArticle(articleInputs),html=renderFullArticle(data,{...options,paperUrl:'/paper/'});
  assert.equal(data.stats.statements,14);
  assert.equal(data.stats.linkedStatements,14);
  assert.equal(data.stats.figures,4);
  assert.equal((html.match(/class="article-proof"/g)||[]).length,(articleInputs.source.match(/\\begin\{proof\}/g)||[]).length);
  assert.equal(data.article.bibliography.length,19);
  assert.match(html,/Exchanging the roles of the coordinates handles the fourth rectangle/);
  assert.match(html,/Exhaustive verification of the literal proof steps is still in progress/);
  assert.match(html,/href="#article-eq-eta-def"/);
  assert.match(html,/Corollary 3.2: fully checked proof document/);
});

test('changed source, source maps, figures and theorem evidence cannot pass publication',()=>{
  assert.throws(()=>fullArticle({...articleInputs,source:articleInputs.source+'\n'}),/source or verification map changed/);
  assert.throws(()=>fullArticle({...articleInputs,mapping:articleInputs.mapping+'\n'}),/source or verification map changed/);
  const changedAssets={...articleInputs.assetBytes,'source/images/eta_nu_extremizers.png':Buffer.from('changed')};
  assert.throws(()=>fullArticle({...articleInputs,assetBytes:changedAssets}),/asset changed/);
  const missing=structuredClone(articleEvidence);delete missing.evidence[Object.keys(missing.evidence)[0]];
  assert.throws(()=>fullArticle({...articleInputs,evidence:missing}),/Missing compiled theorem type/);
  const tainted=structuredClone(articleEvidence);Object.values(tainted.evidence)[0].axioms.push('sorryAx');
  assert.throws(()=>fullArticle({...articleInputs,evidence:tainted}),/Unsupported article axiom/);
});

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

test('the complete proof, equality cases, source and executable download are present', () => {
  const html = renderCompanion(fixture, options);
  assert.match(html, /Every step of the printed argument/);
  assert.match(html, /Original · Corollary 3.2/);
  assert.match(html, /maximum/);
  assert.match(html, /minimum/);
  assert.match(html, /executable.zip/);
  for (const key of ['phi','extremizer','survival','tent','vee','calculus']) {
    assert(html.includes(`id="def-${key}"`));
  }
  assert.equal((html.match(/Exact obligation/g) || []).length, 15);
});

test('unverified proof nodes and unresolved source citations fail publication', () => {
  const changed = structuredClone(fixture);
  changed.document.results[0].checked.proof.kind = 'prose';
  assert.throws(() => renderCompanion(changed, options), /proof node/);
  const citation = structuredClone(fixture);
  delete citation.original.provenance.references['thm:rho-nu'];
  assert.throws(() => renderCompanion(citation, options), /Unknown source reference/);
});
