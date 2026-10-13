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
  assert.match(html,/The first rectangle: the printed factorization and sign estimates/);
  assert.match(html,/Each step below is checked by Lean/);
  assert.match(html,/The second rectangle: nonnegativity and its exact equality set/);
  assert.equal(Object.keys(data.documents).length,4);
  assert.match(html,/The third rectangle: decrease in x and the edge minimum/);
  assert.match(html,/The fourth rectangle: increase in z and the edge minimum/);
  // The source proposition excludes w=1. The checked companion keeps that
  // exact range even though the standalone nonnegativity lemmas extend to it.
  for(const document of Object.values(data.documents)) {
    assert.match(data.evidence[document.correspondence].type,/w < 1/);
  }
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
  const badProof=structuredClone(articleEvidence);Object.values(badProof.documents)[0].checked.proof.kind='prose';
  assert.throws(()=>fullArticle({...articleInputs,evidence:badProof}),/proof node/);
  const badBridge=structuredClone(articleEvidence);Object.values(badBridge.documents)[0].correspondence='Missing.bridge';
  assert.throws(()=>fullArticle({...articleInputs,evidence:badBridge}),/Missing compiled proof-document evidence/);
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


test('the Chatterjee–Blest original retains its table, all panels and both explicitly refuted claims',()=>{
  const directory=new URL('../examples/articles/Rockel2026XiBlest/',import.meta.url);
  const read=name=>fs.readFileSync(new URL(name,directory),'utf8');
  const evidence=JSON.parse(read('article-evidence.json'));
  const inputs={source:read('source/xi-nu-region.tex'),bibliography:read('article.bbl'),mapping:read('article-map.json'),evidence,
    assetBytes:Object.fromEntries(Object.keys(evidence.assets).map(name=>[name,fs.readFileSync(new URL(name,directory))]))};
  const data=fullArticle(inputs),html=renderFullArticle(data,{...options,paperUrl:'/paper/'});
  assert.equal(data.stats.statements,13);assert.equal(data.stats.figures,2);
  assert.equal((html.match(/<img /g)??[]).length,4);assert.match(html,/class="article-table"/);
  assert.equal((html.match(/class="article-source-correction"/g)??[]).length,2);
  assert.match(html,/printed_lower_square_polynomial_false/);assert.match(html,/not_comonotonic_concordanceLE_countermonotonic/);
  assert.equal(Object.keys(data.documents).length,1);
  assert.match(html,/Corrected lower-clamped square moment: where the coefficient comes from/);
  assert.match(html,/lower_square_correspondence/);
  assert.match(html,/Definitions used in this calculation/);
  const missingPrimitive=structuredClone(evidence);
  delete missingPrimitive.evidence['Papers.Rockel2026XiBlest.ArticleCalculations.primitive_definition'];
  assert.throws(()=>fullArticle({...inputs,evidence:missingPrimitive}),/Missing compiled/);
  assert.match(inputs.source,/r\^4 - \\frac\{r\^5\}\{5\}/);assert.match(inputs.source,/C_p\\geq_\{co\} C_/);
  assert.equal(data.article.references['eq:xi'].number,'2');assert.equal(data.article.references['eq:nu'].number,'3');
  assert.match(html,/href="#article-eq-xi"/);assert.match(html,/href="#article-eq-nu"/);
  assert.match(html,/entire original proof text is not yet a certified LeanMirror proof document/);
  assert.doesNotMatch(html,/corollary-3-2\//);
});

test('the Chatterjee–Blomqvist reader retains the original title, numbering and scoped statement bridge',()=>{
  const directory=new URL('../examples/articles/OrendayLaresRockel2026XiBeta/',import.meta.url);
  const read=name=>fs.readFileSync(new URL(name,directory),'utf8');
  const evidence=JSON.parse(read('article-evidence.json'));
  const inputs={source:read('source/xi-beta-region.tex'),bibliography:read('source/xi-beta-region.bbl'),mapping:read('article-map.json'),evidence,
    assetBytes:Object.fromEntries(Object.keys(evidence.assets).map(name=>[name,fs.readFileSync(new URL(name,directory))]))};
  const data=fullArticle(inputs),html=renderFullArticle(data,{...options,paperUrl:'/paper/'});
  assert.equal(data.stats.statements,13);assert.equal(data.stats.linkedStatements,13);
  assert.equal(data.stats.figures,3);assert.equal((html.match(/<img /g)||[]).length,3);
  assert.equal(data.article.bibliography.length,30);
  assert.equal(data.article.references['eq:beta-def'].number,'1.2');
  assert.equal(data.article.references['eq:si-ineq'].number,'1.5');
  assert.equal(data.article.references['eq:J'].number,'5.3');
  assert.match(html,/29 September 2026/);
  assert.match(html,/href="#article-eq-beta-def"/);
  for(const label of ['tent','Lb','Ab'])assert.match(html,new RegExp('href="#article-eq-'+label+'"'));
  assert.equal(Object.keys(data.documents).length,2);
  for(const document of Object.values(data.documents))assert.equal(document.presentation,'statement');
  assert.match(html,/The mathematical statement and its correspondence are checked by Lean/);
  assert.match(html,/Definitions used in this statement/);
  assert.match(html,/lower_bound_correspondence/);assert.match(html,/beta_definition/);
  assert.match(html,/exact_region_correspondence/);assert.match(html,/region_definition/);
  assert.match(html,/Exact region: checked mathematical statement/);
  assert.match(html,/does not certify the article&#39;s printed variational proof/);
  const missingRegionDefinition=structuredClone(evidence);
  delete missingRegionDefinition.evidence['Papers.OrendayLaresRockel2026XiBeta.ArticleDefinitions.region_definition'];
  assert.throws(()=>fullArticle({...inputs,evidence:missingRegionDefinition}),/Missing compiled/);
  assert.match(html,/one-step statement proof reuses the existing compiled lower-bound theorem/);
  assert.match(html,/does not certify the article&#39;s printed proof of Proposition 4.1/);
  assert.match(html,/full definition bridge for the convex-function\/slope-data formulation/);
  assert.equal((html.match(/class="article-proof"/g)||[]).length,(inputs.source.match(/\\begin\{proof\}/g)||[]).length);
});
