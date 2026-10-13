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
  for(const figure of Object.values(data.figureAssets)) {
    assert.match(figure.source,/\.pdf$/);
    assert.match(figure.rendered,/^rendered-figures\/.*\.png$/);
  }
  assert.equal((html.match(/class="article-proof"/g)||[]).length,(articleInputs.source.match(/\\begin\{proof\}/g)||[]).length);
  assert.equal(data.article.bibliography.length,19);
  assert.match(html,/Exchanging the roles of the coordinates handles the fourth rectangle/);
  assert.match(html,/Exhaustive verification of the literal proof steps is still in progress/);
  assert.match(html,/href="#article-eq-eta-def"/);
  assert.match(html,/Corollary 3.2: fully checked proof document/);
  assert.match(html,/The first rectangle: the printed factorization and sign estimates/);
  assert.match(html,/Each step below is checked by Lean/);
  assert.match(html,/The second rectangle: nonnegativity and its exact equality set/);
  assert.equal(Object.keys(data.documents).length,6);
  assert.match(html,/The third rectangle: decrease in x and the edge minimum/);
  assert.match(html,/The fourth rectangle: increase in z and the edge minimum/);
  assert.match(html,/Four rectangles cover the unit square/);
  assert.match(html,/without invoking the native dual inequality/);
  const ns='Papers.Rockel2026ExactBlest.ArticleCalculations.';
  const composition=data.documents[ns+'four_rectangles_valid'].checked.proof,steps=[];
  for(let node=composition;node;node=node.next)steps.push(node.kind);
  assert.deepEqual(steps,['fix','assume','have','have','have','have','finish']);
  const dependencies=data.evidence[ns+'four_rectangles_valid'].dependencies;
  assert(!dependencies.includes('Papers.Rockel2026ExactBlest.paper_dualA'));
  for(const rectangle of ['first','second','third','fourth'])assert(dependencies.includes(ns+rectangle+'_rectangle_verified'));
  assert.match(html,/The exact contact set, including the special horizontal segment/);
  const contact=data.documents[ns+'contact_set_valid'].checked.proof,contactSteps=[];
  for(let node=contact;node;node=node.next)contactSteps.push(node.kind);
  assert.deepEqual(contactSteps,['fix','assume','have','have','have','have','finish']);
  const contactDeps=data.evidence[ns+'contact_set_valid'].dependencies;
  assert(!contactDeps.includes('Papers.Rockel2026ExactBlest.paper_contactA'));
  assert(contactDeps.includes(ns+'second_rectangle_verified'));
  const original='Papers.Rockel2026ExactBlest.ArticleOriginalProof.';
  for(const rectangle of ['first','third','fourth'])assert(contactDeps.includes(original+'graph_'+rectangle+'_contact'));
  // The local proofs use the printed factorizations and strict derivative
  // comparisons; none may quietly invoke the alternative native contact proof.
  for(const name of ['graph_first_contact','graph_third_contact','graph_fourth_contact',
      'graph_third_strict_comparison','graph_fourth_strict_comparison']) {
    const record=data.evidence[original+name];
    assert.match(record.type,/w < 1/);
    assert(!record.dependencies.includes('Papers.Rockel2026ExactBlest.graph_contact_complete'));
    assert(!record.dependencies.includes('Papers.Rockel2026ExactBlest.paper_contactA'));
  }
  assert(data.evidence[original+'graph_third_contact'].dependencies.includes(original+'graph_third_strict_comparison'));
  assert(data.evidence[original+'graph_fourth_contact'].dependencies.includes(original+'graph_fourth_strict_comparison'));
  // The source proposition excludes w=1. The checked companion keeps that
  // exact range even though the standalone nonnegativity lemmas extend to it.
  for(const document of Object.values(data.documents)) {
    const scopedType=document.correspondence===ns+'four_rectangles_correspondence'
      ? data.evidence[ns+'scoped_dualA'].type : document.correspondence===ns+'contact_set_correspondence'
      ? data.evidence['Papers.Rockel2026ExactBlest.paper_contactA'].type : data.evidence[document.correspondence].type;
    assert.match(scopedType,/w < 1/);
  }
});

test('the rho-gamma reader preserves PDF figures and checks the printed optimizer mixture argument',()=>{
  const directory=new URL('../examples/articles/AnsariRockelSteinmassl2026RhoGamma/',import.meta.url);
  const read=name=>fs.readFileSync(new URL(name,directory),'utf8');
  const evidence=JSON.parse(read('article-evidence.json'));
  const inputs={source:read('source/rho-gamma.tex'),bibliography:read('source/rho-gamma.bbl'),mapping:read('article-map.json'),evidence,
    assetBytes:Object.fromEntries(Object.keys(evidence.assets).map(name=>[name,fs.readFileSync(new URL(name,directory))]))};
  const data=fullArticle(inputs),html=renderFullArticle(data,{...options,paperUrl:'/paper/'});
  assert.equal(data.stats.statements,17);assert.equal(data.stats.linkedStatements,17);
  assert.equal(data.stats.figures,2);assert.equal(data.article.bibliography.length,14);
  assert.equal((html.match(/<img /g)||[]).length,2);
  assert.equal((html.match(/class="article-proof"/g)||[]).length,13);
  assert.equal(data.stats.linkedProofPassages,1);
  assert.match(html,/17 September 2026/);assert.match(html,/Steinmaßl/);
  assert.match(html,/href="#article-eq-defs"/);assert.match(html,/href="#article-def-optim-problem"/);
  assert.equal(Object.keys(data.documents).length,2);
  const ns='Papers.AnsariRockelSteinmassl2026RhoGamma.ArticleDefinitions.';
  assert.equal(data.documents[ns+'region_statement_valid'].presentation,'statement');
  const nodes=[];
  for(let node=data.documents[ns+'strict_valid'].checked.proof;node;node=node.next)nodes.push(node);
  assert.deepEqual(nodes.map(n=>n.kind),['fix','fix','assume','choose','have','choose','have','have','have','finish']);
  assert.equal(nodes[3].formula.kind,'and');assert.equal(nodes[5].formula.kind,'and');
  assert.match(html,/Theorem 1.1: the printed strict-monotonicity argument/);
  assert.match(html,/The other main-proof paragraphs are not certified/);
  assert.match(html,/introductory endpoint convention/);
  assert.match(html,/intro_zero_endpoint_incompatible/);
  assert.match(inputs.source,/with \$C_0=M\$ and \$C_\\infty=W\$/);
  assert.match(inputs.source,/setting \$C_0=W\$ and \$C_\\infty=M\$/);
  assert(!data.evidence[ns+'strict_valid'].dependencies.some(n=>n.endsWith('.upperRho_strictMono')));
  assert(!data.evidence[ns+'region_correspondence'].dependencies.some(n=>n.endsWith('.exact_region')));
  for(const figure of Object.values(data.figureAssets)) {
    assert.match(figure.source,/^source\/figures\/.*\.pdf$/);
    assert.match(figure.rendered,/^rendered-figures\/.*\.png$/);
    assert(html.includes('/lean-mirror/rho-gamma/images/'+figure.filename));
  }
  const changedRendering={...inputs.assetBytes};
  changedRendering['rendered-figures/rho_gamma_region.png']=Buffer.from('changed');
  assert.throws(()=>fullArticle({...inputs,assetBytes:changedRendering}),/Article asset changed/);
  for(const certificate of ['gamma_definition','rho_definition','region_correspondence','strict_valid','mixture_definition']){
    const missing=structuredClone(evidence);delete missing.evidence[ns+certificate];
    assert.throws(()=>fullArticle({...inputs,evidence:missing}),/Missing compiled/);
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

test('the Chatterjee–footrule reader retains the original layout and separates statement checks from refutations',()=>{
  const directory=new URL('../examples/articles/Rockel2026XiFootrule/',import.meta.url);
  const read=name=>fs.readFileSync(new URL(name,directory),'utf8');
  const evidence=JSON.parse(read('article-evidence.json'));
  const inputs={source:read('source/xi-footrule-region.tex'),bibliography:read('source/xi-footrule-region.bbl'),mapping:read('article-map.json'),evidence,
    assetBytes:Object.fromEntries(Object.keys(evidence.assets).map(name=>[name,fs.readFileSync(new URL(name,directory))]))};
  const data=fullArticle(inputs),html=renderFullArticle(data,{...options,paperUrl:'/paper/'});
  assert.equal(data.stats.statements,14);assert.equal(data.stats.linkedStatements,11);
  assert.equal(data.stats.figures,3);assert.equal(data.article.bibliography.length,27);
  assert.equal((html.match(/<img /g)||[]).length,9);
  assert.equal((html.match(/class="article-figure-row"/g)||[]).length,4);
  assert.equal((html.match(/class="article-table"/g)||[]).length,2);
  assert.equal((html.match(/class="article-proof"/g)||[]).length,(inputs.source.match(/\\begin\{proof\}/g)||[]).length);
  assert.match(html,/8 September 2025/);
  assert.match(html,/11 of 14 definition and result blocks/);
  assert.match(html,/href="#article-eq-xi-definition"/);assert.match(html,/href="#article-eq-psi-definition"/);
  assert.equal(Object.keys(data.documents).length,2);
  const namespace='Papers.Rockel2026XiFootrule.ArticleDefinitions.';
  assert.equal(data.documents[namespace+'upper_statement_valid'].presentation,'statement');
  assert.match(html,/including both endpoints and uniqueness/);
  assert.match(html,/That printed proof is not certified by this statement check/);
  assert.match(html,/Why the cubic does not have a unique real root/);
  assert.match(html,/Each step below is checked by Lean/);
  assert.equal((html.match(/class="article-source-correction"/g)||[]).length,2);
  assert.match(inputs.source,/the parameter \$\\mu\(y\)\$ is the unique real solution/);
  assert.match(html,/printed_ltd_claim_false/);
  assert.match(html,/footrule_cubic_not_unique_real/);
  assert.match(html,/Appendix Lemmas A.1–A.2/);
  for(const certificate of ['xi_definition','footrule_definition','cubic_counterexample_valid']){
    const missing=structuredClone(evidence);delete missing.evidence[namespace+certificate];
    assert.throws(()=>fullArticle({...inputs,evidence:missing}),/Missing compiled/);
  }
});

test('the joint-region reader checks the printed mixture argument with both endpoint hypotheses',()=>{
  const directory=new URL('../examples/articles/OrendayLaresRockel2026TauFootruleBeta/',import.meta.url);
  const read=name=>fs.readFileSync(new URL(name,directory),'utf8');
  const evidence=JSON.parse(read('article-evidence.json'));
  const inputs={source:read('source/tau-phi-beta-region.tex'),bibliography:read('article.bbl'),mapping:read('article-map.json'),evidence,
    assetBytes:Object.fromEntries(Object.keys(evidence.assets).map(name=>[name,fs.readFileSync(new URL(name,directory))]))};
  const data=fullArticle(inputs),html=renderFullArticle(data,{...options,paperUrl:'/paper/'});
  assert.equal(data.stats.statements,9);assert.equal(data.stats.linkedStatements,9);
  assert.equal(data.stats.figures,3);assert.equal(data.article.bibliography.length,19);
  assert.equal((html.match(/<img /g)||[]).length,3);
  assert.equal((html.match(/class="article-proof"/g)||[]).length,(inputs.source.match(/\\begin\{proof\}/g)||[]).length);
  assert.match(html,/July 2026/);
  assert.match(html,/Theorem 1.1: the exact joint region/);
  assert.match(html,/Filling the vertical fibre: the article&#39;s final mixture argument/);
  assert.match(html,/does not certify the preceding construction of the endpoints/);
  assert.match(html,/two additional source figures remain excluded by the original comment environment/);
  for(const label of ['tau-def','phi-def','beta-def','Q-def','boundary-functions'])assert(html.includes('href="#article-eq-'+label+'"'));
  const namespace='Papers.OrendayLaresRockel2026TauFootruleBeta.ArticleDefinitions.';
  assert.equal(data.documents[namespace+'region_statement_valid'].presentation,'statement');
  const proof=data.documents[namespace+'fibre_valid'].checked.proof,nodes=[];
  for(let node=proof;node;node=node.next)nodes.push(node);
  assert.deepEqual(nodes.map(n=>n.kind),['fix','fix','fix','fix','fix','assume','have','have','have','finish']);
  assert.match(nodes[5].claim,/\\phi\(C\^-\) = p/);
  assert.match(nodes[5].claim,/\\beta\(C\^\+\) = b/);
  assert.equal(nodes[7].formula.kind,'forall');assert.match(nodes[7].claim,/\\mathcal\{Q\}/);
  assert.equal(nodes[8].formula.kind,'exists');assert.equal(nodes[8].formula.type,'[0,1]');
  assert.equal(nodes[9].formula.kind,'exists');assert.equal(nodes[9].formula.type,'\\mathcal{C}');
  for(const certificate of ['q_definition','boundary_definitions','fibre_valid']){
    const missing=structuredClone(evidence);delete missing.evidence[namespace+certificate];
    assert.throws(()=>fullArticle({...inputs,evidence:missing}),/Missing compiled/);
  }
});


test('the xi-rho reader preserves the article and distinguishes a refuted pointwise lemma from its corrected counterpart',()=>{
  const directory=new URL('../examples/articles/AnsariRockel2026XiRho/',import.meta.url);
  const read=name=>fs.readFileSync(new URL(name,directory),'utf8');
  const evidence=JSON.parse(read('article-evidence.json'));
  const inputs={source:read('source/xi-rho-region_arxiv.tex'),bibliography:read('source/xi-rho-region_arxiv.bbl'),mapping:read('article-map.json'),evidence,
    assetBytes:Object.fromEntries(Object.keys(evidence.assets).map(name=>[name,fs.readFileSync(new URL(name,directory))]))};
  const data=fullArticle(inputs),html=renderFullArticle(data,{...options,paperUrl:'/paper/'});
  assert.equal(data.stats.statements,22);assert.equal(data.stats.linkedStatements,15);
  assert.equal(data.stats.figures,5);assert.equal(data.article.bibliography.length,51);
  assert.equal((html.match(/<img /g)||[]).length,11);
  assert.equal((html.match(/class="article-figure-row"/g)||[]).length,7);
  assert.equal((html.match(/class="article-proof"/g)||[]).length,(inputs.source.replace(/(?<!\\)%[^\n]*/g,'').match(/\\begin\{proof\}/g)||[]).length);
  assert.equal((html.match(/<h5/g)||[]).length,3);
  assert.equal(data.config.sourceDate,'2026-05-19');
  assert.match(html,/Printed claim refuted/);assert.match(html,/literal_lemma_refuted/);
  assert.match(inputs.source,/h\(t\)=v\$ for all/);
  assert.match(html,/maximum-principle proof/);
  assert.match(html,/entire preceding optimization problem over arbitrary measurable families/);
  assert.match(html,/Why the equality alternatives in Lemma 8 must hold almost everywhere/);
  for(const label of ['repxicop','frm-rho-integral','eq-b-and-M','eq-C-x','eq-s-v'])assert(html.includes('href="#article-'+label+'"'));
  const ns='Papers.AnsariRockel2026XiRho.ArticleDefinitions.';
  assert.equal(data.documents[ns+'monotone_statement_valid'].presentation,'statement');
  const nodes=[];
  for(let node=data.documents[ns+'endpoint_counterexample_valid'].checked.proof;node;node=node.next)nodes.push(node);
  assert.deepEqual(nodes.map(n=>n.kind),['have','have','have','have','have','finish']);
  assert.equal(nodes[5].formula.kind,'exists');
  assert(data.evidence[ns+'literal_lemma_refuted'].type.includes('¬'));
  // Interpreting the two independently parsed statements must not rely on their truth proofs.
  assert(!data.evidence[ns+'monotone_statement_correspondence'].dependencies.some(n=>n.endsWith('.stochastic_xi_le_abs_rho')||n.endsWith('.stochastic_xi_eq_abs_rho_iff')));
  assert(!data.evidence[ns+'endpoint_counterexample_correspondence'].dependencies.some(n=>n.endsWith('.pointwise_counterexample')));
  const bindings=JSON.parse(inputs.mapping).bindings.filter(b=>b.label==='lem:fanlorentz_ineq');
  assert.deepEqual(bindings.map(b=>b.role??'counterpart'),['refutation','counterpart']);
  for(const certificate of ['xi_definition','rho_definition','sd_definition','literal_lemma_refuted','endpoint_counterexample_valid']){
    const missing=structuredClone(evidence);delete missing.evidence[ns+certificate];
    assert.throws(()=>fullArticle({...inputs,evidence:missing}),/Missing compiled/);
  }
});

test('the rho-footrule reader preserves repeated source labels and checks the printed interpolation argument',()=>{
  const directory=new URL('../examples/articles/AnsariRockel2026RhoFootrule/',import.meta.url);
  const read=name=>fs.readFileSync(new URL(name,directory),'utf8');
  const evidence=JSON.parse(read('article-evidence.json'));
  const inputs={source:read('source/Spearman_arXiv.tex'),bibliography:read('article.bbl'),mapping:read('article-map.json'),evidence,
    assetBytes:Object.fromEntries(Object.keys(evidence.assets).map(name=>[name,fs.readFileSync(new URL(name,directory))]))};
  const data=fullArticle(inputs),html=renderFullArticle(data,{...options,paperUrl:'/paper/'});
  assert.equal(data.stats.statements,40);assert.equal(data.stats.linkedStatements,16);
  assert.equal(data.stats.figures,7);assert.equal(data.article.bibliography.length,37);
  assert.equal((html.match(/<img /g)||[]).length,8);
  assert.equal((html.match(/class="article-proof"/g)||[]).length,23);
  assert.match(html,/20 August 2026/);assert.match(html,/Universität/);assert.match(html,/Straße/);
  assert.match(html,/Source cross-reference notice/);
  assert.deepEqual(data.article.duplicateReferences.map(d=>[d.label,d.choice,d.occurrences.map(o=>o.number)]),
    [['eq:xi-rank-correlation-ratio',2,['7','41']]]);
  for(const n of [1,2])assert(html.includes('id="article-eq-xi-rank-correlation-ratio-occurrence-'+n+'"'));
  assert.match(html,/href="#article-defmaxprob"/);assert.match(html,/href="#article-cor-main"/);
  assert.equal(data.stats.linkedProofPassages,1);
  assert.match(html,/does not certify the preceding construction of the boundary copulas/);
  const ns='Papers.AnsariRockel2026RhoFootrule.ArticleDefinitions.';
  assert.equal(data.documents[ns+'region_statement_valid'].presentation,'statement');
  const nodes=[];
  for(let node=data.documents[ns+'fibre_valid'].checked.proof;node;node=node.next)nodes.push(node);
  assert.deepEqual(nodes.map(n=>n.kind),['fix','fix','fix','fix','assume','have','have','finish']);
  assert.equal(nodes[5].formula.kind,'forall');assert.equal(nodes[6].formula.kind,'exists');
  assert.equal(nodes[7].formula.kind,'exists');assert.equal(nodes[7].formula.type,'\\mathcal{C}');
  for(const certificate of ['region_correspondence','fibre_valid','fibre_correspondence']){
    assert(!data.evidence[ns+certificate].dependencies.some(n=>n.endsWith('.exact_region')||n.endsWith('.fixed_footrule_intermediate')));
  }
  for(const certificate of ['rho_definition','phi_definition','lower_formula','mixture_definition','fibre_valid']){
    const missing=structuredClone(evidence);delete missing.evidence[ns+certificate];
    assert.throws(()=>fullArticle({...inputs,evidence:missing}),/Missing compiled/);
  }
});


test('the approximation article retains its appendix page links and checks the printed finite arguments',()=>{
  const directory=new URL('../examples/articles/Rockel2025Approximation/',import.meta.url);
  const read=name=>fs.readFileSync(new URL(name,directory),'utf8');
  const evidence=JSON.parse(read('article-evidence.json'));
  const inputs={source:read('source/approximating_copulas.tex'),bibliography:read('article.bbl'),mapping:read('article-map.json'),evidence,
    assetBytes:Object.fromEntries(Object.keys(evidence.assets).map(name=>[name,fs.readFileSync(new URL(name,directory))]))};
  const data=fullArticle(inputs),html=renderFullArticle(data,{...options,paperUrl:'/paper/'});
  assert.equal(data.stats.statements,11);assert.equal(data.stats.linkedStatements,10);
  assert.equal(data.stats.figures,9);assert.equal((html.match(/<img /g)||[]).length,15);
  assert.equal(data.article.bibliography.length,32);
  assert.match(html,/25 May 2026/);assert.match(html,/Family-averaged RMSE/);
  assert.match(html,/href="#article-eq-rho-integral"/);assert.match(html,/href="#article-eq-xi"/);
  assert.match(html,/Theorem 4.2: the rectangular checkerboard bound/);
  assert.match(html,/Lemma 5.1: the printed permutation sum proof/);
  assert.match(html,/Theorem 4.5: the printed trace correction bound/);
  assert.match(html,/not certify the printed Karamata proof/);
  assert.match(html,/iid sample with continuous marginal CDFs/);
  assert.match(html,/unit-cost comparison\/arithmetic schedule/);
  for(const [label,page] of Object.entries(data.config.pageReferences)) {
    const ref=data.article.references[label];
    assert(html.includes(`href="#${ref.id}" title="Page in the published PDF">${page}</a>`));
  }
  assert.equal(Object.keys(data.documents).length,4);
  const ns='Papers.Rockel2025Approximation.ArticleDefinitions.';
  const kinds=name=>{const nodes=[];for(let n=data.documents[ns+name].checked.proof;n;n=n.next)nodes.push(n.kind);return nodes;};
  assert.equal(data.documents[ns+'lower_statement_valid'].presentation,'statement');
  assert.deepEqual(kinds('range_valid'),['fix','have','have','have','finish']);
  assert.deepEqual(kinds('trace_valid'),['fix','have','have','have','finish']);
  assert.deepEqual(kinds('permutation_valid'),['fix','have','have','have','have','have','finish']);
  assert(!data.evidence[ns+'lower_correspondence'].dependencies.some(n=>n.endsWith('.checkerboard_xi_le_of_mtp2')));
  assert(!data.evidence[ns+'range_valid'].dependencies.some(n=>n.endsWith('.checkerboardEstimator_mem')));
  assert(!data.evidence[ns+'trace_valid'].dependencies.some(n=>n.endsWith('.checkerboardEstimator_correction_bounds')||n.endsWith('.cellMass_square_bound')));
  for(const name of ['rho_definition','xi_definition','estimator_definition','permutation_valid','trace_valid','range_valid']){
    const missing=structuredClone(evidence);delete missing.evidence[ns+name];
    assert.throws(()=>fullArticle({...inputs,evidence:missing}),/Missing compiled/);
  }
});
