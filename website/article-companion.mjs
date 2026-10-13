import {createHash} from 'node:crypto';
import {articleBlocks,parseArticle,renderArticle,resolveBindings} from '../.lake/packages/lean-mirror/reader/article.mjs';
import {resolveFigureAssets} from '../.lake/packages/lean-mirror/reader/figures.mjs';
import {escape,proofHTML,formulaProse,validateDocument} from '../.lake/packages/lean-mirror/reader/render.mjs';

const hash=text=>createHash('sha256').update(text).digest('hex');
export function fullArticle({source,bibliography,mapping,evidence,assetBytes}) {
  if(evidence.sourceSha256!==hash(source)||evidence.mapSha256!==hash(mapping))throw new Error('Article source or verification map changed: regenerate the Lean export');
  const config=JSON.parse(mapping);
  for(const [name,checksum] of Object.entries(evidence.assets)) {
    if(!assetBytes[name]||hash(assetBytes[name])!==checksum)throw new Error(`Article asset changed: ${name}`);
  }
  const article=parseArticle(source,bibliography,{referenceChoices:config.referenceChoices});
  const figureAssets=resolveFigureAssets(article,config.figureAssets,evidence.assets);
  const annotations=resolveBindings(article,config.bindings);
  for(const items of Object.values(annotations))for(const item of items) {
    const record=evidence.evidence[item.declaration];
    if(!record||record.declaration!==item.declaration||!record.module||!record.type)throw new Error(`Missing compiled theorem type: ${item.declaration}`);
    if(record.axioms.some(a=>!['propext','Classical.choice','Quot.sound'].includes(a)))throw new Error(`Unsupported article axiom: ${item.declaration}`);
  }
  const blocks=articleBlocks(article);
  for(const [certificate,document] of Object.entries(evidence.documents??{})) {
    if(!['proof','statement'].includes(document.presentation??'proof'))throw new Error('Unknown checked document presentation');
    for(const name of [certificate,document.correspondence,document.verified,document.definitionBridge])if(!evidence.evidence[name])throw new Error(`Missing compiled proof-document evidence: ${name}`);
    validateDocument({schemaVersion:1,definitions:[],results:[{...document,id:'article-proof',certificate}]});
  }
  const statements=blocks.filter(b=>b.isResult);
  const proofPassages=blocks.filter(b=>['paragraph','math'].includes(b.kind)&&blocks.some(parent=>parent.kind==='proof'&&parent.start<=b.start&&parent.end>=b.end));
  return {article,config,annotations,figureAssets,evidence:evidence.evidence,documents:evidence.documents??{},stats:{
    statements:statements.length,linkedStatements:statements.filter(b=>annotations[b.id]?.length).length,
    proofPassages:proofPassages.length,linkedProofPassages:proofPassages.filter(b=>annotations[b.id]?.length).length,
    figures:blocks.filter(b=>b.kind==='figure').length,
    unboundProofPassages:proofPassages.filter(b=>!annotations[b.id]?.length).map(b=>({id:b.id,start:b.start,end:b.end,latex:b.latex})),
  }};
}

export function renderFullArticle(data,{url,api,source,paperUrl}) {
  const route=`lean-mirror/${data.config.id??'blest-spearman'}/`;
  const body=renderArticle(data.article,{
    annotations:data.annotations,evidence:data.evidence,definitions:data.config.definitions,
    sourceURL:data.config.sourceURL??'https://arxiv.org/abs/2609.27634v1',
    sourceDate:data.config.sourceDate??'',
    pageReferences:data.config.pageReferences??{},
    figureURL:image=>url(route+'images/'+data.figureAssets[image].filename),
    certificateURL:record=>api(record.module)+'#'+record.declaration,
    proofDetails:(b,items,m)=>items.filter(item=>data.documents[item.declaration]).map(item=>{
      const document=data.documents[item.declaration],statementOnly=document.presentation==='statement';
      return `<section class="article-checked-calculation"><h4>${escape(document.title)}</h4><p>${statementOnly?'The mathematical statement and its correspondence are checked by Lean.':'Each step below is checked by Lean.'}</p>${document.note?'<p>'+escape(document.note)+'</p>':''}<details><summary>Definitions used in this ${statementOnly?'statement':'calculation'}</summary>${m(document.definition,true)}${data.config.paperId==='Rockel2026ExactBlest'?'<p>The potentials are defined in <a href="#article-eq-potential-A">the original potential equations</a>.</p>':''}</details><p>${formulaProse(document.checked.statement,m)}.</p>${statementOnly?'':proofHTML(document.checked.proof,m)}<p>Statement correspondence: <a href="${escape(api(data.evidence[document.correspondence].module)+'#'+document.correspondence)}">${escape(document.correspondence)}</a></p></section>`;
    }).join('')+(b.labels.includes('cor:nu-rho')?`<p><a href="${url(route+'corollary-3-2/')}">Open the precise proof document, with every intermediate claim checked</a></p>`:''),
  });
  return `<div class="article-reader"><div class="eyebrow"><a href="${url('lean-mirror/')}">LeanMirror</a> / Full article</div>
    <p class="article-status">Full original article · Proof-step verification in progress</p>
    <details class="article-verification-overview"><summary>The original article, with verification links</summary>
      <p>The text, formulas, result numbers, proof order, captions, and bibliography are reproduced from the published source. Click a coefficient or boundary function to reach its definition. Open a verification marker to inspect the exact proposition Lean checked.</p>
      <p>${data.stats.linkedStatements} of ${data.stats.statements} definition and result blocks have compiled counterparts. Individual checks are attached to ${data.stats.linkedProofPassages} of ${data.stats.proofPassages} proof passages. Exhaustive verification of the literal proof steps is still in progress; the entire readable article is not yet certified.</p>
      <p><a href="${paperUrl}">Article verification supplement</a>${data.config.paperId==='Rockel2026ExactBlest'?` · <a href="${url(route+'corollary-3-2/')}">Corollary 3.2: fully checked proof document</a>`:''}</p>
    </details>${(data.config.sourceDiscrepancies??[]).map(d=>`<aside class="article-source-correction"><h2>Printed claim refuted · ${escape(d.version)}</h2><p>${escape(d.unverified_claim)}</p><p>${escape(d.evidence)}</p><p>${escape(d.verified_instead)}</p></aside>`).join('')}${body}
    <section id="article-verification" class="article-verification-overview"><h2>Verification and reproducibility</h2>
      <p>Each displayed theorem type is extracted from a compiled Lean declaration. Its transitive axiom audit rejects unfinished proofs and additional axioms. Linking a source passage to a formal statement remains an explicit mathematical translation, which can be inspected here.</p>
      <p>${data.config.verificationScope}</p>
      <div class="paper-links"><a href="${url(route+'article.leanmirror.json')}">LeanMirror article document</a><a href="${url(route+'original.tex')}">Original LaTeX</a><a href="${url(route+'executable.zip')}">Executable source bundle</a></div>
      <pre><code>python scripts/lean_mirror_article.py --check
python scripts/lean_mirror.py --check</code></pre>
      <p><a href="${source}${data.config.paperId==='Rockel2026ExactBlest'?'examples/paper-bridge':'examples/articles/'+data.config.paperId}/article-map.json">Inspect source-to-proof bindings</a></p>
    </section></div>`;
}
