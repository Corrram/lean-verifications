import katex from 'katex';
import {renderFullArticle} from './article-companion.mjs';
import {theoremParagraphs, validateCompanion} from './lean-mirror.mjs';
import {articleBlocks} from './companion/article.mjs';
import {escape, proofHTML} from './companion/render.mjs';

// The reading column is the existing source-faithful article renderer. All new
// mathematics comes from the existing exported companion, never UI copy.
export function renderBlestReader(data, companion, options) {
  validateCompanion(companion);
  const {url, api} = options;
  const route = `lean-mirror/${companion.id}/`;
  const original = renderFullArticle(data, options).replace('<section class="article-bibliography">','<section class="article-bibliography" id="reader-references">');
  const contents = original.match(/<details class="article-contents"><summary>Contents<\/summary><ol>([\s\S]*?)<\/ol><\/details>/)?.[1];
  if (!contents) throw new Error('The original article must supply its contents');
  const keys = new Set(companion.definitions.map(d => `#def-${d.key}`));
  const math = (tex, displayMode = false) => katex.renderToString(tex, {
    displayMode, throwOnError:true, strict:'error', macros:{'\\CC':'\\mathcal{C}'},
    trust: ctx => ctx.command === '\\href' && keys.has(ctx.url),
  });
  const prose = tex => {
    let at=0, html='';
    for (const m of tex.matchAll(/\$([^$]+)\$|\\\[([\s\S]*?)\\\]/g)) {
      html += escape(tex.slice(at,m.index)) + math(m[1]??m[2],m[2]!==undefined);
      at=m.index+m[0].length;
    }
    return html + escape(tex.slice(at));
  };
  const result = companion.document.results[0];
  const definitionModule = d => data.evidence[d.bridge]?.module ??
    (d.bridge.endsWith('.phi_definition')?'Papers.Rockel2026ExactBlest.ArticleCalculus':companion.bridgeModule);
  const definitionTemplates = companion.definitions.map(d => `<template id="def-${escape(d.key)}" data-definition="${escape(d.key)}" data-title="${escape(d.title)}">
    <p class="reader-status">${d.bridge.startsWith('Foundation:')?'Foundation':'Definition correspondence checked'}</p>
    <div class="reader-mathematics">${prose(d.latex)}</div>
    ${d.dependencies.length?`<p class="reader-uses">Uses ${[...new Set(d.dependencies)].map(k=>`<a href="#def-${k}">${escape(companion.definitions.find(x=>x.key===k).title)}</a>`).join(' · ')}</p>`:''}
    <details class="reader-technical"><summary>Lean definition</summary>${d.bridge.startsWith('Foundation:')?`<p>${escape(d.bridge)}</p>`:`<a href="${escape(api(definitionModule(d))+'#'+d.bridge)}">${escape(d.bridge)}</a>`}</details>
  </template>`).join('');
  const passages = Object.fromEntries(articleBlocks(data.article).filter(b=>data.annotations[b.id]?.length).map(b=>[b.id, {
    label:b.isResult?`${b.resultName} ${b.number}`:b.kind==='math'&&b.numbers?.length?`Equation (${b.numbers.join(', ')})`:b.kind==='proof'?'Proof passage':'Article passage',
    latex:b.latex,
    corollary:b.labels.includes('cor:nu-rho'),
  }]));
  const metadata = JSON.stringify({passages, definitions:data.config.definitions,
    definitionKeys:{'article-eq-nu-def':'nu','article-eq-rho-def':'rho','article-eq-Phi-def':'phi'},
  }).replaceAll('<','\\u003c');
  return `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
    <title>${escape(data.article.title)} · LeanMirror</title><meta name="description" content="The original Blest article, with its precise mathematical companion alongside.">
    <link rel="icon" href="${url('assets/favicon.svg')}" type="image/svg+xml">
    <link rel="stylesheet" href="${url('assets/katex/katex.min.css')}"><link rel="stylesheet" href="${url('assets/style.css')}"><link rel="stylesheet" href="${url('assets/blest-reader.css')}">
    <script defer src="${url('assets/blest-reader.js')}"></script></head>
    <body class="blest-reader"><a class="reader-skip" href="#reader-paper">Skip to article</a>
    <header class="reader-bar"><a class="reader-brand" href="${url('lean-mirror/')}"><span aria-hidden="true">L<span class="reader-mark">M</span></span> LeanMirror</a>
      <span class="reader-document-name">Blest’s rank correlation</span><div class="reader-bar-actions"><a href="${url(route+'compiled/')}">Compiled from source</a><a href="https://arxiv.org/pdf/2609.27634v1" target="_blank" rel="noopener">Original PDF ↗</a><button type="button" data-open-scope>Verification</button></div></header>
    <div class="reader-layout">
      <nav class="reader-outline" aria-label="Article contents"><details open><summary>In this article</summary><ol>${contents}</ol><a href="#reader-references">References</a></details>
        <div class="reader-outline-footer"><span>Original · 23 September 2026</span><a href="${url(route+'original.tex')}" download>LaTeX source ↓</a><button type="button" data-open-scope>About this companion</button></div></nav>
      <div class="reader-workspace"><div class="reader-tools"><div class="reader-view-switch" aria-label="Reading view"><button type="button" data-view="article" aria-pressed="true">Article</button><button type="button" data-view="companion" aria-pressed="false">Article + companion</button></div><span class="reader-hint">Select a symbol or a margin marker</span></div>
        <main id="reader-paper" tabindex="-1">${original}</main>
      </div>
      <aside class="reader-inspector" aria-label="Mathematical companion" hidden><header class="reader-inspector-header"><div><span class="reader-kicker">Mathematical companion</span><h2 id="reader-inspector-title">Alongside the article</h2></div><button type="button" class="reader-close" aria-label="Close companion">×</button></header>
        <div class="reader-tabs" role="tablist" aria-label="Companion detail"><button type="button" role="tab" id="reader-math-tab" aria-controls="reader-math-panel" aria-selected="true">Mathematics</button><button type="button" role="tab" id="reader-evidence-tab" aria-controls="reader-evidence-panel" aria-selected="false" tabindex="-1">Lean & source</button></div>
        <div class="reader-inspector-scroll"><section id="reader-math-panel" role="tabpanel" aria-labelledby="reader-math-tab" tabindex="0"></section><section id="reader-evidence-panel" role="tabpanel" aria-labelledby="reader-evidence-tab" tabindex="0" hidden></section></div>
      </aside>
    </div>
    <template id="reader-welcome"><p class="reader-status">Read the paper. Inspect the mathematics.</p><p>The article keeps its original wording, numbering, figures, and proof order. Its companion opens here without replacing the passage you are reading.</p><div class="reader-start-links"><button type="button" data-select="article-eq-nu-def">Blest’s coefficient <span>Definition · Equation (1) →</span></button><button type="button" data-select="article-cor-nu-rho">The sharp deviation bound <span>Corollary 3.2 · Statement and proof →</span></button></div><p class="reader-small">A mathematical counterpart and a proof of the exact source text are different guarantees. The verification view records what is currently available for each passage.</p></template>
    <template id="reader-scope"><p class="reader-status">Current verification scope</p><h3>The complete original article</h3><p>All ${data.stats.statements} labeled results, all proof environments, the four figures, and the bibliography are retained from the pinned LaTeX source.</p><h3>The mathematical companion</h3><p>${data.stats.linkedStatements} results have compiled Lean counterparts. Corollary 3.2 has a checked statement, definitions, and proof document. Six further proof documents cover calculations and equality cases in Proposition 4.3.</p><h3>The exact source text</h3><p>This page shows the original arXiv text; its checks concern the linked Lean propositions and exported mathematical trees. A lightly edited version of the article is compiled from its LaTeX source by LeanMirror: there, every symbol is defined in the text before use, and every sentence of the proof of Corollary 3.2 is derived in Lean from exactly the results it cites. <a href="${url(route+'compiled/')}">Read the compiled article with the status of each sentence</a>.</p><p class="reader-small">Correspondences are inspected passage by passage. Browser typesetting also remains outside the Lean proof.</p><a href="${url(route+'executable.zip')}">Download executable verification sources ↓</a></template>
    <template id="reader-corollary"><p class="reader-status">Statement, definitions & proof checked</p><div class="reader-mathematics">${theoremParagraphs(result.checked.statement,math)}</div>
      <details class="reader-proof-details"><summary>Proof · the paper’s derivative argument</summary><div class="proof-flow">${proofHTML(result.checked.proof,math)}</div></details>
      <details class="reader-wording"><summary>Where the companion is more explicit</summary><ul>${companion.original.provenance.changes.map(s=>`<li>${escape(s)}</li>`).join('')}</ul></details>
      <p class="reader-small">This is the existing checked proof document. Equivalence of the literal LaTeX source is not yet certified.</p></template>
    ${definitionTemplates}<script id="reader-metadata" type="application/json">${metadata}</script>
    <noscript><p class="reader-noscript">The complete article and inline verification details remain available. Enable JavaScript to open the companion beside a passage.</p></noscript></body></html>`;
}
