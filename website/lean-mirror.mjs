import katex from 'katex';

const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const identifier = /^[a-z][a-z0-9-]*$/;
const declaration = /^[A-Za-z][A-Za-z0-9_.]*$/;

export function validateCompanion(data) {
  if (data.schemaVersion !== 1 || !identifier.test(data.id)) throw new Error('Unsupported LeanMirror companion');
  const keys = data.definitions.map((d) => d.key);
  if (new Set(keys).size !== keys.length || keys.some((k) => !identifier.test(k))) throw new Error('Invalid definition identifiers');
  for (const d of data.definitions) {
    if (d.dependencies.some((k) => !keys.includes(k))) throw new Error(`Missing definition dependency: ${d.key}`);
    if (!d.bridge.startsWith('Foundation:') && !declaration.test(d.bridge)) throw new Error('Invalid definition bridge');
  }
  if (data.statement.kind === 'universal' && !keys.includes(data.statement.domain)) throw new Error('Missing quantified domain');
  if (!['universal', 'formula'].includes(data.statement.kind)) throw new Error('Unsupported statement presentation');
  for (const field of ['target', 'equivalence', 'verified', 'targetModule', 'bridgeModule']) {
    if (!declaration.test(data[field])) throw new Error(`Invalid proof reference: ${field}`);
  }
  return data;
}

export function renderCompanion(data, { url, api, source, mirrorSource, sha }) {
  validateCompanion(data);
  const keys = new Set(data.definitions.map((d) => `#def-${d.key}`));
  const math = (latex, displayMode = false) => {
    // Author notation can link only to this companion's declared definitions.
    for (const [, href] of latex.matchAll(/\\href\{([^}]+)\}/g)) {
      if (!keys.has(href)) throw new Error(`Unknown mathematical definition link: ${href}`);
    }
    return katex.renderToString(latex, {
      displayMode, throwOnError: true, strict: 'error',
      trust: (context) => context.command === '\\href' && keys.has(context.url),
    });
  };
  // The exporter supplies a small prose/math format, never arbitrary HTML or TeX.
  const prose = (latex) => {
    let cursor = 0, html = '';
    for (const match of latex.matchAll(/\$([^$]+)\$|\\\[([\s\S]*?)\\\]/g)) {
      html += esc(latex.slice(cursor, match.index));
      html += math(match[1] ?? match[2], match[2] !== undefined);
      cursor = match.index + match[0].length;
    }
    return html + esc(latex.slice(cursor));
  };
  const proofLink = (name, module = data.bridgeModule) => `<a href="${api(module)}#${esc(name)}"><code>${esc(name)}</code></a>`;
  const statement = data.statement;
  const introduction = statement.kind === 'universal'
    ? `Let ${math(statement.variable)} be a <a class="definition-term" href="#def-${esc(statement.domain)}">${esc(statement.noun)}</a>. Then`
    : '';
  const definitions = data.definitions.map((d) => `<section class="mirror-definition" id="def-${esc(d.key)}" tabindex="-1">
    <h3>${esc(d.title)}</h3><div class="definition-body">${prose(d.latex)}</div>
    ${d.dependencies.length ? `<p class="definition-dependencies">Uses ${[...new Set(d.dependencies)].map((k) => `<a href="#def-${k}">${esc(data.definitions.find((x) => x.key === k).title)}</a>`).join(' · ')}</p>` : ''}
    ${d.bridge.startsWith('Foundation:') ? '<p class="definition-foundation">Declared foundation vocabulary: probability and measure theory.</p>' : `<details><summary>Checked definition correspondence</summary><p>${proofLink(d.bridge)}</p></details>`}
  </section>`).join('');
  return `<article class="prose mirror-companion">
    <div class="eyebrow"><a href="${url('lean-mirror/')}">LeanMirror</a> / Mathematical companion</div>
    <h1>${esc(data.title)}</h1>
    <p class="lead">Read the theorem in familiar notation. Follow a term to its precise definition and inspect the proof of correspondence.</p>
    <section class="mirror-theorem" aria-labelledby="mirror-theorem-title">
      <div class="mirror-theorem-heading"><h2 id="mirror-theorem-title">Theorem</h2><a class="mirror-status" href="#correspondence">Lean-checked correspondence ↗</a></div>
      <p>${introduction}</p>${math(statement.formula, true)}
    </section>
    <p class="mirror-help">Follow the <a href="#def-copula">copula</a>, <a href="#def-nu" aria-label="Definition of Blest’s coefficient nu">${math('\\nu')}</a>, or <a href="#def-rho" aria-label="Definition of Spearman’s rho">${math('\\rho')}</a> to its definition below.</p>
    <p class="mirror-source">Source: <a href="${esc(data.sourceUrl)}">${esc(data.source)}</a>. <a href="${url(`papers/${data.paperId}/`)}">Read the article supplement →</a></p>
    <p class="mirror-scope">${esc(data.scope)}</p>
    <h2 id="definitions">Definitions used in this theorem</h2>
    <p>Only the definitions needed to read the statement, followed through to the declared probability conventions.</p>
    <div class="mirror-definitions">${definitions}</div>
    <section id="correspondence" class="mirror-correspondence">
      <h2>What Lean checks</h2>
      <p>The copula predicate, distribution function, and both coefficient definitions agree with the existing formalization. Lean then checks the equivalence of the companion statement and the existing theorem, and transfers its proof to the companion.</p>
      <dl class="mirror-proof-list">
        <dt>Existing theorem</dt><dd>${proofLink(data.target, data.targetModule)}</dd>
        <dt>Statement equivalence</dt><dd>${proofLink(data.equivalence)}</dd>
        <dt>Proved companion statement</dt><dd>${proofLink(data.verified)}</dd>
      </dl>
      <p>The equivalence proof uses the definition correspondences and conversions between the two presentations of a copula. It does not use the inequality proof itself.</p>
      <details><summary>How the certificate and displayed mathematics are connected</summary>
        <p>The controlled mathematical input produces a typed expression tree. Its interpretation is the proposition checked by Lean; its rendering supplies the formulas on this page. The website build recompiles the proofs and rejects stale presentation data before publication.</p>
        <p>The proof audit permits only <code>${data.allowedAxioms.map(esc).join('</code>, <code>')}</code>. The parser, notation, foundational glossary, and renderers are inspectable software and author-supplied data; their correctness is not itself proved in Lean. Recognizing the intended mathematics in the displayed statement and definitions remains the reader’s judgment.</p>
        <p><a href="${mirrorSource}README.md">Read the language and trust-boundary documentation</a>.</p>
      </details>
      <details><summary>Reproduce this exact snapshot</summary><pre><code>git clone https://github.com/Corrram/lean-verifications.git
cd lean-verifications
git checkout --detach ${esc(sha)}
lake exe cache get
python scripts/lean_mirror.py --check
python scripts/test_lean_mirror.py</code></pre></details>
      <div class="paper-links"><a href="${url(`lean-mirror/${data.id}/companion.tex`)}">Download LaTeX</a><a href="${url(`lean-mirror/${data.id}/companion.json`)}">Presentation data</a><a href="${source}Papers/${data.paperId}/ArticleBridge.lean">Inspect correspondence source ↗</a></div>
    </section>
  </article>`;
}
