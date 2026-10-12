import katex from 'katex';
import { formulaProse, proofHTML, sourceHTML, validateDocument } from '../.lake/packages/lean-mirror/reader/render.mjs';

const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const identifier = /^[a-z][a-z0-9-]*$/;
const declaration = /^[A-Za-z][A-Za-z0-9_.]*$/;

// Paragraph breaks change layout only; every conjunct is retained in order.
function theoremParagraphs(f, math) {
  if (f.kind !== 'forall' || f.body.kind !== 'and') return `<p>${formulaProse(f, math)}.</p>`;
  const flatten = node => node.kind === 'and' ? [...flatten(node.left), ...flatten(node.right)] : [node];
  const clauses = flatten(f.body);
  const sentence = items => items.map(item => formulaProse(item, math)).join('; and ');
  return `<p>Every ${math(`${f.binding ?? f.name}\\in ${f.type}`)} satisfies ${sentence(clauses.slice(0,1))}.</p><p>${sentence(clauses.slice(1,3))}.</p><p>Moreover, ${sentence(clauses.slice(3))}.</p>`;
}

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
  if (!data.document?.results?.length || !data.original?.latex) throw new Error('Missing checked proof or original source');
  validateDocument({...data.document, definitions: data.definitions.map(d=>({id:d.key}))});
  const provenance = data.original.provenance;
  if (!/^[a-f0-9]{64}$/.test(provenance.sourceSha256) || !provenance.references) throw new Error('Missing source provenance');
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
      macros: {'\\CC': '\\mathcal{C}'},
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
  const proofLink = (name, module = name.endsWith('.phi_definition') ? 'Papers.Rockel2026ExactBlest.ArticleCalculus' : name.startsWith('Papers.Rockel2026ExactBlest.ArticleProof.') ? 'Papers.Rockel2026ExactBlest.ArticleProof' : data.bridgeModule) => `<a href="${api(module)}#${esc(name)}"><code>${esc(name)}</code></a>`;
  const statement = data.statement;
  // Validate the legacy statement certificate too; both views come from Lean.
  math(statement.formula);
  const result = data.document.results[0];
  const original = data.original;
  const definitions = data.definitions.map((d) => `<section class="mirror-definition" id="def-${esc(d.key)}" tabindex="-1">
    <h3>${esc(d.title)}</h3><div class="definition-body">${prose(d.latex)}</div>
    ${d.dependencies.length ? `<p class="definition-dependencies">Uses ${[...new Set(d.dependencies)].map((k) => `<a href="#def-${k}">${esc(data.definitions.find((x) => x.key === k).title)}</a>`).join(' · ')}</p>` : ''}
    ${d.bridge.startsWith('Foundation:') ? `<p class="definition-foundation">${esc(d.bridge)}</p>` : `<details><summary>Checked definition correspondence</summary><p>${proofLink(d.bridge)}</p></details>`}
  </section>`).join('');
  return `<article class="prose mirror-companion">
    <div class="eyebrow"><a href="${url('lean-mirror/')}">LeanMirror</a> / Mathematical companion</div>
    <h1>${esc(data.title)}</h1>
    <p class="lead">The paper’s statement and proof, with each mathematical step checked by Lean.</p>
    <section class="mirror-theorem" aria-labelledby="mirror-theorem-title">
      <div class="mirror-theorem-heading"><h2 id="mirror-theorem-title">Corollary 3.2</h2><a class="mirror-status" href="#checked-proof">Statement and proof checked ↗</a></div>
      ${theoremParagraphs(result.checked.statement, math)}
    </section>
    <p class="mirror-help">Follow the <a href="#def-copula">copula</a>, <a href="#def-nu" aria-label="Definition of Blest’s coefficient nu">${math('\\nu')}</a>, or <a href="#def-rho" aria-label="Definition of Spearman’s rho">${math('\\rho')}</a> to its definition below.</p>
    <p class="mirror-source">Source: <a href="${esc(data.sourceUrl)}">${esc(data.source)}</a>. <a href="${url(`papers/${data.paperId}/`)}">Read the article supplement →</a></p>
    <p class="mirror-scope">${esc(data.scope)}</p>
    <section id="checked-proof" class="mirror-proof-section">
      <h2>The proof, beside the original</h2>
      <p class="mirror-help">The left column is generated from the checked proof tree. Every “then” is a separate obligation. The right column retains the published wording.</p>
      <label class="mirror-controls"><input type="checkbox" id="show-proof-obligations"> Show full logical formulas</label>
      <div class="mirror-comparison">
        <div class="mirror-precise"><div class="column-label">Precise companion · Lean checked</div>
          <div class="proof-flow">${proofHTML(result.checked.proof, math)}<span class="qed">□</span></div>
        </div>
        <aside class="mirror-original"><div class="column-label">Original · Corollary 3.2</div>
          ${sourceHTML(original.latex, math, original.provenance.references)}
          <p class="mirror-help"><a href="${url(`lean-mirror/${data.id}/original.tex`)}">Exact published source</a>, lines ${original.provenance.passages[0].startLine}–${original.provenance.passages[0].endLine}.</p>
        </aside>
      </div>
    </section>
    <h2 id="definitions">Definitions used in this theorem</h2>
    <p>Definitions needed for the statement and its proof. Click any linked symbol above to come here.</p>
    <div class="mirror-definitions">${definitions}</div>
    <section id="correspondence" class="mirror-correspondence">
      <h2>What Lean checks</h2>
      <p>Lean checks the mathematical interpretation of every proof step, the full statement, and the definition correspondences. The proof follows the paper’s derivative argument; its cited region theorem, family values, and survival identities are compiled dependencies.</p>
      <dl class="mirror-proof-list">
        <dt>Every step of the printed argument</dt><dd>${proofLink(result.certificate, 'Papers.Rockel2026ExactBlest.ArticleProof')}</dd>
        <dt>Complete corollary correspondence</dt><dd>${proofLink(result.correspondence, 'Papers.Rockel2026ExactBlest.ArticleProof')}</dd>
        <dt>Complete corollary proved from the proof tree</dt><dd>${proofLink(result.verified, 'Papers.Rockel2026ExactBlest.ArticleProof')}</dd>
        <dt>Existing theorem</dt><dd>${proofLink(data.target, data.targetModule)}</dd>
        <dt>Statement equivalence</dt><dd>${proofLink(data.equivalence)}</dd>
        <dt>Proved companion statement</dt><dd>${proofLink(data.verified)}</dd>
      </dl>
      <p>The earlier inequality bridge uses definition correspondences and conversions between presentations of a copula. The new proof document separately verifies the calculus, attainment, uniqueness and support claims.</p>
      <details><summary>Precision and presentation changes</summary><ul>${original.provenance.changes.map(s=>`<li>${esc(s)}</li>`).join('')}</ul></details>
      <p class="mirror-help">${esc(original.provenance.license)} <a href="${esc(original.provenance.licenseUrl)}">Original article license</a>.</p>
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
      <div class="paper-links"><a href="${url(`lean-mirror/${data.id}/companion.tex`)}">Download LaTeX</a><a href="${url(`lean-mirror/${data.id}/companion.json`)}">Proof document data</a><a href="${url(`lean-mirror/${data.id}/executable.zip`)}">Executable source bundle</a><a href="${source}Papers/${data.paperId}/ArticleProof.lean">Inspect checked proof ↗</a></div>
    </section>
  </article>`;
}
