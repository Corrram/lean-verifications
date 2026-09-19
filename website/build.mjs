import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFileSync } from 'node:child_process';
import MarkdownIt from 'markdown-it';
import texmath from 'markdown-it-texmath';
import katex from 'katex';
import { parse } from 'smol-toml';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, '..');
const out = path.join(root, 'dist');
const base = process.env.SITE_BASE ?? '/lean-verifications/';
if (!/^\/(?:[\w-]+\/)*$/.test(base)) throw new Error('SITE_BASE must be an absolute directory path');
const sha = process.env.SOURCE_SHA || execFileSync('git', ['rev-parse', 'HEAD'], { cwd: root, encoding: 'utf8' }).trim();
if (!/^[a-f0-9]{40}$/.test(sha)) throw new Error('SOURCE_SHA must be a full commit SHA');
const repo = 'https://github.com/Corrram/lean-verifications';
const source = `${repo}/blob/${sha}/`;
const url = (p = '') => base + p;
const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const read = (p) => fs.readFileSync(path.join(root, p), 'utf8');
const write = (p, text) => { const dest = path.join(out, p); fs.mkdirSync(path.dirname(dest), { recursive: true }); fs.writeFileSync(dest, text); };
const md = new MarkdownIt({ html: false, linkify: true }).use(texmath, { engine: katex, delimiters: 'dollars', katexOptions: { throwOnError: true, strict: 'error', trust: false } });
const chapters = [
  ['copulas', 'Copulas & conventions', 'Probability measures, distribution functions, and the basic examples.'],
  ['measures', 'Dependence measures', 'The normalizations and directions behind the rank coefficients.'],
  ['regions', 'Attainable regions', 'Bounds, extremizers, and what an exact region requires.'],
  ['verification', 'Reading a verification', 'Coverage, hypotheses, axiom reports, and reproducible snapshots.'],
];
const papers = fs.readdirSync(path.join(root, 'Papers'), { withFileTypes: true })
  .filter((d) => d.isDirectory() && fs.existsSync(path.join(root, 'Papers', d.name, 'paper.toml')))
  .map((d) => {
    const p = parse(read(`Papers/${d.name}/paper.toml`));
    if (p.id !== d.name || !/^[A-Za-z][A-Za-z0-9]*$/.test(p.id)) throw new Error(`Invalid paper identifier: ${d.name}`);
    if (!['scaffold', 'in-progress', 'complete-for-scope'].includes(p.verification_status)) throw new Error(`Unknown verification status: ${p.id}`);
    return p;
  }).sort((a, b) => (a.arxiv || '').localeCompare(b.arxiv || '') || a.id.localeCompare(b.id));
const status = (p) => ({ scaffold: 'Scaffold', 'in-progress': 'In progress', 'complete-for-scope': 'Complete for stated scope' }[p.verification_status]);
const badge = (p) => `<span class="badge ${p.verification_status}">${esc(status(p))}</span>`;
const api = (module) => url(`api/${module.replaceAll('.', '/')}.html`);
const searchIndex = [];
const nav = (active) => `<aside class="sidebar" id="navigation">
  <a class="brand" href="${url()}"><span class="brand-mark" aria-hidden="true">∂</span><span>lean-verifications<small>Mathematical handbook</small></span></a>
  <nav aria-label="Main navigation">
    <a class="nav-home ${active === '' ? 'active' : ''}" ${active === '' ? 'aria-current="page"' : ''} href="${url()}">Overview</a>
    <p class="nav-label">The handbook</p>
    ${chapters.map(([slug, title], i) => `<a class="${active === slug ? 'active' : ''}" ${active === slug ? 'aria-current="page"' : ''} href="${url(`handbook/${slug}/`)}"><span class="nav-number">0${i + 1}</span>${esc(title)}</a>`).join('')}
    <p class="nav-label">The formal library</p>
    <a class="${active === 'papers' || active.startsWith('paper:') ? 'active' : ''}" href="${url('papers/')}">Article supplements <span class="nav-count">${papers.length}</span></a>
    <a href="${url('api/')}" data-api-link>Lean API reference <span aria-hidden="true">↗</span></a>
    <a href="${url('search/')}">Search the collection</a>
    <p class="nav-label">Contribute & reproduce</p>
    <a href="${source}docs/ADDING_A_PAPER.md">Add an article <span aria-hidden="true">↗</span></a>
    <a href="${repo}">Source on GitHub <span aria-hidden="true">↗</span></a>
  </nav>
  <div class="sidebar-foot"><span class="version-dot"></span> Lean ${esc(read('lean-toolchain').trim().split(':v')[1])}<br><span>Open mathematics. Explicit scope.</span></div>
</aside>`;

function page(route, title, body, { active = '', label = 'Handbook', description = title, sourcePath = 'README.md' } = {}) {
  const canonical = `https://corrram.github.io${url(route)}`;
  write(`${route}index.html`, `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>${esc(title)} · lean-verifications</title><meta name="description" content="${esc(description)}">
<link rel="canonical" href="${canonical}"><meta name="theme-color" content="#152d3b">
<link rel="icon" href="${url('assets/favicon.svg')}" type="image/svg+xml">
<link rel="stylesheet" href="${url('assets/katex/katex.min.css')}"><link rel="stylesheet" href="${url('assets/style.css')}">
<script defer src="${url('assets/site.js')}"></script></head>
<body data-base="${base}"><a class="skip-link" href="#main">Skip to content</a>${nav(active)}
<div class="page-shell"><header class="topbar"><button class="menu-toggle" aria-expanded="false" aria-controls="navigation">☰ <span>Menu</span></button><span class="breadcrumb">Research supplements <span>/</span> ${esc(label)}</span><a class="search-link" href="${url('search/')}"><span aria-hidden="true">⌕</span> Search <kbd>/</kbd></a></header>
<main id="main" tabindex="-1">${body}</main>
<footer><span>lean-verifications · Marcus Rockel & collaborators</span><span><a href="${source}${sourcePath}">Page source</a> · <a href="${repo}/tree/${sha}">Snapshot ${sha.slice(0, 7)}</a> · <a href="${source}LICENSE">License</a></span></footer></div>
</body></html>`);
}

function render(text, prefix = '') {
  const tokens = md.parse(text, {});
  const headings = new Map();
  for (let i = 0; i < tokens.length; i++) {
    if (tokens[i].type === 'heading_open') {
      const label = tokens[i + 1].content;
      const slug = label.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-|-$/g, '') || 'section';
      const n = headings.get(slug) || 0; headings.set(slug, n + 1);
      tokens[i].attrSet('id', n ? `${slug}-${n}` : slug);
    }
    for (const child of tokens[i].children || []) {
      if (child.type !== 'link_open') continue;
      const href = child.attrGet('href');
      if (href.startsWith('site:')) child.attrSet('href', url(href.slice(5)));
      else if (prefix && !/^(?:[a-z]+:|\/|#)/i.test(href)) child.attrSet('href', new URL(href, prefix).href);
    }
  }
  const html = md.renderer.render(tokens, md.options, {});
  if (/class="(?:katex-error|texerror)"/.test(html)) throw new Error('Invalid TeX in handbook');
  return html;
}

const paperRows = (items) => items.map((p) => `<article class="paper-row" data-publication="${esc(p.publication_status)}" data-search="${esc(`${p.title} ${p.authors.join(' ')} ${p.id} ${p.arxiv} ${p.doi}`.toLowerCase())}"><div class="paper-year">${esc(p.year)}<small>${p.publication_status === 'published' ? 'Journal article' : 'Preprint'}</small></div><div><h3><a href="${url(`papers/${p.id}/`)}">${esc(p.title)}</a></h3><p>${esc(p.authors.join(' · '))}</p><p class="paper-venue">${esc(p.journal || `arXiv:${p.arxiv}`)}</p></div><div class="paper-status">${badge(p)}<a href="${url(`papers/${p.id}/`)}" aria-label="Read supplement: ${esc(p.title)}">View supplement <span aria-hidden="true">→</span></a></div></article>`).join('');

page('', 'A handbook of copula verification', `
<div class="eyebrow">Mathematics / Lean 4 / Research supplements</div>
<div class="intro-grid"><div><h1>A handbook of<br>copula verification.</h1><p class="lead">From mathematical statements to inspectable proofs. Explore the definitions, follow an article’s verification map, and read the Lean behind it.</p><div class="intro-links"><a class="button" href="${url('handbook/copulas/')}">Start with copulas <span aria-hidden="true">→</span></a><a class="text-link" href="${url('api/')}">Open the Lean reference ↗</a></div></div><aside class="formula-panel"><span class="eyebrow">Two views of the same object</span>${md.render('$$C(u,v)=\u005cmu_C([0,u]\u005ctimes[0,v])$$')}<div class="formula-rule"></div><code>ProbabilityTheory.Copula 2</code><p>A distribution function on the page.<br>A probability measure in Lean.</p><a href="${api('Copula.Basic')}#ProbabilityTheory.Copula">Explore the definition →</a></aside></div>
<div class="collection-summary"><span><strong>${papers.length}</strong> article supplements</span><span><strong>${chapters.length}</strong> handbook chapters</span><span><strong>Lean 4</strong> generated API</span></div>
<div class="scope-note"><span class="note-icon" aria-hidden="true">i</span><div><strong>Verification is recorded result by result.</strong><p>${papers.every((p) => p.verification_status === 'scaffold') ? 'All article supplements are currently scaffolds. No article results have been verified here yet.' : 'Consult each supplement’s coverage map for its verified results and remaining gaps.'} A passing build checks the included code; it does not certify an entire article.</p></div></div>
<section><div class="section-heading"><div><span class="eyebrow">A reading path</span><h2>Understand the mathematics.<br>Then inspect the proof.</h2></div><span class="section-aside">Definitions → conventions → coverage</span></div><div class="chapter-grid">${chapters.map(([slug, title, desc], i) => `<a class="chapter-link" href="${url(`handbook/${slug}/`)}"><span class="chapter-number">0${i + 1}</span><h3>${esc(title)}</h3><p>${esc(desc)}</p><span class="chapter-arrow" aria-hidden="true">↗</span></a>`).join('')}</div></section>
<section><div class="section-heading"><div><span class="eyebrow">The collection</span><h2>Article supplements</h2></div><a class="text-link" href="${url('papers/')}">Browse all ${papers.length} articles →</a></div>${paperRows(papers.slice(0, 3))}</section>
<div class="closing-note"><h2>Built to be checked. Written to be cited.</h2><p>Each article has a permanent folder, a versioned source, and an explicit coverage map. Cite an immutable commit for a publication; use this handbook to explore the current collection.</p><a href="${url('handbook/verification/')}">Reproduce and cite a supplement →</a></div>`, { description: 'A mathematical handbook and automatically generated Lean 4 documentation for copula research supplements.' });

chapters.forEach(([slug, title, description], i) => {
  const text = read(`website/content/${slug}.md`);
  const content = render(text);
  page(`handbook/${slug}/`, title, `<article class="prose"><div class="eyebrow">The handbook / Chapter 0${i + 1}</div><h1>${esc(title)}</h1><p class="lead">${esc(description)}</p><div class="reading-note">Mathematical exposition. Article verification status is recorded separately in the coverage maps.</div>${content}<nav class="chapter-pagination" aria-label="Chapter navigation">${i ? `<a href="${url(`handbook/${chapters[i - 1][0]}/`)}">← ${esc(chapters[i - 1][1])}</a>` : `<a href="${url()}">← Overview</a>`}${i < chapters.length - 1 ? `<a href="${url(`handbook/${chapters[i + 1][0]}/`)}">${esc(chapters[i + 1][1])} →</a>` : `<a href="${url('papers/')}">Article supplements →</a>`}</nav></article>`, { active: slug, description, sourcePath: `website/content/${slug}.md` });
  searchIndex.push({ title, kind: 'Handbook', url: url(`handbook/${slug}/`), text: text.replace(/[#*`$]/g, ' ') });
});

page('papers/', 'Article supplements', `<div class="eyebrow">The collection</div><h1>Article supplements</h1><p class="lead">One stable home for each article’s definitions, proofs, bibliography, and verification map.</p><div class="catalog-controls"><label>Find an article<input id="paper-filter" type="search" placeholder="Title, author, arXiv ID, or DOI"></label><label>Publication<select id="publication-filter"><option value="all">All publications</option><option value="published">Journal articles</option><option value="preprint">Preprints</option></select></label></div><p class="result-count" id="paper-count" aria-live="polite">${papers.length} articles</p><div id="paper-list">${paperRows(papers)}</div><p id="paper-empty" hidden>No articles match these filters.</p>`, { active: 'papers', label: 'Articles', sourcePath: 'Papers/README.md' });

for (const p of papers) {
  const dir = `Papers/${p.id}/`;
  const coverage = read(dir + p.coverage);
  const arxiv = p.arxiv ? `${p.arxiv}${p.arxiv_version || ''}` : '';
  const bib = read(dir + 'references.bib');
  const links = [p.doi && `<a href="https://doi.org/${esc(p.doi)}">Journal article ↗</a>`, arxiv && `<a href="https://arxiv.org/abs/${esc(arxiv)}">arXiv:${esc(arxiv)} ↗</a>`, `<a href="${repo}/tree/${sha}/${dir}">Source folder ↗</a>`, `<a href="${api(p.entrypoint)}">Lean module ↗</a>`].filter(Boolean).join('');
  page(`papers/${p.id}/`, p.title, `<article class="prose paper-detail"><div class="eyebrow">Article supplement / ${esc(p.year)}</div><h1>${esc(p.title)}</h1><p class="authors">${esc(p.authors.join(' · '))}</p><p class="publication">${esc(p.journal || 'arXiv preprint')}${p.doi ? ` · DOI ${esc(p.doi)}` : ''}</p><div class="paper-links">${links}</div><div class="scope-note"><div>${badge(p)}<p>${esc(p.scope)}</p></div></div><dl class="metadata"><div><dt>Stable identifier</dt><dd><code>${esc(p.id)}</code></dd></div><div><dt>Source for numbering</dt><dd>${esc(p.source_for_numbering)}</dd></div><div><dt>Lean entry point</dt><dd><a href="${api(p.entrypoint)}"><code>${esc(p.entrypoint)}</code></a></dd></div></dl><section class="coverage">${render(coverage.replace(/^# Coverage\s*\n/, '## Verification map\n'), source + dir)}</section><h2>Inspect the formalization</h2><div class="module-links">${['Definitions', 'Main', 'Axioms'].map((m) => `<a href="${api(`Papers.${p.id}.${m}`)}">${m}<span>Generated Lean documentation →</span></a>`).join('')}</div><h2>Reproduce this snapshot</h2><p>Run the full project build to check every source file. The pinned toolchain and dependencies live at the repository root.</p><pre><code>git clone ${repo}.git
cd lean-verifications
git checkout --detach ${sha}
lake exe cache get
lake build</code></pre><h2>Cite this supplement</h2><p>Use the <a href="${repo}/tree/${sha}/${dir}">permanent folder at commit ${sha.slice(0, 7)}</a> to identify the exact software snapshot. Cite the original article separately. This handbook follows the latest deployed commit.</p><details><summary>Article bibliography (BibTeX)</summary><pre><code>${esc(bib)}</code></pre></details></article>`, { active: `paper:${p.id}`, label: 'Articles', description: p.scope, sourcePath: dir + 'paper.toml' });
  searchIndex.push({ title: p.title, kind: 'Article supplement', url: url(`papers/${p.id}/`), text: `${p.authors.join(' ')} ${p.id} ${p.doi} ${p.arxiv} ${p.scope} ${coverage}` });
}

page('search/', 'Search the collection', `<div class="eyebrow">Handbook & formal library</div><h1>Search the collection</h1><p class="lead">Find an article, a mathematical concept, or a Lean declaration.</p><form class="search-form" id="collection-search" role="search"><label for="search-query">Search terms</label><div><input id="search-query" name="q" type="search" placeholder="Try copula, xi rho, or cdf_one" autocomplete="off"><button class="button" type="submit">Search</button></div></form><p class="search-status" id="search-status" aria-live="polite">Enter a term to search the handbook and generated Lean reference.</p><div id="search-results"></div><p class="native-search">You can also use <a id="native-search-link" href="${url('api/search.html')}">doc-gen4’s full declaration search →</a></p><noscript><p>Interactive search requires JavaScript. Browse the <a href="${url('papers/')}">article index</a> or <a href="${url('api/')} ">Lean module index</a>.</p></noscript>`, { active: 'search', label: 'Search', sourcePath: 'website/build.mjs' });

page('404/', 'Page not found', `<div class="eyebrow">404</div><h1>This page could not be found.</h1><p class="lead">Return to the handbook or search for the article or declaration.</p><a class="button" href="${url()}">Open the handbook →</a>`, { label: 'Page not found' });
fs.copyFileSync(path.join(out, '404/index.html'), path.join(out, '404.html'));
fs.cpSync(path.join(here, 'assets'), path.join(out, 'assets'), { recursive: true });
fs.cpSync(path.join(here, 'node_modules/katex/dist'), path.join(out, 'assets/katex'), { recursive: true });
write('search-index.json', JSON.stringify(searchIndex));
write('.nojekyll', '');
write('build-info.json', JSON.stringify({ commit: sha, lean: read('lean-toolchain').trim(), docGen4: 'a6521b2d0c93dcdf2d640089f95548df5dd8bf46', articles: papers.map(({ id, verification_status }) => ({ id, verification_status })) }, null, 2));
const docs = path.join(root, 'docbuild/.lake/build/doc');
if (fs.existsSync(path.join(docs, 'index.html'))) {
  fs.cpSync(docs, path.join(out, 'api'), { recursive: true });
  // Native doc-gen4 navigation and search remain intact; add a way back to the handbook.
  const back = `<a class="handbook-return" href="${url()}">← Mathematical handbook</a>`;
  const walk = (dir) => { for (const e of fs.readdirSync(dir, { withFileTypes: true })) { const p = path.join(dir, e.name); if (e.isDirectory()) walk(p); else if (e.name.endsWith('.html')) { const html = fs.readFileSync(p, 'utf8'); fs.writeFileSync(p, html.replace(/<main([^>]*)>/, `<main$1>${back}`).replace('</head>', `<style>.handbook-return{display:block;padding:.65rem 1rem;margin-bottom:1.5rem;background:#152d3b;color:#fff;font:14px system-ui;text-decoration:none}.handbook-return:hover{text-decoration:underline}</style></head>`)); } } };
  walk(path.join(out, 'api'));
} else if (!process.argv.includes('--handbook-only')) {
  throw new Error('doc-gen4 output missing. Run lake build Handbook:docs in docbuild, or use --handbook-only for a content preview.');
}
console.log(`Built ${papers.length} paper pages and ${chapters.length} chapters at ${out} (base ${base}).`);
