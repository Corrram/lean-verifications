// Check generated handbook links, source provenance, and real doc-gen4 output.
import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const out = path.join(root, 'dist');
const base = process.env.SITE_BASE ?? '/lean-verifications/';
const preview = process.argv.includes('--handbook-only');
const walk = (dir) => fs.readdirSync(dir, { withFileTypes: true }).flatMap((e) => e.isDirectory() ? walk(path.join(dir, e.name)) : [path.join(dir, e.name)]);
const pages = walk(out).filter((p) => p.endsWith('.html') && !p.startsWith(path.join(out, 'api') + path.sep));
const errors = [];
for (const file of pages) {
  const html = fs.readFileSync(file, 'utf8');
  assert.match(html, /<title>.+<\/title>/, file);
  assert.match(html, /<html lang="en">/, file);
  assert(!/class="(?:katex-error|texerror)"/.test(html), `TeX error in ${file}`);
  for (const [, raw] of html.matchAll(/(?:href|src)="([^"#]+)(?:#[^"]*)?"/g)) {
    const href = raw.replaceAll('&amp;', '&').split('#')[0].split('?')[0];
    if (!href.startsWith(base)) continue;
    const rel = decodeURIComponent(href.slice(base.length));
    if (preview && rel.startsWith('api/')) continue;
    const target = path.join(out, rel, rel.endsWith('/') || !rel ? 'index.html' : '');
    if (!fs.existsSync(target)) errors.push(`${path.relative(out, file)} → ${href}`);
  }
}
const index = JSON.parse(fs.readFileSync(path.join(out, 'search-index.json')));
const metadata = JSON.parse(fs.readFileSync(path.join(out, 'build-info.json')));
assert.equal(index.filter((x) => x.kind === 'Article supplement').length, metadata.articles.length);
assert.match(metadata.commit, /^[a-f0-9]{40}$/);
if (!preview) {
  const data = JSON.parse(fs.readFileSync(path.join(out, 'api/declarations/declaration-data.bmp')));
  for (const name of ['ProbabilityTheory.Copula', 'ProbabilityTheory.Copula.cdf_one', 'ProbabilityTheory.Copula.cdf_nonneg']) assert(data.declarations[name], `Missing generated declaration: ${name}`);
  for (const article of metadata.articles) for (const module of ['Main', 'Definitions', 'Axioms']) assert(fs.existsSync(path.join(out, 'api/Papers', article.id, `${module}.html`)), `Missing API module: ${article.id}.${module}`);
  assert(fs.readFileSync(path.join(out, 'api/index.html'), 'utf8').includes('Mathematical handbook'), 'API back link missing');
}
assert.equal(errors.length, 0, `Broken local links:\n${errors.join('\n')}`);
console.log(`Checked ${pages.length} handbook pages, ${metadata.articles.length} supplements, local links, search metadata${preview ? ' (handbook preview)' : ', and generated Lean declarations'}.`);
