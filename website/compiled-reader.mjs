// The Blest article as LeanMirror compiles it: one source text, rendered with the
// status of every sentence from the kernel-checked certificate
// (Papers/Rockel2026ExactBlest/Source, `article.mirror.json`).
import fs from 'node:fs';
import path from 'node:path';
import {pathToFileURL} from 'node:url';

export async function buildCompiledReader({root, out, url, api, route, evidence}) {
  const reader = path.join(root, '.lake/packages/lean-mirror/reader');
  if (!fs.existsSync(path.join(reader, 'compiled.mjs'))) {
    console.warn('Skipping the compiled-source reader: the pinned lean-mirror has no reader/compiled.mjs');
    return null;
  }
  const load = name => import(pathToFileURL(path.join(reader, name)).href);
  const {parseArticle} = await load('article.mjs');
  const {resolveFigureAssets} = await load('figures.mjs');
  const {renderCompiledReader} = await load('compiled.mjs');
  const dir = path.join(root, 'Papers/Rockel2026ExactBlest/Source');
  const example = path.join(root, 'examples/paper-bridge');
  const source = fs.readFileSync(path.join(dir, 'article.tex'), 'utf8');
  const report = JSON.parse(fs.readFileSync(path.join(dir, 'article.mirror.json'), 'utf8'));
  const bibliography = fs.readFileSync(path.join(example, 'source/exact-blest-regions.bbl'), 'utf8');
  const config = JSON.parse(fs.readFileSync(path.join(example, 'article-map.json'), 'utf8'));
  const figures = resolveFigureAssets(parseArticle(source, bibliography, {referenceChoices: config.referenceChoices}),
    config.figureAssets, evidence.assets);
  const page = route + 'compiled/';
  const html = renderCompiledReader({
    title: 'Blest’s rank correlation, compiled from its source',
    source, bibliography, report, config,
    figureURL: image => url(route + 'images/' + figures[image].filename),
    sourceURL: 'https://arxiv.org/abs/2609.27634v1', sourceDate: config.sourceDate ?? '',
    assets: {icon: url('assets/favicon.svg'), styles: [url('assets/katex/katex.min.css'), url('assets/style.css'), url('assets/lean-mirror-compiled.css')],
      script: url('assets/lean-mirror-compiled.js')},
    links: [{href: url(route), label: 'Article + companion'}, {href: url(page + 'article.tex'), label: 'Compiled source'},
      {href: url(page + 'article.mirror.json'), label: 'Certificate report'}],
    declarationURL: (name, module) => module ? api(module) + '#' + name : null,
    intro: 'This page renders <code>Papers/Rockel2026ExactBlest/Source/article.tex</code>, the text that the Lean kernel compiles. ' +
      'Every symbol it uses is defined earlier in the article. Each marker reports what the certificate checked for its sentence: ' +
      'a green sentence follows in Lean from exactly the results it cites; a blue one is a cited result, proved through the companion development.',
  });
  const destination = path.join(out, page);
  fs.mkdirSync(destination, {recursive: true});
  fs.writeFileSync(path.join(destination, 'index.html'), html);
  fs.copyFileSync(path.join(dir, 'article.tex'), path.join(destination, 'article.tex'));
  fs.copyFileSync(path.join(dir, 'article.mirror.json'), path.join(destination, 'article.mirror.json'));
  fs.mkdirSync(path.join(out, 'assets'), {recursive: true});
  fs.copyFileSync(path.join(reader, 'compiled.css'), path.join(out, 'assets/lean-mirror-compiled.css'));
  fs.copyFileSync(path.join(reader, 'compiled.js'), path.join(out, 'assets/lean-mirror-compiled.js'));
  return {report, page};
}
