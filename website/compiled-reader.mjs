// Articles as Proofread compiles them: one source text, rendered with the status
// of every sentence from the kernel-checked certificate
// (Papers/<paper>/Source, `article.proofread.json`).
import fs from 'node:fs';
import path from 'node:path';
import {pathToFileURL} from 'node:url';

/**
 * Build the reader of `Papers/<paperId>/Source/article.tex` at `<route>compiled/`.
 * `example` is the folder with the article's pinned bibliography and figure map
 * (`article-map.json`); `evidence.assets` are the pinned figure renderings.
 */
export async function buildCompiledReader({root, out, url, api, route, evidence, paperId = 'Rockel2026ExactBlest',
    example = 'examples/paper-bridge', bibliography = 'source/exact-blest-regions.bbl',
    title = 'Blest’s rank correlation, compiled from its source', sourceURL = 'https://arxiv.org/abs/2609.27634v1'}) {
  const reader = path.join(root, '.lake/packages/proofread/reader');
  if (!fs.existsSync(path.join(reader, 'reader.mjs'))) {
    console.warn('Skipping the compiled-source reader: the pinned proofread package has no reader/reader.mjs');
    return null;
  }
  const dir = path.join(root, 'Papers', paperId, 'Source');
  const reportPath = path.join(dir, 'article.proofread.json');
  if (!fs.existsSync(reportPath)) {
    console.warn(`Skipping the compiled-source reader of ${paperId}: build Papers.${paperId}.Source.Certified first`);
    return null;
  }
  const load = name => import(pathToFileURL(path.join(reader, name)).href);
  const {parseArticle} = await load('article.mjs');
  const {resolveFigureAssets} = await load('figures.mjs');
  const {renderCompiledReader} = await load('reader.mjs');
  const source = fs.readFileSync(path.join(dir, 'article.tex'), 'utf8');
  const report = JSON.parse(fs.readFileSync(reportPath, 'utf8'));
  const bbl = fs.readFileSync(path.join(root, example, bibliography), 'utf8');
  const config = JSON.parse(fs.readFileSync(path.join(root, example, 'article-map.json'), 'utf8'));
  const figures = resolveFigureAssets(parseArticle(source, bbl, {referenceChoices: config.referenceChoices}),
    config.figureAssets, evidence.assets);
  const page = route + 'compiled/';
  const html = renderCompiledReader({
    title, source, bibliography: bbl, report, config,
    figureURL: image => url(route + 'images/' + figures[image].filename),
    sourceURL, sourceDate: config.sourceDate ?? '',
    assets: {icon: url('assets/favicon.svg'), styles: [url('assets/katex/katex.min.css'), url('assets/style.css'), url('assets/proofread-reader.css')],
      script: url('assets/proofread-reader.js')},
    links: [{href: url(route), label: 'Article + companion'}, {href: url(page + 'article.tex'), label: 'Compiled source'},
      {href: url(page + 'article.proofread.json'), label: 'Certificate report'}],
    declarationURL: (name, module) => module ? api(module) + '#' + name : null,
    intro: `This page renders <code>Papers/${paperId}/Source/article.tex</code>, the text that the Lean kernel compiles. ` +
      'Every symbol it uses is defined earlier in the article. Each marker reports what the certificate checked for its sentence: ' +
      'a green sentence follows in Lean from exactly the results it cites; a blue one is a cited result, proved through the companion development.',
  });
  const destination = path.join(out, page);
  fs.mkdirSync(destination, {recursive: true});
  fs.writeFileSync(path.join(destination, 'index.html'), html);
  fs.copyFileSync(path.join(dir, 'article.tex'), path.join(destination, 'article.tex'));
  fs.copyFileSync(reportPath, path.join(destination, 'article.proofread.json'));
  fs.mkdirSync(path.join(out, 'assets'), {recursive: true});
  fs.copyFileSync(path.join(reader, 'reader.css'), path.join(out, 'assets/proofread-reader.css'));
  fs.copyFileSync(path.join(reader, 'reader.js'), path.join(out, 'assets/proofread-reader.js'));
  return {report, page};
}
