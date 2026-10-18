// Build just the Blest reader while other papers are being edited. This uses the
// same renderer as the complete website build and preserves unrelated output.
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {execFileSync} from 'node:child_process';
import {fullArticle} from './article-companion.mjs';
import {renderBlestReader} from './blest-reader.mjs';
import {renderCompanion} from './lean-mirror.mjs';
import {buildCompiledReader} from './compiled-reader.mjs';
const here=path.dirname(fileURLToPath(import.meta.url)),root=path.resolve(here,'..');
const directory=path.join(root,'examples/paper-bridge'),out=path.join(root,'dist');
const read=name=>fs.readFileSync(path.join(directory,name),'utf8');
const evidence=JSON.parse(read('article-evidence.json'));
const data=fullArticle({source:read('source/article.tex'),bibliography:read('source/exact-blest-regions.bbl'),mapping:read('article-map.json'),evidence,
  assetBytes:Object.fromEntries(Object.keys(evidence.assets).map(name=>{
    const file=path.resolve(directory,name);
    if(!file.startsWith(directory+path.sep))throw new Error('Unsafe article asset');
    return [name,fs.readFileSync(file)];
  }))});
const companion=JSON.parse(read('blest-bound.json'));
const base=process.env.SITE_BASE??'/lean-verifications/';
if(!/^\/(?:[\w-]+\/)*$/.test(base))throw new Error('Invalid site base');
const sha=execFileSync('git',['rev-parse','HEAD'],{cwd:root,encoding:'utf8'}).trim();
const url=(p='')=>base+p;
const options={url,api:m=>url(`api/${m.replaceAll('.','/')}.html`),source:`https://github.com/Corrram/lean-verifications/blob/${sha}/`,paperUrl:url(`papers/${companion.paperId}/`),sha,mirrorSource:'https://github.com/Corrram/lean-mirror/'};
const route=`lean-mirror/${companion.id}/`,destination=path.join(out,route);
fs.mkdirSync(destination,{recursive:true});
fs.writeFileSync(path.join(destination,'index.html'),renderBlestReader(data,companion,options));
fs.cpSync(path.join(here,'assets'),path.join(out,'assets'),{recursive:true});
fs.cpSync(path.join(here,'node_modules/katex/dist'),path.join(out,'assets/katex'),{recursive:true});
fs.copyFileSync(path.join(here,'node_modules/katex/LICENSE'),path.join(out,'assets/katex/LICENSE'));
fs.mkdirSync(path.join(destination,'images'),{recursive:true});
for(const figure of Object.values(data.figureAssets))fs.copyFileSync(path.join(directory,figure.rendered),path.join(destination,'images',figure.filename));
for(const [from,to] of [['source/article.tex','original.tex'],['blest-bound.json','companion.json'],['blest-bound.tex','companion.tex'],['source.json','source.json']])fs.copyFileSync(path.join(directory,from),path.join(destination,to));
fs.writeFileSync(path.join(destination,'article.leanmirror.json'),JSON.stringify({...evidence,source:read('source/article.tex'),bibliography:read('source/exact-blest-regions.bbl'),mapping:JSON.parse(read('article-map.json'))},null,2));
fs.mkdirSync(path.join(destination,'corollary-3-2'),{recursive:true});
fs.writeFileSync(path.join(destination,'corollary-3-2/index.html'),`<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Corollary 3.2 · LeanMirror</title><link rel="stylesheet" href="${url('assets/style.css')}"><link rel="stylesheet" href="${url('assets/katex/katex.min.css')}"></head><body><main>${renderCompanion(companion,options)}</main></body></html>`);
await buildCompiledReader({root,out,url,api:options.api,route,evidence});
execFileSync(process.env.PYTHON||'python',['scripts/bundle_lean_mirror.py',path.join(destination,'executable.zip')],{cwd:root,stdio:'inherit'});
console.log(`Built ${destination}`);
console.log(`Original retained: ${data.stats.statements} results, ${data.stats.figures} figures, ${data.article.bibliography.length} references.`);
