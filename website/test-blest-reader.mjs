import test from 'node:test';
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {fullArticle,renderFullArticle} from './article-companion.mjs';
import {renderBlestReader} from './blest-reader.mjs';
const directory=new URL('../examples/paper-bridge/',import.meta.url);
const read=file=>fs.readFileSync(new URL(file,directory),'utf8');
const evidence=JSON.parse(read('article-evidence.json'));
const data=fullArticle({source:read('source/article.tex'),bibliography:read('source/exact-blest-regions.bbl'),mapping:read('article-map.json'),evidence,
  assetBytes:Object.fromEntries(Object.keys(evidence.assets).map(name=>[name,fs.readFileSync(new URL(name,directory))]))});
const companion=JSON.parse(read('blest-bound.json'));
const options={url:(p='')=>'/'+p,api:m=>'/api/'+m+'.html',source:'https://example.test/',paperUrl:'/paper/'};
const html=renderBlestReader(data,companion,options);

test('reading column retains the complete existing article without rewriting passages',()=>{
  const original=renderFullArticle(data,options).replace('<section class="article-bibliography">','<section class="article-bibliography" id="reader-references">');
  assert(html.includes(`<main id="reader-paper" tabindex="-1">${original}</main>`));
  assert.equal((html.match(/class="article-result"/g)??[]).length,14);
  assert.equal((html.match(/class="article-proof"/g)??[]).length,(read('source/article.tex').match(/\\begin\{proof\}/g)??[]).length);
  assert.equal((html.match(/<figure /g)??[]).length,4);
});

test('side companion uses exported proofs and records the unverified source boundary',()=>{
  assert.match(html,/Statement, definitions &amp; proof checked|Statement, definitions & proof checked/);
  assert.match(html,/not yet been migrated to LeanMirror/);
  assert.match(html,/literal LaTeX source is not yet certified/);
  for(const d of companion.definitions)assert(html.includes(`data-definition="${d.key}"`));
  const metadata=JSON.parse(html.match(/<script id="reader-metadata" type="application\/json">([\s\S]*?)<\/script>/)[1]);
  assert(Object.values(metadata.passages).some(p=>p.corollary&&p.latex.includes('cor:nu-rho')));
  for(const p of Object.values(metadata.passages))assert(read('source/article.tex').includes(p.latex));
});

test('navigation and definition anchors resolve without duplicating source IDs',()=>{
  const ids=[...html.matchAll(/\bid="([^"]+)"/g)].map(m=>m[1]);
  const unique=new Set(ids);
  assert.equal(ids.length,unique.size);
  for(const [,anchor] of html.matchAll(/href="#([^"]+)"/g))assert(unique.has(anchor),`Missing ${anchor}`);
  assert.match(html,/aria-label="Mathematical companion" hidden/);
  assert.match(html,/<noscript>/);
});
