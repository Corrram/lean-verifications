"""Compile article evidence and export a source-pinned, original-text companion.

An evidence link proves only its extracted proposition. Exhaustive statement and
literal proof-step coverage is measured separately; unbound passages are retained.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path
from lean_mirror import ROOT, LAKE

DIRECTORY = ROOT/'examples/paper-bridge'
INDEX = ROOT/'Papers/Rockel2026ExactBlest/ArticleIndex.lean'
OUT = DIRECTORY/'article-evidence.json'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def index_source(mapping):
    names=sorted({name for b in mapping['bindings'] for name in b['declarations']})
    if any(not re.fullmatch(r'[A-Za-z][A-Za-z0-9_.]*',name) for name in names):
        raise ValueError('Invalid mathematical declaration name')
    lines=['import LeanMirror.Article',
           'import Papers.Rockel2026ExactBlest.ArticleOriginalProof',
           '', '-- Generated registry: each entry extracts and audits an actual theorem.',
           'namespace Papers.Rockel2026ExactBlest.ArticleIndex',
           'open Lean LeanMirror',
           'def evidence : Json := Json.mkObj [']
    lines += [f'  ("{name}", checked_native% {name})'+(',' if i<len(names)-1 else '') for i,name in enumerate(names)]
    lines+= [']', 'end Papers.Rockel2026ExactBlest.ArticleIndex', '']
    return '\n'.join(lines)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    mapping=json.loads((DIRECTORY/'article-map.json').read_text(encoding='utf-8'))
    index=index_source(mapping)
    if args.check:
        if not INDEX.exists() or INDEX.read_text(encoding='utf-8')!=index:
            raise SystemExit('Stale article theorem registry. Run python scripts/lean_mirror_article.py')
    else: INDEX.write_text(index,encoding='utf-8',newline='\n')
    subprocess.run([LAKE,'build','Papers.Rockel2026ExactBlest.ArticleIndex'],cwd=ROOT,check=True)
    provenance=json.loads((DIRECTORY/'source.json').read_text(encoding='utf-8'))
    if digest(DIRECTORY/mapping['source'])!=provenance['sourceSha256']:
        raise ValueError('The pinned original article changed')
    assets=[DIRECTORY/mapping['bibliography'], *sorted((DIRECTORY/'source/images').glob('*'))]
    pinned={str(p.relative_to(DIRECTORY)).replace('\\','/'):digest(p) for p in assets}
    with tempfile.TemporaryDirectory(dir=ROOT/'.lake') as temp:
        fresh=Path(temp)/'article.json'
        subprocess.run([LAKE,'env','lean','--run','scripts/ExportLeanMirrorArticle.lean',str(fresh)],cwd=ROOT,check=True)
        evidence=json.loads(fresh.read_text(encoding='utf-8'))
    data={'schemaVersion':1,'paperId':mapping['paperId'],'sourceSha256':provenance['sourceSha256'],
          'mapSha256':digest(DIRECTORY/'article-map.json'),'assets':pinned,'evidence':evidence}
    generated=json.dumps(data,ensure_ascii=False,indent=2)+'\n'
    if args.check:
        if not OUT.exists() or OUT.read_text(encoding='utf-8')!=generated:
            raise SystemExit('Stale full article evidence. Run python scripts/lean_mirror_article.py')
        print('Full article evidence and all original assets are fresh.')
    else:
        OUT.write_text(generated,encoding='utf-8',newline='\n')
        print('Exported',len(evidence),'audited theorem statements for the full article.')

if __name__=='__main__':main()
