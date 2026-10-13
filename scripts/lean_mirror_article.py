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

BASE_DIRECTORY = ROOT/'examples/paper-bridge'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def index_source(mapping):
    names=sorted({name for b in mapping['bindings'] for name in b['declarations']})
    if any(not re.fullmatch(r'[A-Za-z][A-Za-z0-9_.]*',name) for name in names):
        raise ValueError('Invalid mathematical declaration name')
    paper_id=mapping['paperId']
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9]+',paper_id):raise ValueError('Invalid paper identifier')
    document_namespace=mapping.get('proofDocumentNamespace')
    if document_namespace and not re.fullmatch(r'Papers\.'+re.escape(paper_id)+r'\.[A-Za-z][A-Za-z0-9_.]*',document_namespace):
        raise ValueError('Invalid proof document namespace')
    evidence_module=mapping.get('evidenceModule')
    if evidence_module and not re.fullmatch(r'Papers\.'+re.escape(paper_id)+r'\.[A-Za-z][A-Za-z0-9_.]*',evidence_module):
        raise ValueError('Invalid article evidence module')
    imported_module=evidence_module or document_namespace or f'Papers.{paper_id}.'+('ArticleCalculations' if paper_id=='Rockel2026ExactBlest' else 'Main')
    namespace=f'Papers.{paper_id}.ArticleIndex'
    lines=['import LeanMirror.Article',
           f'import {imported_module}',
           '', '-- Generated registry: each entry extracts and audits an actual theorem.',
           f'namespace {namespace}',
           'open Lean LeanMirror',
           'def evidence : Json := Json.mkObj [']
    lines += [f'  ("{name}", checked_native% {name})'+(',' if i<len(names)-1 else '') for i,name in enumerate(names)]
    lines+= [']', f'end {namespace}', '']
    return '\n'.join(lines)

def export_article(directory,check):
    DIRECTORY=directory
    mapping=json.loads((DIRECTORY/'article-map.json').read_text(encoding='utf-8'))
    namespace=f"Papers.{mapping['paperId']}.ArticleIndex"
    INDEX=ROOT/'Papers'/mapping['paperId']/'ArticleIndex.lean'
    OUT=DIRECTORY/'article-evidence.json'
    index=index_source(mapping)
    if check:
        if not INDEX.exists() or INDEX.read_text(encoding='utf-8')!=index:
            raise SystemExit('Stale article theorem registry. Run python scripts/lean_mirror_article.py')
    else: INDEX.write_text(index,encoding='utf-8',newline='\n')
    subprocess.run([LAKE,'build',namespace],cwd=ROOT,check=True)
    provenance=json.loads((DIRECTORY/'source.json').read_text(encoding='utf-8'))
    source_hash=digest(DIRECTORY/mapping['source'])
    if 'files' in provenance:
        for name,expected in provenance['files'].items():
            path=(DIRECTORY/'source'/name).resolve()
            if not path.is_relative_to((DIRECTORY/'source').resolve()):raise ValueError('Unsafe source path')
            if digest(path)!=expected:raise ValueError('Pinned source changed: '+name)
        if source_hash!=provenance['files'][mapping['source'].removeprefix('source/')]:raise ValueError('Original article changed')
        assets=[DIRECTORY/mapping['bibliography'], *sorted(p for p in (DIRECTORY/'source').rglob('*') if p.is_file())]
    else:
        if source_hash!=provenance['sourceSha256']:raise ValueError('The pinned original article changed')
        assets=[DIRECTORY/mapping['bibliography'], *sorted((DIRECTORY/'source/images').glob('*'))]
    pinned={str(p.relative_to(DIRECTORY)).replace('\\','/'):digest(p) for p in assets}
    with tempfile.TemporaryDirectory(dir=ROOT/'.lake') as temp:
        fresh=Path(temp)/'article.json'
        if mapping['paperId']=='Rockel2026ExactBlest':exporter=ROOT/'scripts/ExportLeanMirrorArticle.lean'
        else:
            exporter=Path(temp)/'Export.lean'
            documents=mapping['proofDocumentNamespace']+'.documents' if mapping.get('proofDocumentNamespace') else 'Lean.Json.mkObj []'
            exporter.write_text(f'import {namespace}\n\ndef main (args : List String) : IO Unit := do\n  let [destination] := args | throw (IO.userError \"expected output path\")\n  IO.FS.writeFile destination ((Lean.Json.mkObj [(\"evidence\", {namespace}.evidence), (\"documents\", {documents})]).pretty ++ \"\\n\")\n',encoding='utf-8')
        subprocess.run([LAKE,'env','lean','--run',str(exporter),str(fresh)],cwd=ROOT,check=True)
        compiled=json.loads(fresh.read_text(encoding='utf-8'))
        evidence=compiled['evidence']
    data={'schemaVersion':1,'paperId':mapping['paperId'],'sourceSha256':source_hash,
          'mapSha256':digest(DIRECTORY/'article-map.json'),'assets':pinned,'evidence':evidence,
          'documents':compiled['documents']}
    generated=json.dumps(data,ensure_ascii=False,indent=2)+'\n'
    if check:
        if not OUT.exists() or OUT.read_text(encoding='utf-8')!=generated:
            raise SystemExit('Stale full article evidence. Run python scripts/lean_mirror_article.py')
        print('Full article evidence and all original assets are fresh.')
    else:
        OUT.write_text(generated,encoding='utf-8',newline='\n')
        print(mapping['paperId']+': exported',len(evidence),'audited theorem statements.')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--paper',help='Export only this paper identifier; default: all authored maps')
    args=parser.parse_args()
    directories=[BASE_DIRECTORY,*sorted(p.parent for p in (ROOT/'examples/articles').glob('*/article-map.json'))]
    if args.paper:
        directories=[d for d in directories if json.loads((d/'article-map.json').read_text(encoding='utf-8'))['paperId']==args.paper]
        if not directories:raise SystemExit('No authored article map for '+args.paper)
    for directory in directories:export_article(directory,args.check)

if __name__=='__main__':main()
