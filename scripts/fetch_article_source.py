"""Import a pinned arXiv source archive without executing manuscript code.

The exact source files remain unchanged; provenance pins every extracted byte.
Research content belongs here, never in the generic LeanMirror repository.
"""
from __future__ import annotations
import argparse
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import tarfile
import tomllib
import urllib.request

ROOT=Path(__file__).resolve().parents[1]
MAX_ARCHIVE=20*1024*1024
MAX_EXTRACTED=80*1024*1024

def digest(data):return hashlib.sha256(data).hexdigest()

def import_source(paper_id):
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9]+',paper_id):raise ValueError('Invalid paper identifier')
    metadata=tomllib.loads((ROOT/'Papers'/paper_id/'paper.toml').read_text(encoding='utf-8'))
    version=metadata['arxiv']+metadata['arxiv_version']
    if not re.fullmatch(r'\d{4}\.\d{4,5}v\d+',version):raise ValueError('Expected a pinned arXiv version')
    url='https://arxiv.org/src/'+version
    directory=ROOT/'examples/articles'/paper_id
    source=directory/'source'
    archive_path=ROOT/'.lake/article-archives'/f'{version}.tar'
    archive_path.parent.mkdir(parents=True,exist_ok=True)
    if archive_path.exists():raw=archive_path.read_bytes()
    else:
        request=urllib.request.Request(url,headers={'User-Agent':'LeanMirror source importer (author-requested manuscript companion)'})
        with urllib.request.urlopen(request,timeout=60) as response:raw=response.read(MAX_ARCHIVE+1)
        if len(raw)>MAX_ARCHIVE:raise ValueError('Source archive exceeds size limit')
        archive_path.write_bytes(raw)
    extracted={}
    with tarfile.open(fileobj=io.BytesIO(raw),mode='r:*') as archive:
        total=0
        for member in archive.getmembers():
            if member.isdir():continue
            relative=PurePosixPath(member.name)
            if not member.isfile() or relative.is_absolute() or '..' in relative.parts or '\\' in member.name or ':' in member.name:
                raise ValueError('Unsafe archive entry: '+member.name)
            total+=member.size
            if total>MAX_EXTRACTED:raise ValueError('Extracted source exceeds size limit')
            target=(source/relative.as_posix()).resolve()
            if not target.is_relative_to(source.resolve()):raise ValueError('Archive path escaped destination')
            data=archive.extractfile(member).read()
            if target.exists() and target.read_bytes()!=data:raise ValueError('Refusing to replace a changed source: '+member.name)
            target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(data)
            extracted[relative.as_posix()]=digest(data)
    provenance={'schemaVersion':1,'paperId':paper_id,'arxiv':version,'sourceURL':url,
                'archiveSha256':digest(raw),'files':extracted,
                'sourceDiscrepancies':metadata.get('source_discrepancies',[])}
    directory.mkdir(parents=True,exist_ok=True)
    (directory/'source.json').write_text(json.dumps(provenance,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    (source/'LEAN-MIRROR-NOTICE.txt').write_text(
        f"Original article: {metadata['title']}\nAuthors: {', '.join(metadata['authors'])}\n"
        f"Exact source: {url}\n\nImported at the author's request. Manuscript copyright and licensing remain unchanged.\n"
        "The software license does not relicense this article. Source files are unmodified.\n"
        "This import is provenance, not a claim that the original statements or proofs are correct.\n",
        encoding='utf-8')
    print(version,': imported',len(extracted),'source files into',directory)

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paper_id',nargs='+')
    for paper_id in parser.parse_args().paper_id:import_source(paper_id)
