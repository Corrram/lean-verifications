"""Verify every imported manuscript against its pinned original source bytes."""
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parents[1]

def check_sources(root=ROOT):
    count=0
    for manifest in sorted((root/'examples/articles').glob('*/source.json')):
        data=json.loads(manifest.read_text(encoding='utf-8'))
        source=(manifest.parent/'source').resolve()
        for name,checksum in data['files'].items():
            path=(source/name).resolve()
            if not path.is_relative_to(source):raise ValueError('Unsafe original-source path: '+name)
            if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=checksum:
                raise ValueError('Original source changed: '+str(path))
            count+=1
        bibliography=manifest.parent/'bibliography.json'
        if bibliography.exists():
            info=json.loads(bibliography.read_text(encoding='utf-8'))
            output=(manifest.parent/info['generated']).resolve()
            if not output.is_relative_to(manifest.parent.resolve()):raise ValueError('Unsafe bibliography path')
            if hashlib.sha256(output.read_bytes()).hexdigest()!=info['sha256']:raise ValueError('Generated bibliography changed')
    print('Checked',count,'unaltered manuscript source files.')

if __name__=='__main__':check_sources()
