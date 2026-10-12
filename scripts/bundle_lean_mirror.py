"""Package the pinned project sources needed to reproduce the paper companion."""
from pathlib import Path
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def bundle(destination):
    destination = Path(destination).resolve()
    destination.relative_to(ROOT / 'dist')
    files = [ROOT / name for name in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
             'Papers.lean', 'Verification.lean', 'LICENSE', 'README.md', 'docs/LEAN_MIRROR.md')]
    for folder in ('Papers', 'Verification', 'scripts', 'examples/paper-bridge'):
        files += [p for p in (ROOT / folder).rglob('*') if p.is_file()
                  and '__pycache__' not in p.parts]
    with zipfile.ZipFile(destination, 'w', compression=zipfile.ZIP_DEFLATED) as archive:
        for p in sorted(set(files)):
            info = zipfile.ZipInfo('lean-verifications/' + p.relative_to(ROOT).as_posix(),
                                   date_time=(2020, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, p.read_bytes())
        info = zipfile.ZipInfo('lean-verifications/READ-ME-FIRST.txt', date_time=(2020, 1, 1, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        archive.writestr(info, (
            'LeanMirror companion to Corollary 3.2 of arXiv:2609.27634v1\n\n'
            'Install Lean using the pinned lean-toolchain, then run:\n'
            '  lake exe cache get\n'
            '  python scripts/lean_mirror.py --check\n'
            '  python scripts/test_lean_mirror.py\n'
            '  python scripts/test_paper_source.py\n\n'
            'Read examples/paper-bridge/blest-bound.tex for the mathematical companion.\n'
            'This bundle contains verification sources, not the website build.\n'
            'The source manuscript and its license notice are in examples/paper-bridge/source/.\n'
        ))


if __name__ == '__main__':
    bundle(sys.argv[1])
