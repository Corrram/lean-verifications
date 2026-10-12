"""The comparison text must be an exact excerpt of the pinned published source."""
import copy
import json
import shutil
import tempfile
import unittest
from pathlib import Path
from lean_mirror import ROOT, engine


class SourceTests(unittest.TestCase):
    def test_source_and_excerpt_are_pinned(self):
        source_dir = ROOT / 'examples/paper-bridge'
        metadata = json.loads((source_dir / 'source.json').read_text(encoding='utf-8'))
        mirror = engine()
        self.assertIn('corollary-3-2', mirror.load_source(source_dir, metadata))
        with tempfile.TemporaryDirectory(dir=ROOT / '.lake') as temp:
            root = Path(temp)
            root.resolve().relative_to((ROOT / '.lake').resolve())
            shutil.copytree(source_dir / 'source', root / 'source')
            excerpt = root / metadata['passages'][0]['file']
            excerpt.write_text(excerpt.read_text(encoding='utf-8').replace('positive', 'negative'), encoding='utf-8')
            with self.assertRaisesRegex(ValueError, 'excerpt changed'):
                mirror.load_source(root, metadata)
            changed = copy.deepcopy(metadata)
            changed['passages'][0]['sha256'] = mirror.digest(excerpt)
            with self.assertRaisesRegex(ValueError, 'no longer matches'):
                mirror.load_source(root, changed)


if __name__ == '__main__':
    unittest.main()
