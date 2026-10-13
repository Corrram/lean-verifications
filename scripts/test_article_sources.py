"""Exercise source import confinement and preservation using local archives."""
import contextlib
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch
import fetch_article_source as importer
from check_article_sources import check_sources

class OriginalSourceTests(unittest.TestCase):
    def setUp(self):
        scratch=importer.ROOT/'.lake/source-tests'
        scratch.mkdir(parents=True,exist_ok=True)
        self.temporary=tempfile.TemporaryDirectory(dir=scratch)
        self.root=Path(self.temporary.name)
        metadata=self.root/'Papers/Example'
        metadata.mkdir(parents=True)
        (metadata/'paper.toml').write_text('title="Example"\nauthors=["Author"]\narxiv="2603.09768"\narxiv_version="v1"\n',encoding='utf-8')
        self.archive=self.root/'.lake/article-archives/2603.09768v1.tar'
        self.archive.parent.mkdir(parents=True)
    def tearDown(self):self.temporary.cleanup()
    def archive_member(self,name,contents=b'original theorem',symlink=False):
        with tarfile.open(self.archive,'w') as archive:
            member=tarfile.TarInfo(name)
            if symlink:member.type=tarfile.SYMTYPE;member.linkname='../outside'
            else:member.size=len(contents)
            archive.addfile(member,None if symlink else io.BytesIO(contents))
    def import_source(self):
        with patch.object(importer,'ROOT',self.root),contextlib.redirect_stdout(io.StringIO()):
            importer.import_source('Example')
    def test_exact_source_is_idempotent_and_checked(self):
        self.archive_member('article.tex');self.import_source();self.import_source()
        with contextlib.redirect_stdout(io.StringIO()):check_sources(self.root)
        source=self.root/'examples/articles/Example/source/article.tex'
        self.assertEqual(source.read_bytes(),b'original theorem')
        source.write_bytes(b'changed theorem')
        with self.assertRaisesRegex(ValueError,'changed'):check_sources(self.root)
        with self.assertRaisesRegex(ValueError,'changed'):self.import_source()
        self.assertEqual(source.read_bytes(),b'changed theorem')
    def test_paths_and_links_cannot_escape_source_directory(self):
        for name,symlink in [('../escaped.tex',False),('/absolute.tex',False),('C:/absolute.tex',False),('linked.tex',True)]:
            with self.subTest(name=name):
                self.archive_member(name,symlink=symlink)
                with self.assertRaisesRegex(ValueError,'Unsafe'):self.import_source()
        self.assertFalse((self.root/'examples/articles/Example/source').exists())
    def test_invalid_paper_identifier_is_rejected(self):
        with self.assertRaisesRegex(ValueError,'identifier'):importer.import_source('../Example')

if __name__=='__main__':unittest.main()
