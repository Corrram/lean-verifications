"""Cross-build evidence order is irrelevant; mathematical content is not."""
import copy
import json
from pathlib import PurePosixPath, PureWindowsPath
import unittest
from lean_mirror_article import canonical_evidence, first_difference


class EvidenceFreshnessTests(unittest.TestCase):
    def test_windows_and_linux_filename_order_have_identical_canonical_exports(self):
        names = ['source/images/figure.png', 'source/LEAN-MIRROR-NOTICE.txt', 'source/article.tex']
        windows = {name: 'unchanged-hash' for name in sorted(names, key=PureWindowsPath)}
        linux = {name: 'unchanged-hash' for name in sorted(names, key=PurePosixPath)}
        self.assertNotEqual(json.dumps(windows), json.dumps(linux))
        self.assertEqual(json.dumps(windows, sort_keys=True), json.dumps(linux, sort_keys=True))

    def test_collection_order_does_not_change_the_export(self):
        windows = {'theorem': {'type': 'P ↔ Q', 'axioms': ['propext', 'Quot.sound'],
                               'dependencies': ['lemmaB', 'lemmaA']}}
        linux = copy.deepcopy(windows)
        linux['theorem']['axioms'].reverse()
        linux['theorem']['dependencies'].reverse()
        self.assertEqual(canonical_evidence(windows), canonical_evidence(linux))

    def test_actual_statement_or_dependency_changes_remain_visible(self):
        saved = {'theorem': {'type': 'P ↔ Q', 'axioms': ['propext'],
                             'dependencies': ['lemmaA']}}
        fresh = copy.deepcopy(saved)
        fresh['theorem']['type'] = 'P → Q'
        self.assertEqual(first_difference(saved, fresh)[0], '$.theorem.type')
        fresh = copy.deepcopy(saved)
        fresh['theorem']['dependencies'].append('extraAxiom')
        self.assertIsNotNone(first_difference(canonical_evidence(saved), canonical_evidence(fresh)))


if __name__ == '__main__':
    unittest.main()
