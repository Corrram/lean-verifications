"""Cross-build evidence order is irrelevant; mathematical content is not."""
import copy
import unittest
from lean_mirror_article import canonical_evidence, first_difference


class EvidenceFreshnessTests(unittest.TestCase):
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
