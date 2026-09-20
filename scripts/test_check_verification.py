"""Regression tests for false verification claims; no Lean axioms are introduced."""

from pathlib import Path
import tempfile
import unittest

from check_verification import check


class CoverageChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.paper = self.root / "Papers" / "Example"
        self.paper.mkdir(parents=True)
        self.write("paper.toml", 'id = "Example"\ncoverage = "COVERAGE.md"\n'
                   'verification_status = "in-progress"\n')
        self.write("COVERAGE.md", "| Theorem 1 | `Papers.Example.result` | verified | Full domain |\n")
        self.write("Axioms.lean", "import Papers.Example.Main\nimport Verification.AxiomAudit\n"
                   "#print axioms Papers.Example.result\n"
                   "#assert_standard_axioms Papers.Example.result\n")

    def write(self, name, text):
        (self.paper / name).write_text(text, encoding="utf-8")

    def test_mapped_audited_theorem(self):
        self.assertEqual(check(self.root), ([], 1))

    def test_missing_assertion(self):
        self.write("Axioms.lean", "#print axioms Papers.Example.result\n")
        self.assertTrue(any("missing axiom assertion" in e for e in check(self.root)[0]))

    def test_nested_comment_does_not_count(self):
        self.write("Axioms.lean", "/- outer /- inner -/\n"
                   "#print axioms Papers.Example.result\n"
                   "#assert_standard_axioms Papers.Example.result\n-/\n")
        self.assertEqual(len(check(self.root)[0]), 2)

    def test_exit_cannot_skip_checks(self):
        audit = (self.paper / "Axioms.lean").read_text()
        self.write("Axioms.lean", "#exit\n" + audit)
        self.assertTrue(any("unexpected command" in e for e in check(self.root)[0]))

    def test_empty_progress_claim(self):
        self.write("COVERAGE.md", "| Theorem 1 | — | pending | Needs proof |\n")
        self.assertTrue(any("no verified results" in e for e in check(self.root)[0]))

    def test_incomplete_scope(self):
        self.write("paper.toml", 'id = "Example"\ncoverage = "COVERAGE.md"\n'
                   'verification_status = "complete-for-scope"\n')
        self.write("COVERAGE.md", (self.paper / "COVERAGE.md").read_text() +
                   "| Theorem 2 | — | pending | Needs proof |\n")
        self.assertTrue(any("still has pending rows" in e for e in check(self.root)[0]))

    def test_wrong_supplement(self):
        self.write("COVERAGE.md", "| Theorem 1 | `Papers.Other.result` | verified | Full domain |\n")
        self.assertTrue(any("another supplement" in e for e in check(self.root)[0]))


if __name__ == "__main__":
    unittest.main()
