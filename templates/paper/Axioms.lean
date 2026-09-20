import Papers.__PAPER_ID__.Main
import Verification.AxiomAudit

/-!
# Axiom reports for __PAPER_ID__

Add both `#print axioms` and `#assert_standard_axioms` commands for every
fully qualified theorem claimed as verified in COVERAGE.md, one per line.
The full build executes the axiom allowlist checks; scripts/check_verification.py
requires matching coverage, assertion, and report entries.
There are no final declarations to audit in the initial scaffold.
-/
