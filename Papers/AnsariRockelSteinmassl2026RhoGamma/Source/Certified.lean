import Papers.AnsariRockelSteinmassl2026RhoGamma.Source.Proofs
import Proofread.Certify

/-! # The certified article

The kernel checks `certificate`: every compiled claim of `article.tex` holds and
every definition is well defined. `verifiedK : meaningfulK ∧ claimK` is then each
claim, as stated in the text. The command also writes `article.proofread.json`
and `article.proofread.tex`. -/

#proofread_certify Papers.AnsariRockelSteinmassl2026RhoGamma.Source "article.tex" using Papers.AnsariRockelSteinmassl2026RhoGamma.Source.Proofs

open Papers.AnsariRockelSteinmassl2026RhoGamma.Source in
/-- Theorem 1.1, equation (6), as compiled from the article. -/
example : meaningful0 ∧ claim0 := verified0
