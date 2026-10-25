import Papers.Rockel2026ExactBlest.Source.Steps
import Papers.Rockel2026ExactBlest.Source.CompanionFamilies
import Proofread.Certify

/-! # The certified article

The kernel checks `certificate`: every claim of `article.tex` that has a
justification follows from the premises the text gives it, all definitions are
well defined, and the proof sentences of Corollary 3.2 use only what they cite.
`verifiedK : meaningfulK ∧ claimK` is then each claim, as stated in the text. -/

#proofread_certify Papers.Rockel2026ExactBlest.Source "article.tex" using Papers.Rockel2026ExactBlest.Source.Proofs

open Papers.Rockel2026ExactBlest.Source in
/-- Corollary 3.2, as compiled from the article. -/
example : meaningful14 ∧ claim14 := verified14
