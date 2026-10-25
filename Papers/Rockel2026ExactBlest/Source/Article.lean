import Papers.Rockel2026ExactBlest.Source.Compiled
import Proofread.Readable
import Proofread.Library.UnitSquareModel

/-! # Readable definitions and claims of the compiled article

Every definition and claim of `article.tex` as an ordinary Lean constant, tied to
the compiled document by kernel-checked `rfl` theorems (`env`, `welldefI`,
`holdsK`). The vocabulary's words (distribution function, probability measure,
uniform marginals) mean what `Proofread.UnitSquare.model` says. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#proofread_semantics Papers.Rockel2026ExactBlest.Source "article.tex" with Proofread.UnitSquare.model
