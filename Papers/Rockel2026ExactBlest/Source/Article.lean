import Papers.Rockel2026ExactBlest.Source.Compiled
import LeanMirror.Tex.Readable

/-! # Readable definitions and claims of the compiled article

Every definition and claim of `article.tex` as an ordinary Lean constant, tied to
the compiled document by kernel-checked `rfl` theorems (`env`, `welldefI`,
`holdsK`). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#mirror_semantics Papers.Rockel2026ExactBlest.Source "article.tex"
