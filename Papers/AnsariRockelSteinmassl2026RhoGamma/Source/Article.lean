import Papers.AnsariRockelSteinmassl2026RhoGamma.Source.Compiled
import Proofread.Readable
import Proofread.Library.UnitSquareModel

/-! # Readable definitions and claims of the compiled article

Spearman's rho, Gini's gamma, the region `Ω_{ρ,γ}`, its upper boundary `ρ̄`
(a maximum), the constants `d_*`, `g_*`, `d_0`, `Δ_0`, `r_0`, `g_0`, and the
claims of Theorem 1.1, Corollary 2.1, Proposition 2.3 and Corollary 2.4, as
Lean constants tied to the compiled document by kernel-checked `rfl` theorems. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#proofread_semantics Papers.AnsariRockelSteinmassl2026RhoGamma.Source "article.tex" with Proofread.UnitSquare.model
