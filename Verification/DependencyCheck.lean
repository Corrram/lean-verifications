import Copula.CDF

/-!
# Dependency integration check

These examples check that the pinned copula API is usable downstream.
They are infrastructure checks, not formalizations of claims in an article.
-/

open ProbabilityTheory
open scoped unitInterval

namespace Verification

example (C : Copula 2) : C.cdf (fun _ => 1) = 1 := C.cdf_one

example (C : Copula 2) (u : Fin 2 → I) : 0 ≤ C.cdf u := C.cdf_nonneg u

end Verification
