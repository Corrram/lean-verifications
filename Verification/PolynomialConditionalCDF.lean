import Copula.Rank.ConditionalDerivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open MeasureTheory ProbabilityTheory Polynomial Set Filter
open scoped unitInterval Topology

namespace Verification

/-- An actual polynomial CDF section identifies the conditional CDF almost everywhere. -/
theorem conditionalCDF_polynomial (C : Copula 2) (v : I) (p : ℝ[X])
    (hp : ∀ u : I, p.eval (u : ℝ) = C.cdf ![u,v]) :
    (fun u : I => C.conditionalCDF u v) =ᵐ[volume]
      fun u : I => p.derivative.eval (u : ℝ) := by
  filter_upwards [C.conditionalCDF_eq_deriv v, Measure.ae_ne volume (0 : I),
    Measure.ae_ne volume (1 : I)] with u hu hu0 hu1
  rw [hu]
  have h0 : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have h1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h))
  have he : Copula.cdfSection C v =ᶠ[𝓝 (u : ℝ)] (fun x => p.eval x) := by
    filter_upwards [Ioo_mem_nhds h0 h1] with x hx
    have h := hp ⟨x,hx.1.le,hx.2.le⟩
    simpa only [Copula.cdfSection,projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩] using h.symm
  exact ((p.hasDerivAt (u : ℝ)).congr_of_eventuallyEq he).deriv

end Verification
