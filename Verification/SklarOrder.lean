import Copula.Sklar.Continuous
import Copula.Order.Orthant

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem denseRange_cdfUnit_of_continuous (μ : Measure ℝ)
    (hc : Continuous (ProbabilityTheory.cdf μ)) : DenseRange (cdfUnit μ) := by
  have hd : Dense (Ioo (0 : I) 1) := by
    rw [dense_iff_closure_eq,closure_Ioo (zero_ne_one : (0:I)≠1)]
    ext u
    simp [unitInterval.le_one']
  apply hd.mono
  intro u hu
  obtain ⟨x,hx⟩ := exists_cdf_eq_of_continuous μ hc hu.1 hu.2
  exact ⟨x,Subtype.ext hx⟩

theorem sklar_lowerOrthant_of_common_marginals {d : ℕ}
    (μ ν : ProbabilityMeasure (Fin d → ℝ)) (C D : Copula d)
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i)))
    (hm : ∀ i,marginal μ i=marginal ν i)
    (hC : IsSklarCopula μ C) (hD : IsSklarCopula ν D)
    (ho : ∀ x,μ.toMeasure.real (Iic x)≤ν.toMeasure.real (Iic x)) : C.LowerOrthantLE D := by
  have hd : DenseRange (marginalTransform μ) :=
    DenseRange.piMap (fun i => denseRange_cdfUnit_of_continuous (marginal μ i) (hc i))
  have he : marginalTransform μ=marginalTransform ν := by
    funext x i
    exact congrArg (fun m => cdfUnit m (x i)) (hm i)
  intro u
  apply hd.induction_on (p := fun u => C.cdf u≤D.cdf u) u (isClosed_le C.continuous_cdf D.continuous_cdf)
  intro x
  rw [hC x,he,hD x]
  exact ho x

end Verification
