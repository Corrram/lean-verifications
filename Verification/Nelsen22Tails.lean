import Verification.Nelsen22Dependence
import Copula.TailDependence.Derivative

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n22Diagonal (θ t : ℝ) : ℝ :=
  (1-Real.sin (min (2*Real.arcsin (1-t^θ)) (Real.pi/2)))^θ⁻¹

theorem n22Diagonal_deriv_one {θ : ℝ} (hθ : 0 < θ) : HasDerivAt (n22Diagonal θ) 2 1 := by
  have hx : HasDerivAt (fun t : ℝ => 1-t^θ) (-θ) 1 := by
    convert (((hasDerivAt_id (1:ℝ)).rpow_const (p := θ) (Or.inl (by norm_num))).const_sub 1) using 1
    · rfl
    · simp [id_eq]
  have ha : HasDerivAt (fun t : ℝ => Real.arcsin (1-t^θ)) (-θ) 1 := by
    have hh := (Real.hasDerivAt_arcsin (x := 1-(1:ℝ)^θ) (by simp) (by simp)).comp 1 hx
    simpa [Function.comp_def] using hh
  have hb : HasDerivAt (fun t : ℝ => (1-Real.sin (2*Real.arcsin (1-t^θ)))^θ⁻¹) 2 1 := by
    have hh := (((ha.const_mul 2).sin).const_sub 1).rpow_const (p := θ⁻¹) (Or.inl (by simp))
    convert hh using 1
    simp [hθ.ne']
  apply hb.congr_of_eventuallyEq
  have hc := ha.continuousAt.const_mul 2
  have hh : 2*Real.arcsin (1-(1:ℝ)^θ) < Real.pi/2 := by simp; positivity
  filter_upwards [hc (Iio_mem_nhds hh)] with t ht
  exact congrArg (fun z : ℝ => (1-Real.sin z)^θ⁻¹) (min_eq_left ht.le)

theorem nelsen22_upperTail (θ : ℝ) (hθ : θ ∈ Icc 0 1) :
    (nelsen22 θ hθ).HasUpperTailDependence 0 := by
  by_cases hz : θ = 0
  · subst θ; rw [nelsen22_zero]; exact hasUpperTailDependence_independence
  have hp : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hz)
  have he (t : I) : n22Diagonal θ t = (nelsen22 θ hθ).diagonal t := by
    rw [Copula.diagonal,nelsen22_cdf_full hp hθ.2]
    simp only [n22Diagonal,two_mul]
  simpa only [sub_self] using hasUpperTailDependence_of_hasDerivWithinAt he (n22Diagonal_deriv_one hp).hasDerivWithinAt

end Verification
