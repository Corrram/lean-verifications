import Verification.PlackettLogDensity
import Verification.PlackettDensityNecessity

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem plackettLogScore_monotone {θ u : ℝ} (hθ : θ ∈ Icc 1 2) (hu : u ∈ Icc 0 1) :
    MonotoneOn (plackettLogScore θ u) (Icc 0 1) := by
  have hd (v : ℝ) (hv : v ∈ Icc 0 1) :=
    plackettLogScore_deriv (plackettN_pos hθ.1 hu hv) (plackettD_pos (by linarith [hθ.1]) hu hv)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
  · intro v hv; exact (hd v hv).continuousAt.continuousWithinAt
  · intro v hv; exact (hd v (interior_subset hv)).hasDerivWithinAt
  · intro v hv
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hθ.1)
      (plackettLogPolynomial_nonneg ⟨by linarith [hθ.1],by linarith [hθ.2]⟩ hu (interior_subset hv)))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem plackettDensity_isTP2 {θ : ℝ} (hθ : θ ∈ Icc 1 2) :
    IsTP2 (fun u v : I => plackettDensity θ u v) := by
  intro a b c d hab hcd
  have hd (u : ℝ) (hu : u ∈ Icc 0 1) :
      HasDerivAt (fun x => plackettLogDensity θ x d-plackettLogDensity θ x c)
        (plackettLogScore θ u d-plackettLogScore θ u c) u :=
    (plackettLogDensity_deriv (plackettN_pos hθ.1 hu d.property)
      (plackettD_pos (by linarith [hθ.1]) hu d.property)).sub
    (plackettLogDensity_deriv (plackettN_pos hθ.1 hu c.property)
      (plackettD_pos (by linarith [hθ.1]) hu c.property))
  have hm : MonotoneOn (fun u => plackettLogDensity θ u d-plackettLogDensity θ u c) (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    · intro u hu; exact (hd u hu).continuousAt.continuousWithinAt
    · intro u hu; exact (hd u (interior_subset hu)).hasDerivWithinAt
    · intro u hu
      exact sub_nonneg.mpr (plackettLogScore_monotone hθ (interior_subset hu) c.property d.property hcd)
  have hh := hm a.property b.property hab
  have hi : plackettLogDensity θ a d+plackettLogDensity θ b c ≤
      plackettLogDensity θ a c+plackettLogDensity θ b d := by linarith
  rw [plackettLogDensity_eq hθ.1 a.property d.property,plackettLogDensity_eq hθ.1 b.property c.property,
    plackettLogDensity_eq hθ.1 a.property c.property,plackettLogDensity_eq hθ.1 b.property d.property] at hi
  have he := Real.exp_le_exp.mpr hi
  simpa only [Real.exp_add,Real.exp_log (plackettDensity_pos hθ.1 a.property d.property),
    Real.exp_log (plackettDensity_pos hθ.1 b.property c.property),
    Real.exp_log (plackettDensity_pos hθ.1 a.property c.property),
    Real.exp_log (plackettDensity_pos hθ.1 b.property d.property)] using he

theorem plackett_hasMTP2Density {θ : ℝ} (hθ : 0 < θ) (h : θ ∈ Icc 1 2) :
    (plackett θ hθ).HasMTP2Density := by
  by_cases he : θ=1
  · subst θ; rw [plackett_one]; exact hasMTP2Density_independence 2
  refine ⟨fun x => plackettDensity θ (x 0) (x 1),?_,?_,?_,plackett_toMeasure_density hθ he⟩
  · unfold plackettDensity plackettD plackettA; fun_prop
  · intro x; exact plackettDensity_nonneg hθ (x 0).property (x 1).property
  · exact (isMTP2_fin_two_iff _).mpr (plackettDensity_isTP2 h)

theorem plackett_density_tp2_iff {θ : ℝ} (hθ : 0 < θ) :
    (plackett θ hθ).HasMTP2Density ↔ θ ∈ Icc (1:ℝ) 2 :=
  ⟨plackett_density_tp2_necessary hθ,plackett_hasMTP2Density hθ⟩

end Verification
