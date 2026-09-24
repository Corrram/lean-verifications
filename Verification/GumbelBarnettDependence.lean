import Verification.GumbelBarnett
import Verification.SchurOrthantEquivalence
import Copula.Dependence.DensityTotalPositivity
import Copula.TailDependence.Quadrant
import Copula.Order.SymmetricSchur
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open ProbabilityTheory MeasureTheory Set Filter
open scoped unitInterval Topology

namespace Verification

theorem gumbelBarnett_cdf_power (θ u v : I) :
    (gumbelBarnett θ).cdf ![u,v] = (v:ℝ) * (u:ℝ)^(1-(θ:ℝ)*Real.log (v:ℝ)) := by
  have hp : 1 ≤ 1-(θ:ℝ)*Real.log (v:ℝ) := by
    have hl := Real.log_nonpos v.property.1 v.property.2
    nlinarith [θ.property.1]
  rw [gumbelBarnett_cdf]
  by_cases hu : (u:ℝ) = 0
  · simp [hu, Real.zero_rpow (show 1-(θ:ℝ)*Real.log (v:ℝ) ≠ 0 by linarith)]
  have hu' : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm hu)
  rw [Real.rpow_def_of_pos hu']
  have he : Real.log (u:ℝ)*(1-(θ:ℝ)*Real.log (v:ℝ)) =
      Real.log (u:ℝ)+(-(θ:ℝ)*Real.log (u:ℝ)*Real.log (v:ℝ)) := by ring
  rw [he, Real.exp_add, Real.exp_log hu']
  ring

theorem gumbelBarnett_isSD (θ : I) : (gumbelBarnett θ).IsSD := by
  intro a b c v hab hbc
  rcases eq_or_lt_of_le hab with he | hab'
  · subst b; simp
  rcases eq_or_lt_of_le hbc with he | hbc'
  · subst c; simp
  have hp : 1 ≤ 1-(θ:ℝ)*Real.log (v:ℝ) := by
    have hl := Real.log_nonpos v.property.1 v.property.2
    nlinarith [θ.property.1]
  have hc := ConvexOn.smul v.property.1 (convexOn_rpow hp)
  have hs := hc.secant_mono_aux1 a.property.1 c.property.1
    (show (a:ℝ) < b from hab') (show (b:ℝ) < c from hbc')
  simp only [gumbelBarnett_cdf_power]
  dsimp at hs
  nlinarith [hs]

theorem gumbelBarnett_isCD (θ : I) : (gumbelBarnett θ).IsCD := by
  exact ⟨gumbelBarnett_isSD θ, by rw [gumbelBarnett_transpose]; exact gumbelBarnett_isSD θ⟩

private theorem log_half_sq_pos : 0 < Real.log (1/2:ℝ)^2 := by
  have h : Real.log (1/2:ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  exact sq_pos_of_ne_zero h.ne

theorem gumbelBarnett_isPQD_iff (θ : I) : (gumbelBarnett θ).IsPQD ↔ θ = 0 := by
  constructor
  · intro h
    let q : I := ⟨1/2, by norm_num, by norm_num⟩
    have ht := h q q
    rw [gumbelBarnett_cdf] at ht
    change (1/2:ℝ)*(1/2) ≤ (1/2:ℝ)*(1/2)*
      Real.exp (-(θ:ℝ)*Real.log (1/2:ℝ)*Real.log (1/2:ℝ)) at ht
    have he : 1 ≤ Real.exp (-(θ:ℝ)*Real.log (1/2:ℝ)*Real.log (1/2:ℝ)) := by nlinarith
    have hn := Real.one_le_exp_iff.mp he
    have hm : (θ:ℝ) ≤ 0 := by nlinarith [log_half_sq_pos]
    exact Subtype.ext (le_antisymm hm θ.property.1)
  · rintro rfl
    rw [gumbelBarnett_zero]
    exact Copula.isCI_independence.isPQD

theorem gumbelBarnett_isCI_iff (θ : I) : (gumbelBarnett θ).IsCI ↔ θ = 0 := by
  constructor
  · intro h
    exact (gumbelBarnett_isPQD_iff θ).mp h.isPQD
  · rintro rfl
    rw [gumbelBarnett_zero]
    exact Copula.isCI_independence

theorem gumbelBarnett_density_tp2_iff (θ : I) :
    (gumbelBarnett θ).HasMTP2Density ↔ θ = 0 := by
  constructor
  · intro h
    exact (gumbelBarnett_isPQD_iff θ).mp (Copula.hasMTP2Density_isPQD _ h)
  · rintro rfl
    rw [gumbelBarnett_zero]
    exact Copula.hasMTP2Density_independence 2

theorem gumbelBarnett_lowerOrthant_iff (θ η : I) :
    (gumbelBarnett θ).LowerOrthantLE (gumbelBarnett η) ↔ η ≤ θ := by
  constructor
  · intro h
    let q : I := ⟨1/2, by norm_num, by norm_num⟩
    have ht := h ![q,q]
    simp only [gumbelBarnett_cdf] at ht
    change (1/2:ℝ)*(1/2)*Real.exp (-(θ:ℝ)*Real.log (1/2:ℝ)*Real.log (1/2:ℝ)) ≤
      (1/2:ℝ)*(1/2)*Real.exp (-(η:ℝ)*Real.log (1/2:ℝ)*Real.log (1/2:ℝ)) at ht
    have he : Real.exp (-(θ:ℝ)*Real.log (1/2:ℝ)*Real.log (1/2:ℝ)) ≤
        Real.exp (-(η:ℝ)*Real.log (1/2:ℝ)*Real.log (1/2:ℝ)) := by nlinarith
    have hn := Real.exp_le_exp.mp he
    change (η:ℝ) ≤ θ
    nlinarith [log_half_sq_pos]
  · intro h x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, gumbelBarnett_cdf, gumbelBarnett_cdf]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (x 0).property.1 (x 1).property.1)
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ Real.log (x 0:ℝ)*Real.log (x 1:ℝ) :=
      mul_nonneg_of_nonpos_of_nonpos
        (Real.log_nonpos (x 0).property.1 (x 0).property.2)
        (Real.log_nonpos (x 1).property.1 (x 1).property.2)
    have hh := mul_le_mul_of_nonneg_right (show (η:ℝ) ≤ θ from h) hp
    nlinarith

theorem gumbelBarnett_schur_iff (θ η : I) :
    (gumbelBarnett θ).SchurBothLE (gumbelBarnett η) ↔ θ ≤ η := by
  rw [Copula.SchurBothLE, gumbelBarnett_transpose, gumbelBarnett_transpose, and_self]
  exact (schurLE_iff_lowerOrthantLE_isSD _ _ (gumbelBarnett_isSD θ)
    (gumbelBarnett_isSD η)).trans (gumbelBarnett_lowerOrthant_iff η θ)

theorem gumbelBarnett_tails (θ : I) :
    (gumbelBarnett θ).HasLowerTailDependence 0 ∧
      (gumbelBarnett θ).HasUpperTailDependence 0 :=
  ⟨Copula.isNQD_hasLowerTailDependence_zero (gumbelBarnett_isCD θ).isNQD,
    Copula.isNQD_hasUpperTailDependence_zero (gumbelBarnett_isCD θ).isNQD⟩

theorem gumbelBarnett_cdf_parameter_continuous (u v : I) :
    Continuous (fun θ : I => (gumbelBarnett θ).cdf ![u,v]) := by
  simp only [gumbelBarnett_cdf]
  fun_prop

end Verification
