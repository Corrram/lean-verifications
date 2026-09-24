import Copula.Families.AMH
import Copula.Archimedean.Power
import Copula.Archimedean.Symmetry
import Copula.Dependence.DensityTotalPositivity
import Copula.TailDependence.Quadrant

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

theorem innerPower_cdf (g : BivariateGenerator) (p : ℝ) (hp : 1 ≤ p) (u v : I) :
    (g.innerPower p hp).copula.cdf ![u,v] =
      (g.copula.cdf ![unitPower u p⁻¹ (inv_nonneg.mpr (by linarith)),
        unitPower v p⁻¹ (inv_nonneg.mpr (by linarith))])^p := by
  have hn (w : I) : unitPower w p⁻¹ (inv_nonneg.mpr (by linarith)) = 0 ↔ w = 0 := by
    constructor
    · intro h
      apply Subtype.ext
      have hh := congrArg (fun z : I => (z:ℝ)) h
      exact (Real.rpow_eq_zero_iff_of_nonneg w.property.1).mp hh |>.1
    · rintro rfl
      apply Subtype.ext
      exact Real.zero_rpow (inv_ne_zero (by linarith))
  simp only [BivariateGenerator.cdf_copula, Matrix.cons_val_zero, Matrix.cons_val_one,
    BivariateGenerator.cdf, hn]
  by_cases h : u = 0 ∨ v = 0
  · simp [h, Real.zero_rpow (show p ≠ 0 by linarith)]
  · simp only [h, ite_false]
    rfl

/-- Nelsen 10 is the inner-power transform of AMH at parameter minus one. -/
noncomputable def nelsen10Positive (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) : Copula 2 :=
  ((amhGenerator (-1) le_rfl (by norm_num)).innerPower θ⁻¹ ((one_le_inv₀ hθ).mpr hθ1)).copula

noncomputable def nelsen10 (θ : I) : Copula 2 :=
  if h : (θ:ℝ) = 0 then independence 2
  else nelsen10Positive θ (lt_of_le_of_ne θ.property.1 (Ne.symm h)) θ.property.2

theorem nelsen10_zero : nelsen10 0 = independence 2 := by simp [nelsen10]

theorem nelsen10_positive_cdf (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (u v : I) :
    (nelsen10Positive θ hθ hθ1).cdf ![u,v] =
      (u:ℝ)*v/(1+(1-(u:ℝ)^θ)*(1-(v:ℝ)^θ))^θ⁻¹ := by
  unfold nelsen10Positive
  rw [innerPower_cdf]
  have hg : (amhGenerator (-1) le_rfl (by norm_num)).copula = amh (-1) le_rfl (by norm_num) := by
    norm_num [amh]
  rw [hg, cdf_amh]
  simp only [coe_unitPower, inv_inv, neg_mul, one_mul, sub_neg_eq_add]
  have hu := Real.rpow_nonneg u.property.1 θ
  have hv := Real.rpow_nonneg v.property.1 θ
  have hd : 0 ≤ 1+(1-(u:ℝ)^θ)*(1-(v:ℝ)^θ) := by
    have hu1 := Real.rpow_le_one u.property.1 u.property.2 hθ.le
    have hv1 := Real.rpow_le_one v.property.1 v.property.2 hθ.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hv1)]
  rw [Real.div_rpow (mul_nonneg hu hv) hd, Real.mul_rpow hu hv,
    Real.rpow_rpow_inv u.property.1 hθ.ne', Real.rpow_rpow_inv v.property.1 hθ.ne']

theorem nelsen10_one : nelsen10 1 = amh (-1) le_rfl (by norm_num) := by
  norm_num [nelsen10, nelsen10Positive, amh]

theorem nelsen10_cdf (θ u v : I) (hθ : 0 < (θ:ℝ)) :
    (nelsen10 θ).cdf ![u,v] =
      (u:ℝ)*v/(1+(1-(u:ℝ)^(θ:ℝ))*(1-(v:ℝ)^(θ:ℝ)))^(θ:ℝ)⁻¹ := by
  simp only [nelsen10, hθ.ne', dite_false]
  exact nelsen10_positive_cdf θ hθ θ.property.2 u v

theorem nelsen10_isNQD (θ : I) : (nelsen10 θ).IsNQD := by
  by_cases hz : (θ:ℝ) = 0
  · have he : θ = 0 := Subtype.ext hz
    rw [he, nelsen10_zero]
    exact isNQD_independence
  have hp : 0 < (θ:ℝ) := lt_of_le_of_ne θ.property.1 (Ne.symm hz)
  intro u v
  rw [nelsen10_cdf θ u v hp]
  have hu := Real.rpow_le_one u.property.1 u.property.2 θ.property.1
  have hv := Real.rpow_le_one v.property.1 v.property.2 θ.property.1
  have hd : 1 ≤ 1+(1-(u:ℝ)^(θ:ℝ))*(1-(v:ℝ)^(θ:ℝ)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)]
  exact div_le_self (mul_nonneg u.property.1 v.property.1)
    (Real.one_le_rpow hd (inv_nonneg.mpr θ.property.1))

theorem nelsen10_isPQD_iff (θ : I) : (nelsen10 θ).IsPQD ↔ θ = 0 := by
  constructor
  · intro h
    by_contra hz
    have hp : 0 < (θ:ℝ) := lt_of_le_of_ne θ.property.1
      (Ne.symm (fun hh => hz (Subtype.ext hh)))
    let q : I := ⟨1/2, by norm_num, by norm_num⟩
    have hh := h q q
    rw [nelsen10_cdf θ q q hp] at hh
    have hq : (1/2:ℝ)^(θ:ℝ) < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hp
    have hd : 1 < 1+(1-(1/2:ℝ)^(θ:ℝ))*(1-(1/2:ℝ)^(θ:ℝ)) := by
      nlinarith [sq_pos_of_pos (sub_pos.mpr hq)]
    have hpow := Real.one_lt_rpow hd (inv_pos.mpr hp)
    have hlt := div_lt_self (by norm_num : 0 < (1/2:ℝ)*(1/2)) hpow
    exact (not_le_of_gt hlt) hh
  · rintro rfl
    rw [nelsen10_zero]
    exact isPQD_independence

theorem nelsen10_isCI_iff (θ : I) : (nelsen10 θ).IsCI ↔ θ = 0 := by
  constructor
  · intro h
    exact (nelsen10_isPQD_iff θ).mp h.isPQD
  · rintro rfl
    rw [nelsen10_zero]
    exact isCI_independence

theorem nelsen10_density_tp2_iff (θ : I) : (nelsen10 θ).HasMTP2Density ↔ θ = 0 := by
  constructor
  · intro h
    exact (nelsen10_isPQD_iff θ).mp (hasMTP2Density_isPQD _ h)
  · rintro rfl
    rw [nelsen10_zero]
    exact hasMTP2Density_independence 2

theorem nelsen10_tails (θ : I) :
    (nelsen10 θ).HasLowerTailDependence 0 ∧ (nelsen10 θ).HasUpperTailDependence 0 :=
  ⟨isNQD_hasLowerTailDependence_zero (nelsen10_isNQD θ),
    isNQD_hasUpperTailDependence_zero (nelsen10_isNQD θ)⟩

end Verification
