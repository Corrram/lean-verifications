import Copula.Dependence.AMHTotalPositivity
import Verification.CubeFubini
import Mathlib.Analysis.Calculus.Deriv.Inv

open ProbabilityTheory MeasureTheory Set
open scoped unitInterval

namespace Verification

noncomputable def amhDen (θ u v : ℝ) : ℝ := 1 - θ * (1-u) * (1-v)

noncomputable def amhNum (θ u v : ℝ) : ℝ :=
  (1-θ) * amhDen θ u v + 2*θ*u*v

noncomputable def amhDensity (θ : ℝ) (x : Fin 2 → I) : ℝ :=
  amhNum θ (x 0) (x 1) / amhDen θ (x 0) (x 1)^3

theorem amhDen_pos {θ u v : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) : 0 < amhDen θ u v := by
  have hp : (1-u)*(1-v) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left (show 1-v ≤ 1 by linarith [hv.1])
      (show 0 ≤ 1-u by linarith [hu.2])
    linarith [hu.1]
  have ht := mul_le_mul_of_nonneg_left hp hθ
  dsimp [amhDen]
  nlinarith

theorem amhNum_nonneg {θ u v : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) : 0 ≤ amhNum θ u v := by
  exact add_nonneg (mul_nonneg (by linarith) (amhDen_pos hθ hθ1 hu hv).le)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hθ) hu.1) hv.1)

theorem amhDensity_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x : Fin 2 → I) : 0 ≤ amhDensity θ x :=
  div_nonneg (amhNum_nonneg hθ hθ1 (x 0).property (x 1).property)
    (pow_nonneg (amhDen_pos hθ hθ1 (x 0).property (x 1).property).le _)

theorem continuous_amhDensity {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    Continuous (amhDensity θ) := by
  apply Continuous.div
  · unfold amhNum amhDen; fun_prop
  · unfold amhDen; fun_prop
  · intro x
    exact pow_ne_zero _ (amhDen_pos hθ hθ1 (x 0).property (x 1).property).ne'

theorem amhNum_tp2 {θ : ℝ} (hθ : 0 ≤ θ) :
    IsTP2 (fun u v : I => amhNum θ u v) := by
  intro a b c d hab hcd
  have hi : amhNum θ a c * amhNum θ b d - amhNum θ a d * amhNum θ b c =
      θ * (1-θ)^2 * ((b:ℝ)-a) * ((d:ℝ)-c) := by
    unfold amhNum amhDen
    ring
  have hn := mul_nonneg (mul_nonneg (mul_nonneg hθ (sq_nonneg (1-θ)))
    (sub_nonneg.mpr (show (a:ℝ) ≤ b from hab)))
    (sub_nonneg.mpr (show (c:ℝ) ≤ d from hcd))
  linarith

theorem amhDen_inv_tp2 {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    IsTP2 (fun u v : I => 1 / amhDen θ u v) := by
  intro a b c d hab hcd
  have hp (u v : I) := amhDen_pos hθ hθ1 u.property v.property
  have hi : amhDen θ a d * amhDen θ b c - amhDen θ a c * amhDen θ b d =
      θ * ((b:ℝ)-a) * ((d:ℝ)-c) := by unfold amhDen; ring
  have hn := mul_nonneg (mul_nonneg hθ
    (sub_nonneg.mpr (show (a:ℝ) ≤ b from hab)))
    (sub_nonneg.mpr (show (c:ℝ) ≤ d from hcd))
  have hd : amhDen θ a c * amhDen θ b d ≤ amhDen θ a d * amhDen θ b c := by
    linarith
  simp only [div_mul_div_comm, one_mul]
  exact div_le_div_of_nonneg_left zero_le_one (mul_pos (hp a c) (hp b d)) hd

theorem isMTP2_amhDensity {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    IsMTP2 (amhDensity θ) := by
  rw [Copula.isMTP2_fin_two_iff]
  have hn (u v : I) : 0 ≤ amhNum θ u v := amhNum_nonneg hθ hθ1 u.property v.property
  have hd (u v : I) : 0 ≤ 1 / amhDen θ u v :=
    (one_div_pos.mpr (amhDen_pos hθ hθ1 u.property v.property)).le
  have ht := amhDen_inv_tp2 hθ hθ1
  have ht2 := ht.mul ht hd hd
  have ht3 := ht2.mul ht (fun u v => mul_nonneg (hd u v) (hd u v)) hd
  have h := (amhNum_tp2 hθ).mul ht3 hn
    (fun u v => mul_nonneg (mul_nonneg (hd u v) (hd u v)) (hd u v))
  convert h using 1
  funext u v
  simp only [amhDensity, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

noncomputable def amhPartial (θ u v : ℝ) : ℝ :=
  v * (1-θ*(1-v)) / amhDen θ u v ^ 2

theorem amh_cdf_derivative {θ u v : ℝ} (hd : amhDen θ u v ≠ 0) :
    HasDerivAt (fun x : ℝ => x*v / amhDen θ x v) (amhPartial θ u v) u := by
  have hden : HasDerivAt (fun x => amhDen θ x v) (θ*(1-v)) u := by
    convert (((hasDerivAt_id u).const_sub 1).const_mul θ |>.mul_const (1-v)).const_sub 1 using 1 <;>
      first | rfl | ring
  convert ((hasDerivAt_id u).mul_const v).div hden hd using 1
  · rfl
  · dsimp [amhPartial]
    field_simp
    unfold amhDen
    ring

theorem amh_partial_derivative {θ u v : ℝ} (hd : amhDen θ u v ≠ 0) :
    HasDerivAt (fun y : ℝ => amhPartial θ u y)
      (amhNum θ u v / amhDen θ u v ^ 3) v := by
  have hden : HasDerivAt (fun y => amhDen θ u y) (θ*(1-u)) v := by
    convert (((hasDerivAt_id v).const_sub 1).const_mul (θ*(1-u))).const_sub 1 using 1 <;>
      first | rfl | ring
  have hnum := (hasDerivAt_id v).mul
    ((((hasDerivAt_id v).const_sub 1).const_mul θ).const_sub 1)
  convert hnum.div (hden.pow 2) (pow_ne_zero 2 hd) using 1
  · rfl
  · dsimp [amhNum, amhPartial]
    field_simp [hd]
    unfold amhDen
    ring

theorem integral_amhDensity_second {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (u v : I) :
    (∫ y in Iic v, amhDensity θ ![u,y]) = amhPartial θ u v := by
  change (∫ y in Iic v, amhNum θ u y / amhDen θ u y ^ 3) = _
  rw [Copula.integral_unit_Iic (fun y => amhNum θ u y / amhDen θ u y ^ 3)]
  have hmem (y : ℝ) (hy : y ∈ uIcc 0 (v:ℝ)) : y ∈ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le v.property.1] at hy
    exact ⟨hy.1, hy.2.trans v.property.2⟩
  have hc : ContinuousOn (fun y : ℝ => amhNum θ u y / amhDen θ u y ^ 3)
      (uIcc 0 (v:ℝ)) := by
    apply ContinuousOn.div
    · unfold amhNum amhDen; fun_prop
    · unfold amhDen; fun_prop
    · intro y hy
      exact pow_ne_zero _ (amhDen_pos hθ hθ1 u.property (hmem y hy)).ne'
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => amh_partial_derivative (amhDen_pos hθ hθ1 u.property (hmem y hy)).ne')
    hc.intervalIntegrable
  simpa [amhPartial] using he

theorem integral_amhPartial_first {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (u v : I) : (∫ x in Iic u, amhPartial θ x v) = (u:ℝ)*v / amhDen θ u v := by
  rw [Copula.integral_unit_Iic (fun x => amhPartial θ x v)]
  have hmem (x : ℝ) (hx : x ∈ uIcc 0 (u:ℝ)) : x ∈ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le u.property.1] at hx
    exact ⟨hx.1, hx.2.trans u.property.2⟩
  have hc : ContinuousOn (fun x : ℝ => amhPartial θ x v) (uIcc 0 (u:ℝ)) := by
    unfold amhPartial
    apply ContinuousOn.div
    · fun_prop
    · unfold amhDen; fun_prop
    · intro x hx
      exact pow_ne_zero _ (amhDen_pos hθ hθ1 (hmem x hx) v.property).ne'
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => amh_cdf_derivative (amhDen_pos hθ hθ1 (hmem x hx) v.property).ne')
    hc.intervalIntegrable
  simpa using he

theorem amh_toMeasure_density {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    (Copula.amh θ (by linarith) hθ1.le).toMeasure =
      (volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal (amhDensity θ x)) := by
  apply Copula.toMeasure_eq_withDensity_of_cdf_integral _
    (Copula.integrable_continuous_cube volume (continuous_amhDensity hθ hθ1))
    (amhDensity_nonneg hθ hθ1)
  intro x
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, integral_cube_Iic_iterated
    (Copula.integrable_continuous_cube volume (continuous_amhDensity hθ hθ1))]
  simp_rw [integral_amhDensity_second hθ hθ1]
  rw [integral_amhPartial_first hθ hθ1, Copula.cdf_amh]
  rfl

theorem amh_hasMTP2Density {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    (Copula.amh θ (by linarith) hθ1.le).HasMTP2Density :=
  ⟨amhDensity θ, (continuous_amhDensity hθ hθ1).measurable,
    amhDensity_nonneg hθ hθ1, isMTP2_amhDensity hθ hθ1, amh_toMeasure_density hθ hθ1⟩

end Verification
