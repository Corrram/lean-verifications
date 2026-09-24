import Verification.Nelsen17
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n17PowerBase (a x y : ℝ) : ℝ := 1+(x^a-1)*(y^a-1)/((2:ℝ)^a-1)

theorem n17PowerBase_bounds {a x y : ℝ} (ha : 1 ≤ a) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hx2 : 2 ≤ x^a) (hy2 : 2 ≤ y^a) :
    max 1 ((x*y/2)*(4:ℝ)^(-a⁻¹)) ≤ n17PowerBase a x y^a⁻¹ ∧
      n17PowerBase a x y^a⁻¹ ≤ (4:ℝ)^a⁻¹*max 1 (x*y/2) := by
  have hap : 0 < a := by linarith
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hz2 : 2 ≤ (2:ℝ)^a := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ha
    simpa only [Real.rpow_one] using hh
  have hz : 0 < (2:ℝ)^a-1 := by linarith
  have hprod : 0 ≤ (x^a-1)*(y^a-1) := mul_nonneg (by linarith) (by linarith)
  have hB1 : 1 ≤ n17PowerBase a x y := by
    dsimp [n17PowerBase]
    exact le_add_of_nonneg_right (div_nonneg hprod hz.le)
  have hB : 0 < n17PowerBase a x y := by linarith
  have hp : (x*y/2)^a = x^a*y^a/(2:ℝ)^a := by
    rw [Real.div_rpow (mul_nonneg hx0.le hy0.le) (by norm_num), Real.mul_rpow hx0.le hy0.le]
  have hlo : (x*y/2)^a/4 ≤ n17PowerBase a x y := by
    rw [hp]
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 4)).mpr
    apply (div_le_iff₀ (by linarith : 0 < (2:ℝ)^a)).mpr
    have hsmall : x^a*y^a ≤ 4*((x^a-1)*(y^a-1)) := by
      nlinarith [mul_nonneg (show 0 ≤ x^a-2 by linarith) (show 0 ≤ y^a-2 by linarith)]
    have hid : (n17PowerBase a x y-1)*((2:ℝ)^a-1) = (x^a-1)*(y^a-1) := by
      dsimp [n17PowerBase]; field_simp; ring
    nlinarith
  have hhi : n17PowerBase a x y ≤ 4*(max 1 (x*y/2))^a := by
    have hm1 : 1 ≤ (max 1 (x*y/2))^a := Real.one_le_rpow (le_max_left _ _) hap.le
    have hmp : (x*y/2)^a ≤ (max 1 (x*y/2))^a :=
      Real.rpow_le_rpow (by positivity) (le_max_right _ _) hap.le
    have hratio : (x^a-1)*(y^a-1)/((2:ℝ)^a-1) ≤ 2*(x*y/2)^a := by
      rw [hp]
      apply (div_le_iff₀ hz).mpr
      have hz0 : 0 < (2:ℝ)^a := by linarith
      have he : 2*(x^a*y^a/(2:ℝ)^a)*((2:ℝ)^a-1) =
          (2*x^a*y^a*((2:ℝ)^a-1))/(2:ℝ)^a := by ring
      rw [he]
      apply (le_div_iff₀ hz0).mpr
      have hpositive := mul_nonneg hz0.le (show 0 ≤ x^a+y^a-1 by linarith)
      nlinarith [mul_nonneg (show 0 ≤ (2:ℝ)^a-2 by linarith) (mul_nonneg (by linarith : 0 ≤ x^a) (by linarith : 0 ≤ y^a))]
    dsimp [n17PowerBase]
    linarith
  have hrlo := Real.rpow_le_rpow (by positivity : 0 ≤ (x*y/2)^a/4) hlo (inv_pos.mpr hap).le
  have hrhi := Real.rpow_le_rpow hB.le hhi (inv_pos.mpr hap).le
  have hloeq : ((x*y/2)^a/4)^a⁻¹ = (x*y/2)*(4:ℝ)^(-a⁻¹) := by
    rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_rpow_inv (by positivity) hap.ne',
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
    rfl
  have hhieq : (4*(max 1 (x*y/2))^a)^a⁻¹ = (4:ℝ)^a⁻¹*max 1 (x*y/2) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_rpow_inv (by positivity) hap.ne']
  rw [hloeq] at hrlo
  rw [hhieq] at hrhi
  exact ⟨max_le (Real.one_le_rpow hB1 (inv_pos.mpr hap).le) hrlo,hrhi⟩

theorem nelsen17_tendsto_atBot {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, θ a ≠ 0) (ht : Tendsto θ l atBot) (u v : I) :
    Tendsto (fun a => (nelsen17 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 (max 1 ((1+(u:ℝ))*(1+(v:ℝ))/2)-1)) := by
  by_cases hu : u = 0
  · subst u
    have hz : max 1 ((1+((0:I):ℝ))*(1+(v:ℝ))/2)-1 = 0 := by
      rw [max_eq_left (by change (1+0)*(1+(v:ℝ))/2 ≤ 1; linarith [v.property.2])]
      ring
    rw [hz]
    simp only [cdf_two_zero_left]
    exact tendsto_const_nhds
  by_cases hv : v = 0
  · subst v
    have hz : max 1 ((1+(u:ℝ))*(1+((0:I):ℝ))/2)-1 = 0 := by
      rw [max_eq_left (by change (1+(u:ℝ))*(1+0)/2 ≤ 1; linarith [u.property.2])]
      ring
    rw [hz]
    have he (C : Copula 2) : C.cdf ![u,0] = 0 := C.cdf_eq_zero_of_coord_eq_zero _ 1 (by simp)
    simp only [he]
    exact tendsto_const_nhds
  have hu0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
  have hv0 : 0 < (v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hv))
  have ht' : Tendsto (fun a => -θ a) l atTop := tendsto_neg_atBot_atTop.comp ht
  have hi : Tendsto (fun a => (-θ a)⁻¹) l (𝓝 (0:ℝ)) := tendsto_inv_atTop_zero.comp ht'
  have hp : Tendsto (fun a => (4:ℝ)^((-θ a)⁻¹)) l (𝓝 (1:ℝ)) := by
    simpa only [Real.rpow_zero] using tendsto_const_nhds.rpow hi (Or.inl (by norm_num : (4:ℝ) ≠ 0))
  have hn : Tendsto (fun a => (4:ℝ)^(-(-θ a)⁻¹)) l (𝓝 (1:ℝ)) := by
    simpa only [Real.rpow_zero,neg_zero] using tendsto_const_nhds.rpow hi.neg (Or.inl (by norm_num : (4:ℝ) ≠ 0))
  let z : ℝ := (1+(u:ℝ))*(1+(v:ℝ))/2
  have hlo : Tendsto (fun a => max 1 (z*(4:ℝ)^(-(-θ a)⁻¹))-1) l (𝓝 (max 1 z-1)) := by
    simpa only [mul_one] using ((tendsto_const_nhds.max (hn.const_mul z)).sub_const 1)
  have hhi : Tendsto (fun a => (4:ℝ)^((-θ a)⁻¹)*max 1 z-1) l (𝓝 (max 1 z-1)) := by
    simpa only [one_mul] using (hp.mul_const (max 1 z)).sub_const 1
  have hxu := (tendsto_rpow_atTop_of_base_gt_one (1+(u:ℝ)) (by linarith)).comp ht'
  have hxv := (tendsto_rpow_atTop_of_base_gt_one (1+(v:ℝ)) (by linarith)).comp ht'
  have hevent : ∀ᶠ a in l, 1 ≤ -θ a ∧ 2 ≤ (1+(u:ℝ))^(-θ a) ∧ 2 ≤ (1+(v:ℝ))^(-θ a) := by
    filter_upwards [ht'.eventually (eventually_ge_atTop (1:ℝ)),
      hxu.eventually (eventually_ge_atTop (2:ℝ)), hxv.eventually (eventually_ge_atTop (2:ℝ))] with a ha hb hc
    exact ⟨ha,hb,hc⟩
  have he (a : α) : (nelsen17 (θ a) (hθ a)).cdf ![u,v] =
      n17PowerBase (-θ a) (1+(u:ℝ)) (1+(v:ℝ))^(-θ a)⁻¹-1 := by
    rw [nelsen17_cdf_full]
    simp only [n17PowerBase,inv_neg]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hevent] with a ha
    rw [he]
    exact sub_le_sub_right (n17PowerBase_bounds ha.1 (by linarith : 1 ≤ 1+(u:ℝ))
      (by linarith : 1 ≤ 1+(v:ℝ)) ha.2.1 ha.2.2).1 1
  · filter_upwards [hevent] with a ha
    rw [he]
    exact sub_le_sub_right (n17PowerBase_bounds ha.1 (by linarith : 1 ≤ 1+(u:ℝ))
      (by linarith : 1 ≤ 1+(v:ℝ)) ha.2.1 ha.2.2).2 1

end Verification
