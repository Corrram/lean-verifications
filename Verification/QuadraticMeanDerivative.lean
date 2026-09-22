import Verification.QuadraticSectionIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! # Differentiating the clamped quadratic normalization map -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval Topology

namespace Verification

theorem unitClamp_lipschitz : LipschitzWith 1 unitClamp :=
  LipschitzWith.id.const_max 0 |>.const_min 1

theorem hasDerivAt_unitClamp (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt unitClamp (if 0<x ∧ x<1 then 1 else 0) x := by
  rcases lt_or_gt_of_ne hx0 with hx | hx
  · rw [ite_eq_right (by simp [not_lt_of_ge hx.le])]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    unfold unitClamp
    rw [max_eq_left hy.le]
    norm_num
  · rcases lt_or_gt_of_ne hx1 with h1 | h1
    · rw [ite_eq_left ⟨hx,h1⟩]
      apply (hasDerivAt_id x).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds hx,eventually_lt_nhds h1] with y hy0 hy1
      unfold unitClamp
      rw [max_eq_right hy0.le,min_eq_right hy1.le]
      rfl
    · rw [ite_eq_right (by simp [not_lt_of_ge h1.le])]
      apply (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
      filter_upwards [eventually_gt_nhds h1] with y hy
      unfold unitClamp
      rw [max_eq_right (by linarith),min_eq_left hy.le]

theorem square_ae_ne (a : ℝ) : ∀ᵐ x : I,(x : ℝ)^2 ≠ a := by
  have he (x : I) (hx : (x : ℝ)^2=a) : Real.sqrt a=(x : ℝ) := by
    rw [← hx,Real.sqrt_sq x.property.1]
  by_cases ha : Real.sqrt a ∈ Icc (0 : ℝ) 1
  · filter_upwards [volume.ae_ne (⟨Real.sqrt a,ha⟩ : I)] with x hx
    intro hh
    apply hx
    exact Subtype.ext (he x hh).symm
  · exact Filter.Eventually.of_forall fun x hx => ha ((he x hx).symm ▸ x.property)

noncomputable def clampedSquareMean (b q : ℝ) : ℝ := ∫ x : I,unitClamp (b*((x : ℝ)^2-q))

theorem clampedSquareMean_hasDerivAt_integral (b q : ℝ) (hb : 0 < b) :
    HasDerivAt (clampedSquareMean b)
      (∫ x : I,if 0<b*((x : ℝ)^2-q) ∧ b*((x : ℝ)^2-q)<1 then -b else 0) q := by
  have hd : ∀ᵐ x : I, HasDerivAt (fun y => unitClamp (b*((x : ℝ)^2-y)))
      (if 0<b*((x : ℝ)^2-q) ∧ b*((x : ℝ)^2-q)<1 then -b else 0) q := by
    filter_upwards [square_ae_ne q,square_ae_ne (q+1/b)] with x hx0 hx1
    have h0 : b*((x : ℝ)^2-q) ≠ 0 := mul_ne_zero hb.ne' (sub_ne_zero.mpr hx0)
    have h1 : b*((x : ℝ)^2-q) ≠ 1 := by
      intro hh
      have hdiv : (x : ℝ)^2-q=1/b := (eq_div_iff hb.ne').mpr (by nlinarith [hh])
      apply hx1
      linarith
    have h := (hasDerivAt_unitClamp _ h0 h1).comp q
      (((hasDerivAt_id q).const_sub ((x : ℝ)^2)).const_mul b)
    convert! h using 1
    split_ifs <;> ring
  have hl (x : I) : LipschitzWith (Real.nnabs b) (fun y : ℝ => unitClamp (b*((x : ℝ)^2-y))) := by
    have h : LipschitzWith (Real.nnabs b) (fun y : ℝ => b*((x : ℝ)^2-y)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      rw [Real.dist_eq,Real.dist_eq,Real.coe_nnabs]
      have he : b*((x : ℝ)^2-y)-b*((x : ℝ)^2-z)=b*(z-y) := by ring
      rw [he,abs_mul,abs_sub_comm z y]
    simpa only [one_mul,Function.comp_def] using unitClamp_lipschitz.comp h
  have hm : Measurable (fun x : I => b*((x : ℝ)^2-q)) := by fun_prop
  have hm' : Measurable (fun x : I => if 0<b*((x : ℝ)^2-q) ∧ b*((x : ℝ)^2-q)<1 then -b else 0) :=
    measurable_const.ite ((measurableSet_lt measurable_const hm).inter
      (measurableSet_lt hm measurable_const)) measurable_const
  exact (hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun y : ℝ => fun x : I => unitClamp (b*((x : ℝ)^2-y))) (x₀ := q)
    (s := univ) (bound := fun _ : I => b)
    (Filter.univ_mem)
    (Filter.Eventually.of_forall fun y => (by unfold unitClamp; fun_prop : Continuous (fun x : I => unitClamp (b*((x : ℝ)^2-y)))).aestronglyMeasurable)
    (Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop))
    hm'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (hl x).lipschitzOnWith)
    (integrable_const b) hd).2

theorem clampedSquareMean_hasDerivAt (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1) :
    HasDerivAt (clampedSquareMean b) (-b*(quadraticUpper b q-quadraticLower q)) q := by
  let r := quadraticLower q
  let s := quadraticUpper b q
  obtain ⟨hr,hrs,hs⟩ := quadratic_switch_bounds b q hb hq
  change 0 ≤ r at hr
  change r ≤ s at hrs
  change s ≤ 1 at hs
  let ru : I := ⟨r,hr,hrs.trans hs⟩
  let su : I := ⟨s,hr.trans hrs,hs⟩
  have hR : 0 ≤ q+1/b := by linarith [show -(1/b) ≤ q by simpa only [neg_div] using hq.1]
  have hrsq : r^2=max 0 q := Real.sq_sqrt (le_max_left _ _)
  have hRsq := Real.sq_sqrt hR
  have hinv : b*(1/b)=1 := by field_simp
  have he : (fun x : I => if 0<b*((x : ℝ)^2-q) ∧ b*((x : ℝ)^2-q)<1 then -b else 0) =ᵐ[volume]
      (Ioo ru su).indicator (fun _ => -b) := by
    filter_upwards [volume.ae_ne (0 : I),volume.ae_ne (1 : I)] with x hx0 hx1
    have hxpos : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (by
      intro hh; apply hx0; exact Subtype.ext hh.symm)
    have hxlt : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 (by
      intro hh; apply hx1; exact Subtype.ext hh)
    have hiff : (0<b*((x : ℝ)^2-q) ∧ b*((x : ℝ)^2-q)<1) ↔ x ∈ Ioo ru su := by
      change _ ↔ r<(x : ℝ) ∧ (x : ℝ)<s
      constructor
      · rintro ⟨h0,h1⟩
        have hqlo : q < (x : ℝ)^2 := by nlinarith
        have hqhi : (x : ℝ)^2 < q+1/b := by nlinarith
        constructor
        · rcases le_total 0 q with hq0 | hq0
          · rw [max_eq_right hq0] at hrsq
            nlinarith
          · rw [max_eq_left hq0] at hrsq
            nlinarith
        · apply lt_min hxlt
          nlinarith [Real.sqrt_nonneg (q+1/b)]
      · rintro ⟨h0,h1⟩
        have hxR : (x : ℝ)<Real.sqrt (q+1/b) := h1.trans_le (min_le_right _ _)
        have hqlo : q < (x : ℝ)^2 := by nlinarith [le_max_right (0 : ℝ) q]
        have hqhi : (x : ℝ)^2 < q+1/b := by nlinarith [Real.sqrt_nonneg (q+1/b)]
        exact ⟨mul_pos hb (sub_pos.mpr hqlo),by nlinarith [mul_pos hb (sub_pos.mpr hqhi)]⟩
    by_cases hmem : x ∈ Ioo ru su
    · rw [ite_eq_left (hiff.mpr hmem),indicator_of_mem hmem]
    · rw [ite_eq_right (fun hh => hmem (hiff.mp hh)),indicator_of_notMem hmem]
  have hi : (∫ x : I,if 0<b*((x : ℝ)^2-q) ∧ b*((x : ℝ)^2-q)<1 then -b else 0)= -b*(s-r) := by
    rw [integral_congr_ae he,integral_indicator measurableSet_Ioo,integral_const]
    simp only [Measure.real,Measure.restrict_apply_univ,unitInterval.volume_Ioo,smul_eq_mul]
    change (ENNReal.ofReal (s-r)).toReal*(-b)= -b*(s-r)
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hrs)]
    ring
  convert! clampedSquareMean_hasDerivAt_integral b q hb using 1
  exact hi.symm

end Verification
