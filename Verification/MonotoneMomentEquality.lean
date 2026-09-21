import Verification.StochasticRho

/-! # Equality in the decreasing-function moment bound

The nonnegative defect |g(u)-g(w)|-(g(u)-g(w))^2 vanishes precisely
when each difference is zero or has absolute value one. Consequently a
bounded function is either constant or binary almost everywhere.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

def pairMomentDefect (x y : ℝ) : ℝ := |x - y| - (x - y) ^ 2

theorem pairMomentDefect_mem_Icc {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    pairMomentDefect x y ∈ Icc 0 1 := by
  have ha : |x - y| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
  unfold pairMomentDefect
  constructor <;> nlinarith [sq_abs (x - y), abs_nonneg (x - y), sq_nonneg (x - y)]

theorem integrable_pairMomentDefect {g : I → ℝ} (hg : Measurable g)
    (hb : ∀ u, g u ∈ Icc 0 1) :
    Integrable (fun p : I × I => pairMomentDefect (g p.1) (g p.2))
      ((volume : Measure I).prod volume) := by
  refine (integrable_const (1 : ℝ)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · unfold pairMomentDefect
    exact ((continuous_abs.measurable.comp ((hg.comp measurable_fst).sub
      (hg.comp measurable_snd))).sub
      (((hg.comp measurable_fst).sub (hg.comp measurable_snd)).pow_const 2)).aestronglyMeasurable
  · have h := pairMomentDefect_mem_Icc (hb p.1) (hb p.2)
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem integral_sq_sub_unit {g : I → ℝ} (hg : Measurable g)
    (hb : ∀ u, g u ∈ Icc 0 1) (c : ℝ) :
    (∫ w : I, (c - g w) ^ 2) = c ^ 2 - 2 * c * (∫ w : I, g w) + ∫ w : I, g w ^ 2 := by
  have hi := integrable_unit_bounded hg hb
  have hsq : Integrable (fun w => g w ^ 2) := integrable_unit_bounded (hg.pow_const 2)
    (fun w => ⟨sq_nonneg _, by nlinarith [(hb w).1, (hb w).2]⟩)
  have he : (fun w : I => (c - g w) ^ 2) = fun w => c ^ 2 - (2 * c) * g w + g w ^ 2 := by
    funext w; ring
  have hd : Integrable (fun w => c ^ 2 - (2 * c) * g w) :=
    (integrable_const _).sub (hi.const_mul _)
  rw [he, integral_add hd hsq, integral_sub (integrable_const _) (hi.const_mul _),
    integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem integral_integral_sq_sub_unit {g : I → ℝ} (hg : Measurable g)
    (hb : ∀ u, g u ∈ Icc 0 1) :
    (∫ u : I, ∫ w : I, (g u - g w) ^ 2) =
      2 * (∫ u : I, g u ^ 2) - 2 * (∫ u : I, g u) ^ 2 := by
  have hi := integrable_unit_bounded hg hb
  have hsq : Integrable (fun w => g w ^ 2) := integrable_unit_bounded (hg.pow_const 2)
    (fun w => ⟨sq_nonneg _, by nlinarith [(hb w).1, (hb w).2]⟩)
  have hd : Integrable (fun u => g u ^ 2 - 2 * g u * (∫ w : I, g w)) :=
    hsq.sub ((hi.const_mul 2).mul_const _)
  simp_rw [integral_sq_sub_unit hg hb]
  rw [integral_add hd (integrable_const _),
    integral_sub hsq ((hi.const_mul 2).mul_const _), integral_mul_const, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

theorem integral_integral_abs_sub_of_antitone {g : I → ℝ} (hg : Antitone g)
    (hb : ∀ u, g u ∈ Icc 0 1) :
    (∫ u : I, ∫ w : I, |g u - g w|) =
      4 * (∫ u : I, ∫ w in Iic u, g w) - 2 * (∫ u : I, g u) := by
  have hi := integrable_unit_bounded hg.measurable hb
  have hF := integrable_lower_integral hg.measurable hb
  have hw : Integrable (fun u : I => (u : ℝ) * g u) :=
    integrable_unit_bounded (measurable_subtype_coe.mul hg.measurable)
      (fun u => ⟨mul_nonneg u.property.1 (hb u).1,
        (mul_le_mul_of_nonneg_right u.property.2 (hb u).1).trans (by simpa using (hb u).2)⟩)
  have hd : Integrable (fun u => 2 * (∫ w in Iic u, g w) - (∫ w : I, g w)) :=
    (hF.const_mul 2).sub (integrable_const _)
  have ha : Integrable (fun u => 2 * (∫ w in Iic u, g w) - (∫ w : I, g w) + g u) := hd.add hi
  simp_rw [integral_abs_sub_of_antitone hg hb, mul_assoc]
  rw [integral_sub ha (hw.const_mul 2), integral_add hd hi,
    integral_sub (hF.const_mul 2) (integrable_const _), integral_const_mul, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hA := integral_lower_integral hg.measurable hb
  have hid : (fun u : I => (1 - (u : ℝ)) * g u) = fun u => g u - (u : ℝ) * g u := by
    funext u; ring
  rw [hid, integral_sub hi hw] at hA
  linarith

theorem integral_pairMomentDefect {g : I → ℝ} (hg : Antitone g)
    (hb : ∀ u, g u ∈ Icc 0 1) :
    (∫ u : I, ∫ w : I, pairMomentDefect (g u) (g w)) =
      2 * (2 * (∫ u : I, ∫ w in Iic u, g w) - (∫ u : I, g u) +
        (∫ u : I, g u) ^ 2 - (∫ u : I, g u ^ 2)) := by
  have ha (u w : I) : |g u - g w| ≤ 1 := abs_le.mpr
    ⟨by linarith [(hb u).1, (hb w).2], by linarith [(hb u).2, (hb w).1]⟩
  have hiabs : Integrable (fun p : I × I => |g p.1 - g p.2|)
      ((volume : Measure I).prod volume) := by
    refine (integrable_const (1 : ℝ)).mono'
      (continuous_abs.measurable.comp ((hg.measurable.comp measurable_fst).sub
        (hg.measurable.comp measurable_snd))).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs, abs_abs] using ha p.1 p.2
  have hisq : Integrable (fun p : I × I => (g p.1 - g p.2) ^ 2)
      ((volume : Measure I).prod volume) := by
    refine (integrable_const (1 : ℝ)).mono'
      (((hg.measurable.comp measurable_fst).sub
        (hg.measurable.comp measurable_snd)).pow_const 2).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_one_iff_abs_le_one _).mpr (ha p.1 p.2)
  have he (u : I) : (∫ w : I, pairMomentDefect (g u) (g w)) =
      (∫ w : I, |g u - g w|) - ∫ w : I, (g u - g w) ^ 2 := by
    apply integral_sub
    · exact integrable_unit_bounded (continuous_abs.measurable.comp (measurable_const.sub hg.measurable))
        (fun w => ⟨abs_nonneg _, ha u w⟩)
    · exact integrable_unit_bounded ((measurable_const.sub hg.measurable).pow_const 2)
        (fun w => ⟨sq_nonneg _, (sq_le_one_iff_abs_le_one _).mpr (ha u w)⟩)
  simp_rw [he]
  rw [integral_sub hiabs.integral_prod_left hisq.integral_prod_left,
    integral_integral_abs_sub_of_antitone hg hb, integral_integral_sq_sub_unit hg.measurable hb]
  ring

theorem ae_constant_or_binary_of_pair_defect_zero {g : I → ℝ}
    (hb : ∀ u, g u ∈ Icc 0 1)
    (hz : ∀ᵐ u : I, ∀ᵐ w : I, pairMomentDefect (g u) (g w) = 0) :
    (∀ᵐ u : I, g u = ∫ w : I, g w) ∨ (∀ᵐ u : I, g u = 0 ∨ g u = 1) := by
  by_cases hbin : ∀ᵐ u : I, g u = 0 ∨ g u = 1
  · exact Or.inr hbin
  have hex : ∃ u : I, (∀ᵐ w : I, pairMomentDefect (g u) (g w) = 0) ∧ g u ≠ 0 ∧ g u ≠ 1 := by
    by_contra hn
    apply hbin
    filter_upwards [hz] with u hu
    by_contra he
    exact hn ⟨u, hu, (not_or.mp he).1, (not_or.mp he).2⟩
  obtain ⟨u, hu, hu0, hu1⟩ := hex
  have hp : 0 < g u := lt_of_le_of_ne (hb u).1 (Ne.symm hu0)
  have hq : g u < 1 := lt_of_le_of_ne (hb u).2 hu1
  have he : ∀ᵐ w : I, g w = g u := by
    filter_upwards [hu] with w hw
    have ha : |g u - g w| < 1 := abs_lt.mpr
      ⟨by linarith [(hb w).2], by linarith [(hb w).1]⟩
    have hzero : |g u - g w| = 0 := by
      unfold pairMomentDefect at hw
      nlinarith [sq_abs (g u - g w), abs_nonneg (g u - g w)]
    exact (sub_eq_zero.mp (abs_eq_zero.mp hzero)).symm
  have hm : (∫ w : I, g w) = g u := by simpa using integral_congr_ae he
  exact Or.inl (by simpa only [hm] using he)

theorem ae_constant_or_binary_of_moment_eq {g : I → ℝ} (hg : Antitone g)
    (hb : ∀ u, g u ∈ Icc 0 1)
    (he : (∫ u : I, g u ^ 2) = 2 * (∫ u : I, ∫ w in Iic u, g w) -
      (∫ u : I, g u) + (∫ u : I, g u) ^ 2) :
    (∀ᵐ u : I, g u = ∫ w : I, g w) ∨ (∀ᵐ u : I, g u = 0 ∨ g u = 1) := by
  have hz : (∫ u : I, ∫ w : I, pairMomentDefect (g u) (g w)) = 0 := by
    rw [integral_pairMomentDefect hg hb, he]
    ring
  have hn (u w : I) := (pairMomentDefect_mem_Icc (hb u) (hb w)).1
  have ha := (integral_eq_zero_iff_of_nonneg (fun u => integral_nonneg (hn u))
    (integrable_pairMomentDefect hg.measurable hb).integral_prod_left).mp hz
  apply ae_constant_or_binary_of_pair_defect_zero hb
  filter_upwards [ha] with u hu
  have hi : Integrable (fun w : I => pairMomentDefect (g u) (g w)) :=
    integrable_unit_bounded
      ((continuous_abs.measurable.comp (measurable_const.sub hg.measurable)).sub
        ((measurable_const.sub hg.measurable).pow_const 2))
      (fun w => pairMomentDefect_mem_Icc (hb u) (hb w))
  exact (integral_eq_zero_iff_of_nonneg (hn u) hi).mp hu

/-- An antitone binary function with mean v is the lower-interval indicator,
up to the unavoidable null-set ambiguity. -/
theorem ae_lower_indicator_of_antitone_binary {g : I → ℝ} (hg : Antitone g)
    (hb : ∀ u, g u ∈ Icc 0 1) (v : I) (hm : (∫ u : I, g u) = (v : ℝ))
    (hbin : ∀ᵐ u : I, g u = 0 ∨ g u = 1) :
    g =ᵐ[volume] (Iic v).indicator (fun _ => (1 : ℝ)) := by
  classical
  let e : I → ℝ := (Iic v).indicator (fun _ => 1)
  have hi := integrable_unit_bounded hg.measurable hb
  have he : Integrable e := (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have hesq : (fun u => e u ^ 2) = e := by
    funext u
    by_cases hu : u ∈ Iic v <;> simp [e, hu]
  have hge : (fun u => e u * g u) = (Iic v).indicator g := by
    funext u
    by_cases hu : u ∈ Iic v <;> simp [e, hu]
  have hgei : Integrable (fun u => e u * g u) := by
    rw [hge]
    exact hi.indicator measurableSet_Iic
  have heval : (∫ u : I, e u) = (v : ℝ) := by
    simp [e, integral_indicator measurableSet_Iic, integral_const, Measure.real,
      unitInterval.volume_Iic, ENNReal.toReal_ofReal v.property.1]
  have hsq : (∫ u : I, g u ^ 2) = (v : ℝ) := by
    rw [← hm]
    apply integral_congr_ae
    filter_upwards [hbin] with u hu
    rcases hu with hu | hu <;> simp only [hu] <;> norm_num
  have hlow : (∫ u : I, e u * g u) = (v : ℝ) := by
    have hl := integral_sq_le_lower_at_mean hg hb v hm
    rw [hsq, ← integral_indicator measurableSet_Iic, ← hge] at hl
    have hu := integral_mono hgei he (fun u => by
      change e u * g u ≤ e u
      by_cases hu : u ∈ Iic v
      · simpa only [e, indicator_of_mem hu, one_mul] using (hb u).2
      · simp only [e, indicator_of_notMem hu, zero_mul, le_refl])
    rw [heval] at hu
    exact le_antisymm hu hl
  have hsi : Integrable (fun u => g u ^ 2) := integrable_unit_bounded (hg.measurable.pow_const 2)
    (fun u => ⟨sq_nonneg _, by nlinarith [(hb u).1, (hb u).2]⟩)
  have hid : (fun u => (g u - e u) ^ 2) = fun u => g u ^ 2 - 2 * (e u * g u) + e u := by
    funext u
    have h := congrFun hesq u
    nlinarith
  have hdi : Integrable (fun u => g u ^ 2 - 2 * (e u * g u)) := hsi.sub (hgei.const_mul 2)
  have hzi : Integrable (fun u => (g u - e u) ^ 2) := by
    rw [hid]
    exact hdi.add he
  have hz : (∫ u : I, (g u - e u) ^ 2) = 0 := by
    rw [hid, integral_add hdi he, integral_sub hsi (hgei.const_mul 2),
      integral_const_mul, hsq, hlow, heval]
    ring
  have ha := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg _) hzi).mp hz
  filter_upwards [ha] with u hu
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hu)

/-- Equality in the moment inequality, with equality of functions interpreted
almost everywhere, as required for integral statements. -/
theorem moment_eq_iff_ae_constant_or_lower_indicator {g : I → ℝ} (hg : Antitone g)
    (hb : ∀ u, g u ∈ Icc 0 1) (v : I) (hm : (∫ u : I, g u) = (v : ℝ)) :
    (∫ u : I, g u ^ 2) = 2 * (∫ u : I, ∫ w in Iic u, g w) - (v : ℝ) + (v : ℝ) ^ 2 ↔
      (∀ᵐ u : I, g u = (v : ℝ)) ∨ g =ᵐ[volume] (Iic v).indicator (fun _ => (1 : ℝ)) := by
  classical
  constructor
  · intro he
    have he' : (∫ u : I, g u ^ 2) = 2 * (∫ u : I, ∫ w in Iic u, g w) -
        (∫ u : I, g u) + (∫ u : I, g u) ^ 2 := by simpa only [hm] using he
    rcases ae_constant_or_binary_of_moment_eq hg hb he' with hc | hb'
    · exact Or.inl (by simpa only [hm] using hc)
    · exact Or.inr (ae_lower_indicator_of_antitone_binary hg hb v hm hb')
  · intro he
    have hz : ∀ᵐ u : I, ∀ᵐ w : I, pairMomentDefect (g u) (g w) = 0 := by
      rcases he with hc | hi
      · filter_upwards [hc] with u hu
        filter_upwards [hc] with w hw
        simp [pairMomentDefect, hu, hw]
      · have hb' : ∀ᵐ u : I, g u = 0 ∨ g u = 1 := by
          filter_upwards [hi] with u hu
          rw [hu]
          by_cases hm' : u ∈ Iic v <;> simp [hm']
        filter_upwards [hb'] with u hu
        filter_upwards [hb'] with w hw
        rcases hu with hu | hu <;> rcases hw with hw | hw <;>
          norm_num [pairMomentDefect, hu, hw]
    have hzero : (∫ u : I, ∫ w : I, pairMomentDefect (g u) (g w)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hz] with u hu
      exact integral_eq_zero_of_ae hu
    rw [integral_pairMomentDefect hg hb, hm] at hzero
    linarith

end Verification
