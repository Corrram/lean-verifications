import Papers.Rockel2026XiBlest.SectionFormulas
import Verification.QuadraticMeanDerivative

/-! # The normalization derivative and all four substitutions in Lemma 4.2 -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiBlest

theorem normalizationMean_eq_clampedSquareMean (b : ℝ) : normalizationMean b=clampedSquareMean b := by
  funext q
  unfold normalizationMean clampedSquareMean
  simpa only [unitInterval.coe_symm_eq] using
    integral_unit_reflection (fun x : I => unitClamp (b*((x : ℝ)^2-q)))

theorem normalizationMean_hasDerivAt (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1) :
    HasDerivAt (normalizationMean b) (-b*(quadraticUpper b q-quadraticLower q)) q := by
  rw [normalizationMean_eq_clampedSquareMean]
  exact clampedSquareMean_hasDerivAt b q hb hq

/-- The unclamped part of an interior normalization section has positive width. -/
theorem quadratic_switch_strict (b q : ℝ) (hb : 0 < b)
    (hq : q ∈ Ioo (-1/b) 1) :
    quadraticLower q < quadraticUpper b q := by
  have hinv : 0 < 1/b := one_div_pos.mpr hb
  have hmax1 : max 0 q < 1 := max_lt (by norm_num) hq.2
  have hqlo : -(1/b) < q := by simpa only [neg_div] using hq.1
  have hmax2 : max 0 q < q+1/b :=
    max_lt (by linarith) (by linarith)
  unfold quadraticLower quadraticUpper
  apply lt_min
  · simpa using Real.sqrt_lt_sqrt (le_max_left 0 q) hmax1
  · exact Real.sqrt_lt_sqrt (le_max_left 0 q) hmax2

/-- At every interior response threshold, the normalization inverse stays
strictly inside its effective parameter interval. -/
theorem extremalQ_interior (b : ℝ) (hb : 0 < b) (v : I)
    (hv : (v : ℝ) ∈ Ioo (0 : ℝ) 1) :
    extremalQ b hb v ∈ Ioo (-1/b) 1 := by
  have ha := quadraticIntercept_mem b hb.le v
  have hq : extremalQ b hb v ∈ Icc (-1/b) (1 : ℝ) := by
    unfold extremalQ
    constructor
    · apply (div_le_div_iff_of_pos_right hb).mpr
      linarith [ha.2]
    · apply (div_le_one hb).mpr
      linarith [ha.1]
  have hqe : -b * extremalQ b hb v = quadraticIntercept b hb.le v := by
    unfold extremalQ
    field_simp
  have hm : normalizationMean b (extremalQ b hb v) = (v : ℝ) := by
    rw [normalizationMean_eq, hqe, quadraticIntercept_mean]
  obtain ⟨_, _, hleft, hright, _⟩ := normalizationMean_properties b hb
  constructor
  · by_contra! h
    have heq : extremalQ b hb v = -1/b := le_antisymm h hq.1
    rw [heq, hleft] at hm
    linarith [hv.2]
  · by_contra! h
    have heq : extremalQ b hb v = 1 := le_antisymm hq.2 h
    rw [heq, hright] at hm
    linarith [hv.1]

/-- The inverse normalization has a nonzero slope wherever the response is
strictly between zero and one. -/
theorem normalizationMean_deriv_neg_at_extremalQ (b : ℝ) (hb : 0 < b)
    (v : I) (hv : (v : ℝ) ∈ Ioo (0 : ℝ) 1) :
    deriv (normalizationMean b) (extremalQ b hb v) < 0 := by
  have hq := extremalQ_interior b hb v hv
  have hs := quadratic_switch_strict b (extremalQ b hb v) hb hq
  have hd := normalizationMean_hasDerivAt b (extremalQ b hb v) hb ⟨hq.1.le, hq.2.le⟩
  rw [hd.deriv]
  nlinarith [mul_pos hb (sub_pos.mpr hs)]

/-- A real-domain extension of the source normalization inverse. On the
interior of the unit interval it agrees with the manuscript's q(v). -/
noncomputable def extremalQExtension (b : ℝ) (hb : 0 < b) (v : ℝ) : ℝ :=
  extremalQ b hb ⟨unitClamp v, unitClamp_mem v⟩

theorem extremalQExtension_coe (b : ℝ) (hb : 0 < b) (v : I) :
    extremalQExtension b hb (v : ℝ) = extremalQ b hb v := by
  have hcl : unitClamp (v : ℝ) = (v : ℝ) := by
    unfold unitClamp
    rw [max_eq_right v.property.1, min_eq_right v.property.2]
  unfold extremalQExtension
  congr 1
  apply Subtype.ext
  exact hcl

private theorem extremalQExtension_continuous (b : ℝ) (hb : 0 < b) :
    Continuous (extremalQExtension b hb) := by
  have hc : Continuous (fun v : ℝ => unitClamp v) := by
    unfold unitClamp
    fun_prop
  have hmap : Continuous (fun v : ℝ => (⟨unitClamp v, unitClamp_mem v⟩ : I)) :=
    hc.subtype_mk _
  exact (extremalQ_continuous b hb).comp hmap

private theorem normalizationMean_extremalQExtension (b : ℝ) (hb : 0 < b)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) :
    normalizationMean b (extremalQExtension b hb v) = v := by
  have hcl : unitClamp v = v := by
    unfold unitClamp
    rw [max_eq_right hv.1, min_eq_right hv.2]
  let w : I := ⟨v, hv⟩
  have he : extremalQExtension b hb v = extremalQ b hb w := by
    unfold extremalQExtension
    congr 1
    apply Subtype.ext
    exact hcl
  rw [he, normalizationMean_eq]
  have hqe : -b * extremalQ b hb w = quadraticIntercept b hb.le w := by
    unfold extremalQ
    field_simp
  rw [hqe, quadraticIntercept_mean]

/-- The manuscript's inverse normalization parameter is differentiable at
every interior response threshold, with an explicit reciprocal slope. -/
theorem extremalQExtension_hasDerivAt (b : ℝ) (hb : 0 < b)
    (v : ℝ) (hv : v ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (extremalQExtension b hb)
      (-b * (quadraticUpper b (extremalQExtension b hb v) -
        quadraticLower (extremalQExtension b hb v)))⁻¹ v := by
  let w : I := ⟨v, ⟨hv.1.le, hv.2.le⟩⟩
  have hcl : unitClamp v = v := by
    unfold unitClamp
    rw [max_eq_right hv.1.le, min_eq_right hv.2.le]
  have he : extremalQExtension b hb v = extremalQ b hb w := by
    unfold extremalQExtension
    congr 1
    apply Subtype.ext
    exact hcl
  have hq := extremalQ_interior b hb w hv
  have hd := normalizationMean_hasDerivAt b (extremalQExtension b hb v) hb
    (show extremalQExtension b hb v ∈ Icc (-1/b) 1 by
      rw [he]
      exact ⟨hq.1.le, hq.2.le⟩)
  have hne : -b * (quadraticUpper b (extremalQExtension b hb v) -
        quadraticLower (extremalQExtension b hb v)) ≠ 0 := by
    apply ne_of_lt
    rw [he]
    nlinarith [mul_pos hb (sub_pos.mpr (quadratic_switch_strict b _ hb hq))]
  apply HasDerivAt.of_local_left_inverse
    (extremalQExtension_continuous b hb).continuousAt hd hne
  filter_upwards [isOpen_Ioo.mem_nhds hv] with y hy
  exact normalizationMean_extremalQExtension b hb y ⟨hy.1.le, hy.2.le⟩

/-- The coefficient -b q'(v) in the revised density formula equals the
reciprocal length of the unclamped conditional-density band. -/
theorem extremalQExtension_density_coefficient (b : ℝ) (hb : 0 < b)
    (v : I) (hv : (v : ℝ) ∈ Ioo (0 : ℝ) 1) :
    -b * deriv (extremalQExtension b hb) (v : ℝ) =
      1 / (quadraticUpper b (extremalQ b hb v) -
        quadraticLower (extremalQ b hb v)) := by
  have hq := extremalQ_interior b hb v hv
  have hs := quadratic_switch_strict b (extremalQ b hb v) hb hq
  have hlen : quadraticUpper b (extremalQ b hb v) -
      quadraticLower (extremalQ b hb v) ≠ 0 := ne_of_gt (sub_pos.mpr hs)
  rw [(extremalQExtension_hasDerivAt b hb (v : ℝ) hv).deriv,
    extremalQExtension_coe b hb v]
  field_simp

/-- The active set in the clamped-square normalization has exact Lebesgue
length given by the difference of its switch points. -/
theorem quadratic_active_interval_integral (b q : ℝ) (hb : 0 < b)
    (hq : q ∈ Icc (-1/b) 1) :
    (∫ x : I, if 0 < b*((x : ℝ)^2-q) ∧
        b*((x : ℝ)^2-q) < 1 then (1 : ℝ) else 0) =
      quadraticUpper b q - quadraticLower q := by
  have he := (clampedSquareMean_hasDerivAt_integral b q hb).unique
    (clampedSquareMean_hasDerivAt b q hb hq)
  have hf : (fun x : I => if 0 < b*((x : ℝ)^2-q) ∧
        b*((x : ℝ)^2-q) < 1 then -b else 0) =
      fun x : I => -b * (if 0 < b*((x : ℝ)^2-q) ∧
        b*((x : ℝ)^2-q) < 1 then (1 : ℝ) else 0) := by
    funext x
    split_ifs <;> ring
  rw [hf, integral_const_mul] at he
  exact (mul_left_cancel₀ (by linarith : -b ≠ 0)) he

/-- The reflected closed active strip has the same length: switching
equalities occur only on two null square-level sets. -/
theorem quadratic_closed_active_reflected_integral (b q : ℝ) (hb : 0 < b)
    (hq : q ∈ Icc (-1/b) 1) :
    (∫ u : I, if 0 ≤ b*((1-(u : ℝ))^2-q) ∧
        b*((1-(u : ℝ))^2-q) ≤ 1 then (1 : ℝ) else 0) =
      quadraticUpper b q - quadraticLower q := by
  have hsq0 := unitInterval.measurePreserving_symm.quasiMeasurePreserving.ae
    (square_ae_ne q)
  have hsq1 := unitInterval.measurePreserving_symm.quasiMeasurePreserving.ae
    (square_ae_ne (q+1/b))
  have hae : (fun u : I => if 0 ≤ b*((1-(u : ℝ))^2-q) ∧
        b*((1-(u : ℝ))^2-q) ≤ 1 then (1 : ℝ) else 0) =ᵐ[volume]
      (fun u : I => if 0 < b*((1-(u : ℝ))^2-q) ∧
        b*((1-(u : ℝ))^2-q) < 1 then (1 : ℝ) else 0) := by
    filter_upwards [hsq0, hsq1] with u h0 h1
    simp only [unitInterval.coe_symm_eq] at h0 h1
    let z := b*((1-(u : ℝ))^2-q)
    have hz0 : z ≠ 0 := mul_ne_zero hb.ne' (sub_ne_zero.mpr h0)
    have hz1 : z ≠ 1 := by
      intro he
      apply h1
      have hdiv : (1-(u : ℝ))^2-q=1/b :=
        (eq_div_iff hb.ne').mpr (by nlinarith [he])
      linarith
    have he : (0 ≤ z ∧ z ≤ 1) ↔ (0 < z ∧ z < 1) := by
      constructor
      · rintro ⟨hlo,hhi⟩
        exact ⟨lt_of_le_of_ne hlo (Ne.symm hz0),
          lt_of_le_of_ne hhi hz1⟩
      · rintro ⟨hlo,hhi⟩
        exact ⟨hlo.le,hhi.le⟩
    change (if 0 ≤ z ∧ z ≤ 1 then (1 : ℝ) else 0) =
      (if 0 < z ∧ z < 1 then (1 : ℝ) else 0)
    simp only [he]
  rw [integral_congr_ae hae]
  have hr := integral_unit_reflection
    (fun x : I => if 0 < b*((x : ℝ)^2-q) ∧
        b*((x : ℝ)^2-q) < 1 then (1 : ℝ) else 0)
  simp only [unitInterval.coe_symm_eq] at hr
  exact hr.trans (quadratic_active_interval_integral b q hb hq)

/-- Away from the unit-square edges, the strict clamped-square active
condition is precisely the interval between the two switching points. -/
theorem quadratic_active_iff_switch (b q t : ℝ) (hb : 0 < b)
    (hq : q ∈ Icc (-1/b) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (0 < b*(t^2-q) ∧ b*(t^2-q) < 1) ↔
      (quadraticLower q < t ∧ t < quadraticUpper b q) := by
  have hR : 0 ≤ q+1/b := by
    have hqlo : -(1/b) ≤ q := by simpa only [neg_div] using hq.1
    linarith
  have hrsq : (quadraticLower q)^2 = max 0 q :=
    Real.sq_sqrt (le_max_left _ _)
  have hRsq := Real.sq_sqrt hR
  have hrnonneg : 0 ≤ quadraticLower q := Real.sqrt_nonneg _
  constructor
  · rintro ⟨h0,h1⟩
    have hqlo : q < t^2 := by nlinarith
    have hqhi : t^2 < q+1/b := by
      have hlt : t^2-q < 1/b :=
        (lt_div_iff₀ hb).mpr (by nlinarith [h1])
      linarith
    constructor
    · rcases le_total 0 q with hq0 | hq0
      · rw [max_eq_right hq0] at hrsq
        by_contra h
        have hle : t ≤ quadraticLower q := le_of_not_gt h
        nlinarith [mul_nonneg (sub_nonneg.mpr hle)
          (add_nonneg hrnonneg ht.1.le)]
      · rw [max_eq_left hq0] at hrsq
        have hr0 : quadraticLower q = 0 := by nlinarith [sq_nonneg (quadraticLower q)]
        rw [hr0]
        exact ht.1
    · apply lt_min ht.2
      nlinarith [Real.sqrt_nonneg (q+1/b)]
  · rintro ⟨h0,h1⟩
    have htR : t < Real.sqrt (q+1/b) := h1.trans_le (min_le_right _ _)
    have hsq : (quadraticLower q)^2 < t^2 := by
      have hprod := mul_pos (sub_pos.mpr h0)
        (add_pos_of_nonneg_of_pos hrnonneg ht.1)
      nlinarith [hprod]
    have hqlo : q < t^2 := by
      rw [hrsq] at hsq
      exact (le_max_right (0 : ℝ) q).trans_lt hsq
    have hqhi : t^2 < q+1/b := by
      have hprod := mul_pos (sub_pos.mpr htR)
        (add_pos_of_pos_of_nonneg ht.1 (Real.sqrt_nonneg (q+1/b)))
      nlinarith [hprod]
    have hlt : b*(t^2-q) < 1 := by
      have hh : t^2-q < 1/b := by linarith
      have hmul := (lt_div_iff₀ hb).mp hh
      nlinarith [hmul]
    exact ⟨mul_pos hb (sub_pos.mpr hqlo), hlt⟩

/-- Lemma 4.2(i), including the zero-radius endpoint. -/
theorem substitution_upper (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1)
    (hqneg : q ≤ 0) (hR : Real.sqrt (q+1/b) ≤ 1) :
    -(2*Real.sqrt (q+1/b))*deriv (normalizationMean b) q=2*b*(Real.sqrt (q+1/b))^2 := by
  rw [(normalizationMean_hasDerivAt b q hb hq).deriv]
  simp only [quadraticUpper,quadraticLower,max_eq_left hqneg,Real.sqrt_zero,min_eq_right hR,sub_zero]
  ring

/-- Lemma 4.2(ii). -/
theorem substitution_unclamped (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1)
    (hqneg : q ≤ 0) (hR : 1 ≤ Real.sqrt (q+1/b)) :
    -(2*Real.sqrt (q+1/b))*deriv (normalizationMean b) q=2*b*Real.sqrt (q+1/b) := by
  rw [(normalizationMean_hasDerivAt b q hb hq).deriv]
  simp only [quadraticUpper,quadraticLower,max_eq_left hqneg,Real.sqrt_zero,min_eq_left hR,sub_zero]
  ring

/-- Lemma 4.2(iii), including q=0. -/
theorem substitution_double (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1)
    (hqpos : 0 ≤ q) (hR : Real.sqrt (q+1/b) ≤ 1) :
    -(2*Real.sqrt (q+1/b))*deriv (normalizationMean b) q=
      1+b*(Real.sqrt (q+1/b)-Real.sqrt q)^2 := by
  rw [(normalizationMean_hasDerivAt b q hb hq).deriv]
  simp only [quadraticUpper,quadraticLower,max_eq_right hqpos,min_eq_right hR]
  have hs := Real.sq_sqrt hqpos
  have hS := Real.sq_sqrt (show 0 ≤ q+1/b by positivity)
  have hi : b*(1/b)=1 := by field_simp
  have hd : (Real.sqrt (q+1/b))^2-(Real.sqrt q)^2=1/b := by linarith
  nlinarith [congrArg (fun x : ℝ => b*x) hd]

/-- Lemma 4.2(iv), including both boundary radii. -/
theorem substitution_lower (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1)
    (hqpos : 0 ≤ q) (hR : 1 ≤ Real.sqrt (q+1/b)) :
    -(2*Real.sqrt q)*deriv (normalizationMean b) q=2*b*Real.sqrt q*(1-Real.sqrt q) := by
  rw [(normalizationMean_hasDerivAt b q hb hq).deriv]
  simp only [quadraticUpper,quadraticLower,max_eq_right hqpos,min_eq_left hR]
  ring

end Papers.Rockel2026XiBlest
