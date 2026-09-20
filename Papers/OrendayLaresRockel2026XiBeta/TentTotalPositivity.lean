import Papers.OrendayLaresRockel2026XiBeta.TentDensity
import Verification.AETotalPositivity

/-! # Proposition 3(vii): TP2 and RR2 of the tent density

The necessity arguments use positive-length intervals, so isolated values on
strip boundaries cannot repair a failed minor inequality.
-/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

private theorem tentStart_le_half (r : I) : tentStart r ≤ Copula.unitHalf := by
  change (1 - (r : ℝ)) / 2 ≤ (1 / 2 : ℝ)
  linarith [r.property.1]

private theorem half_le_tentEnd (r : I) : Copula.unitHalf ≤ tentEnd r := by
  change (1 / 2 : ℝ) ≤ (1 + (r : ℝ)) / 2
  linarith [r.property.1]

private theorem tentSlope_left (r v : I) (ha : tentStart r < v) (hv : v ≤ Copula.unitHalf) :
    tentSlope r v = 1 := by
  by_cases hr : r = 1
  · simp [tentSlope, hr, medianSign, hv]
  · norm_num [tentSlope, hr, lowerStep, not_le.mpr ha, hv, hv.trans (half_le_tentEnd r)]

private theorem tentSlope_right (r v : I) (hv : Copula.unitHalf < v) (hz : v ≤ tentEnd r) :
    tentSlope r v = -1 := by
  by_cases hr : r = 1
  · simp [tentSlope, hr, medianSign, not_le.mpr hv]
  · norm_num [tentSlope, hr, lowerStep, not_le.mpr hv,
      not_le.mpr ((tentStart_le_half r).trans_lt hv), hz]

private theorem tentSlope_outside (r v : I) (hr : r ≠ 1) (hv : v ≤ tentStart r) :
    tentSlope r v = 0 := by
  norm_num [tentSlope, hr, lowerStep, hv, hv.trans (tentStart_le_half r),
    (hv.trans (tentStart_le_half r)).trans (half_le_tentEnd r)]

private theorem tentSlope_zero (v : I) : tentSlope 0 v = 0 := by
  have ha : tentStart 0 = Copula.unitHalf := by apply Subtype.ext; norm_num [tentStart, Copula.unitHalf]
  have hz : tentEnd 0 = Copula.unitHalf := by apply Subtype.ext; norm_num [tentEnd, Copula.unitHalf]
  simp only [tentSlope, zero_ne_one, ite_false, ha, hz]
  ring

private theorem tentSlope_ae_antitone_iff (r : I) (s : ℝ) (hs : s ≠ 0) :
    (∀ᵐ v₁ : I, ∀ᵐ v₂ : I, v₁ ≤ v₂ → s * tentSlope r v₂ ≤ s * tentSlope r v₁) ↔
      r = 0 ∨ (r = 1 ∧ 0 ≤ s) := by
  by_cases hr0 : r = 0
  · subst r
    simp only [tentSlope_zero, mul_zero, le_refl, implies_true, Filter.eventually_true, true_or]
  have hrp : 0 < (r : ℝ) := lt_of_le_of_ne r.property.1 (fun h => hr0 (Subtype.ext h.symm))
  have hal : tentStart r < Copula.unitHalf := by change (1 - (r : ℝ)) / 2 < (1 / 2 : ℝ); linarith
  have hzr : Copula.unitHalf < tentEnd r := by change (1 / 2 : ℝ) < (1 + (r : ℝ)) / 2; linarith
  constructor
  · intro h
    obtain ⟨v₁, hv₁, h₁⟩ := exists_mem_Ioo_of_ae hal h
    obtain ⟨v₂, hv₂, h₂⟩ := exists_mem_Ioo_of_ae hzr h₁
    have hi := h₂ (hv₁.2.le.trans hv₂.1.le)
    rw [tentSlope_left r v₁ hv₁.1 hv₁.2.le, tentSlope_right r v₂ hv₂.1 hv₂.2.le] at hi
    have hs0 : 0 ≤ s := by linarith
    refine Or.inr ⟨?_, hs0⟩
    by_contra hr1
    have ha0 : (0 : I) < tentStart r := by
      have hrlt : (r : ℝ) < 1 := lt_of_le_of_ne r.property.2 (fun h => hr1 (Subtype.ext h))
      change (0 : ℝ) < (1 - (r : ℝ)) / 2
      linarith
    obtain ⟨w₁, hw₁, h₃⟩ := exists_mem_Ioo_of_ae ha0 h
    obtain ⟨w₂, hw₂, h₄⟩ := exists_mem_Ioo_of_ae hal h₃
    have hj := h₄ (hw₁.2.le.trans hw₂.1.le)
    rw [tentSlope_outside r w₁ hr1 hw₁.2.le, tentSlope_left r w₂ hw₂.1 hw₂.2.le] at hj
    exact hs (by linarith)
  · rintro (h | ⟨rfl, hs0⟩)
    · exact (hr0 h).elim
    · filter_upwards [] with v₁
      filter_upwards [] with v₂
      intro hv
      simp only [tentSlope, ite_true]
      exact mul_le_mul_of_nonneg_left (medianSign_antitone hv) hs0

theorem tentDensity_ae_tp2_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    HasAEOrderedMinors 1 (fun u v => tentDensity b hb ![u, v]) ↔ b = 0 ∨ b = 1 := by
  change HasAEOrderedMinors 1 (fun u v => 1 + medianSign u * signedTentSlope b hb v) ↔ _
  rw [stepDensity_ae_minors_iff]
  by_cases hn : 0 ≤ b
  · simp only [signedTentSlope, dite_eq_left hn]
    rw [tentSlope_ae_antitone_iff _ 1 (by norm_num)]
    simp [Subtype.ext_iff]
  · simp only [signedTentSlope, dite_eq_right hn]
    have he (v : I) : (1 : ℝ) * -tentSlope ⟨-b, by constructor <;> linarith [hb.1]⟩ v =
        (-1 : ℝ) * tentSlope ⟨-b, by constructor <;> linarith [hb.1]⟩ v := by ring
    simp_rw [he]
    rw [tentSlope_ae_antitone_iff _ (-1) (by norm_num)]
    simp [Subtype.ext_iff, show b ≠ 0 by linarith, show b ≠ 1 by linarith]

private theorem signedTentSlope_neg (b : ℝ) (hb : b ∈ Icc (-1) 1)
    (hn : -b ∈ Icc (-1) 1) (v : I) :
    signedTentSlope (-b) hn v = -signedTentSlope b hb v := by
  rcases lt_trichotomy b 0 with h | rfl | h
  · simp only [signedTentSlope, dite_eq_left (by linarith : 0 ≤ -b),
      dite_eq_right (not_le.mpr h), neg_neg]
  · simp only [signedTentSlope, neg_zero, le_refl, dite_true]
    change tentSlope (0 : I) v = -tentSlope (0 : I) v
    rw [tentSlope_zero]
    norm_num
  · simp only [signedTentSlope, dite_eq_right (by linarith : ¬0 ≤ -b),
      dite_eq_left h.le, neg_neg]

theorem tentDensity_ae_rr2_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    HasAEOrderedMinors (-1) (fun u v => tentDensity b hb ![u, v]) ↔ b = 0 ∨ b = -1 := by
  have hn : -b ∈ Icc (-1) 1 := by constructor <;> linarith [hb.1, hb.2]
  have h := tentDensity_ae_tp2_iff (-b) hn
  change HasAEOrderedMinors 1 (fun u v => 1 + medianSign u * signedTentSlope (-b) hn v) ↔ _ at h
  change HasAEOrderedMinors (-1) (fun u v => 1 + medianSign u * signedTentSlope b hb v) ↔ _
  rw [stepDensity_ae_minors_iff] at h ⊢
  simp only [signedTentSlope_neg b hb hn, one_mul, neg_one_mul] at h ⊢
  convert h using 1
  constructor <;> rintro (h | h)
  all_goals first | exact Or.inl (by linarith) | exact Or.inr (by linarith)

private theorem signedTentSlope_zero (hb : (0 : ℝ) ∈ Icc (-1) 1) (v : I) :
    signedTentSlope 0 hb v = 0 := by
  simp only [signedTentSlope, le_refl, dite_true]
  exact tentSlope_zero v

private theorem signedTentSlope_one (hb : (1 : ℝ) ∈ Icc (-1) 1) (v : I) :
    signedTentSlope 1 hb v = medianSign v := by
  simp only [signedTentSlope, show (0 : ℝ) ≤ 1 by norm_num, dite_true]
  change tentSlope (1 : I) v = medianSign v
  simp [tentSlope]

private theorem signedTentSlope_neg_one (hb : (-1 : ℝ) ∈ Icc (-1) 1) (v : I) :
    signedTentSlope (-1) hb v = -medianSign v := by
  simp only [signedTentSlope, show ¬(0 : ℝ) ≤ -1 by norm_num, dite_false]
  simp only [neg_neg]
  change -tentSlope (1 : I) v = -medianSign v
  simp [tentSlope]

theorem tentDensity_tp2_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    IsMTP2 (tentDensity b hb) ↔ b = 0 ∨ b = 1 := by
  constructor
  · intro h
    apply (tentDensity_ae_tp2_iff b hb).mp
    have ht := (Copula.isMTP2_fin_two_iff _).mp h
    filter_upwards [] with u₁
    filter_upwards [] with u₂
    filter_upwards [] with v₁
    filter_upwards [] with v₂
    intro hu hv
    simpa only [one_mul] using sub_nonneg.mpr (ht u₁ u₂ v₁ v₂ hu hv)
  · rintro (rfl | rfl)
    · have he : tentDensity 0 hb = fun _ => (1 : ℝ) := by
        funext x
        simp [tentDensity, signedTentSlope_zero]
      rw [he]
      exact isMTP2_const 1
    · apply (Copula.isMTP2_fin_two_iff _).mpr
      intro u₁ u₂ v₁ v₂ hu hv
      have h := stepDensity_ordered_minors (s := 1) (d := medianSign)
        (by simpa only [one_mul] using medianSign_antitone) u₁ u₂ v₁ v₂ hu hv
      simpa only [tentDensity, signedTentSlope_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, sub_nonneg] using h

theorem tentDensity_rr2_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    IsRR2 (fun u v => tentDensity b hb ![u, v]) ↔ b = 0 ∨ b = -1 := by
  constructor
  · intro h
    exact (tentDensity_ae_rr2_iff b hb).mp (aeOrderedMinors_of_rr2 h)
  · rintro (rfl | rfl)
    · intro u₁ u₂ v₁ v₂ _ _
      simp [tentDensity, signedTentSlope_zero]
    · intro u₁ u₂ v₁ v₂ hu hv
      have h := stepDensity_ordered_minors (s := -1) (d := fun v => -medianSign v)
        (by simpa only [neg_mul_neg, one_mul] using medianSign_antitone) u₁ u₂ v₁ v₂ hu hv
      simp only [neg_one_mul, neg_nonneg, sub_nonpos] at h
      simpa only [tentDensity, signedTentSlope_neg_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one] using h

private theorem measurable_tentDensity (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    Measurable (tentDensity b hb) :=
  measurable_const.add ((measurable_medianSign.comp (measurable_pi_apply 0)).mul
    ((signedTentSlope_measurable b hb).comp (measurable_pi_apply 1)))

private theorem tentDensity_nonneg (b : ℝ) (hb : b ∈ Icc (-1) 1) (x : Fin 2 → I) :
    0 ≤ tentDensity b hb x := by
  rcases tentDensity_values b hb x with h | h | h <;> rw [h] <;> norm_num

/-- The classification is unchanged for any measurable nonnegative density version. -/
theorem leftBoundary_density_version_ae_minors_iff (b : ℝ) (hb : b ∈ Icc (-1) 1)
    {f : (Fin 2 → I) → ℝ} (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (he : (leftBoundary b hb).toMeasure =
      (volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal (f x))) (s : ℝ) :
    HasAEOrderedMinors s (fun u v => f ![u, v]) ↔
      HasAEOrderedMinors s (fun u v => tentDensity b hb ![u, v]) := by
  apply aeOrderedMinors_congr
  apply ae_curry_of_ae_eq
  exact density_ae_eq hf (measurable_tentDensity b hb) hn (tentDensity_nonneg b hb)
    (he.symm.trans (leftBoundary_density b hb))

theorem leftBoundary_hasMTP2Density_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).HasMTP2Density ↔ b = 0 ∨ b = 1 := by
  constructor
  · rintro ⟨f, hf, hn, ht, he⟩
    apply (tentDensity_ae_tp2_iff b hb).mp
    apply (leftBoundary_density_version_ae_minors_iff b hb hf hn he 1).mp
    exact aeOrderedMinors_of_tp2 ((Copula.isMTP2_fin_two_iff f).mp ht)
  · intro h
    exact ⟨tentDensity b hb, measurable_tentDensity b hb, tentDensity_nonneg b hb,
      (tentDensity_tp2_iff b hb).mpr h, leftBoundary_density b hb⟩

theorem leftBoundary_hasRR2Density_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    HasRR2Density (leftBoundary b hb) ↔ b = 0 ∨ b = -1 := by
  constructor
  · rintro ⟨f, hf, hn, ht, he⟩
    apply (tentDensity_ae_rr2_iff b hb).mp
    apply (leftBoundary_density_version_ae_minors_iff b hb hf hn he (-1)).mp
    exact aeOrderedMinors_of_rr2 ht
  · intro h
    exact ⟨tentDensity b hb, measurable_tentDensity b hb, tentDensity_nonneg b hb,
      (tentDensity_rr2_iff b hb).mpr h, leftBoundary_density b hb⟩

end Papers.OrendayLaresRockel2026XiBeta
