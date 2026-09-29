import Papers.OrendayLaresRockel2026XiBeta.TentV2Basic
import Copula.UnitInterval

/-! # The tent is the unique minimizer (introduction and Remark 3.3)

Among all `1`-Lipschitz functions `g : [0,1] → ℝ` with `g(1/2) = b/2`, the signed tent `g_b`
is pointwise smallest in absolute value and is the unique minimizer of `∫ g²`,
with minimal value `|b|³/12`. This is the variational statement behind (1.4).
-/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

theorem continuous_tentG (b : ℝ) : Continuous (tentG b) := by
  unfold tentG; exact continuous_const.mul (continuous_medianTent _)

/-- Pointwise: `|g_b(v)| ≤ |g(v)|` for every `1`-Lipschitz `g` with `g(1/2) = b/2`. -/
theorem abs_tentG_le_abs {b : ℝ} (g : I → ℝ) (hg : ∀ v w : I, |g v - g w| ≤ |(v : ℝ) - w|)
    (h2 : g Copula.unitHalf = b / 2) (v : I) : |tentG b v| ≤ |g v| := by
  have hl := hg v Copula.unitHalf
  have hu : ((Copula.unitHalf : I) : ℝ) = 1 / 2 := rfl
  rw [hu, h2] at hl
  have hgv : |b| / 2 - |(v : ℝ) - 1 / 2| ≤ |g v| := by
    have h3 : |b / 2| ≤ |g v| + |g v - b / 2| := by
      calc |b / 2| = |g v - (g v - b / 2)| := by ring_nf
        _ ≤ |g v| + |g v - b / 2| := abs_sub _ _
    rw [abs_div, abs_two] at h3
    linarith
  unfold tentG
  rw [abs_mul]
  by_cases hb : b = 0
  · subst hb; simp [sgn_zero]
  · have : |sgn b| = 1 := by
      rcases lt_or_gt_of_ne hb with h | h
      · rw [sgn_of_neg h]; norm_num
      · rw [sgn_of_pos h]; norm_num
    have hm : |medianTent |b| v| = medianTent |b| v := abs_of_nonneg (le_max_left _ _)
    rw [this, one_mul, hm]
    exact max_le (abs_nonneg _) hgv

theorem tentG_sq_le {b : ℝ} (g : I → ℝ) (hg : ∀ v w : I, |g v - g w| ≤ |(v : ℝ) - w|)
    (h2 : g Copula.unitHalf = b / 2) (v : I) : tentG b v ^ 2 ≤ g v ^ 2 :=
  sq_le_sq.mpr (abs_tentG_le_abs g hg h2 v)

/-- The signed tent minimizes `∫ g²` among `1`-Lipschitz functions with `g(1/2) = b/2`,
and the minimal value is `|b|³/12`. -/
theorem tent_minimizes {b : ℝ} (hb : b ∈ Icc (-1 : ℝ) 1) (g : I → ℝ)
    (hg : ∀ v w : I, |g v - g w| ≤ |(v : ℝ) - w|) (h2 : g Copula.unitHalf = b / 2) :
    |b| ^ 3 / 12 ≤ ∫ v : I, g v ^ 2 := by
  have hgc : Continuous g :=
    (LipschitzWith.of_dist_le_mul (K := 1) (fun v w => by
      simpa [Real.dist_eq, Subtype.dist_eq] using hg v w)).continuous
  calc |b| ^ 3 / 12 = ∫ v : I, tentG b v ^ 2 := (integral_tentG_sq b hb).symm
    _ ≤ ∫ v : I, g v ^ 2 := integral_mono
        (Copula.integrable_continuous_unit volume (((continuous_tentG b).comp continuous_subtype_val).pow 2))
        (Copula.integrable_continuous_unit volume ((hgc.comp continuous_id).pow 2))
        (fun v => tentG_sq_le g hg h2 v)

theorem continuous_of_lipschitz_unit (g : I → ℝ) (hg : ∀ v w : I, |g v - g w| ≤ |(v : ℝ) - w|) :
    Continuous g :=
  (LipschitzWith.of_dist_le_mul (K := 1) (fun v w => by
    simpa [Real.dist_eq, Subtype.dist_eq] using hg v w)).continuous

/-- Uniqueness of the minimizer: equality forces `g = g_b` on `[0,1]`. -/
theorem tent_minimizer_unique {b : ℝ} (hb : b ∈ Icc (-1 : ℝ) 1) (g : I → ℝ)
    (hg : ∀ v w : I, |g v - g w| ≤ |(v : ℝ) - w|) (h2 : g Copula.unitHalf = b / 2)
    (heq : ∫ v : I, g v ^ 2 = |b| ^ 3 / 12) : ∀ v : I, g v = tentG b v := by
  have hgc := continuous_of_lipschitz_unit g hg
  have hti : Continuous (fun v : I => tentG b v) := (continuous_tentG b).comp continuous_subtype_val
  have hsq : ∀ v : I, g v ^ 2 = tentG b v ^ 2 := by
    have hf : Continuous (fun v : I => g v ^ 2 - tentG b v ^ 2) := (hgc.pow 2).sub (hti.pow 2)
    have hnn : (0 : I → ℝ) ≤ fun v => g v ^ 2 - tentG b v ^ 2 :=
      fun v => sub_nonneg.mpr (tentG_sq_le g hg h2 v)
    have hint : ∫ v : I, (g v ^ 2 - tentG b v ^ 2) = 0 := by
      have hi1 : Integrable (fun v : I => g v ^ 2) :=
        Copula.integrable_continuous_unit volume (hgc.pow 2)
      have hi2 : Integrable (fun v : I => tentG b v ^ 2) :=
        Copula.integrable_continuous_unit volume (hti.pow 2)
      rw [integral_sub hi1 hi2, heq, integral_tentG_sq b hb]
      ring
    have hae := (integral_eq_zero_iff_of_nonneg hnn
      (Copula.integrable_continuous_unit volume hf)).mp hint
    have hz : (fun v : I => g v ^ 2 - tentG b v ^ 2) = 0 :=
      (Continuous.ae_eq_iff_eq (volume : Measure I) hf continuous_const).mp hae
    intro v
    have := congrFun hz v
    simp only [Pi.zero_apply] at this
    linarith
  intro v
  by_cases hb0 : b = 0
  · subst hb0
    rw [tentG_zero]
    have := hsq v
    rw [tentG_zero] at this
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (by simpa using this)
  have hbpos : 0 < |b| := abs_pos.mpr hb0
  by_cases hv : |(v : ℝ) - 1 / 2| < |b| / 2
  · -- inside the support of the tent
    have hm : 0 < medianTent |b| v := by
      unfold medianTent
      exact lt_max_of_lt_right (by linarith)
    have hsg : sgn b * b = |b| := by
      rcases lt_or_gt_of_ne hb0 with h | h
      · rw [sgn_of_neg h, abs_of_neg h]; ring
      · rw [sgn_of_pos h, abs_of_pos h]; ring
    have hsq1 : sgn b * sgn b = 1 := by
      rcases lt_or_gt_of_ne hb0 with h | h
      · rw [sgn_of_neg h]; norm_num
      · rw [sgn_of_pos h]; norm_num
    -- nonvanishing of g on the support
    have hne : ∀ w : I, |(w : ℝ) - 1 / 2| < |b| / 2 → g w ≠ 0 := by
      intro w hw h0
      have := hsq w
      rw [h0] at this
      have hmw : 0 < medianTent |b| w := by
        unfold medianTent
        exact lt_max_of_lt_right (by linarith)
      have : tentG b w ^ 2 = (sgn b * sgn b) * medianTent |b| w ^ 2 := by unfold tentG; ring
      rw [hsq1] at this
      nlinarith [this, hsq w, h0]
    -- sign of g
    have hsign : 0 < g v * b := by
      by_contra hcon
      have hcon' : g v * b ≤ 0 := not_lt.mp hcon
      have hgv0 : g v ≠ 0 := hne v hv
      have hneg : g v * (b / 2) < 0 := by
        rcases lt_or_gt_of_ne hgv0 with h | h <;> rcases lt_or_gt_of_ne hb0 with h' | h' <;>
          nlinarith
      let g' : ℝ → ℝ := fun t => g (Set.projIcc 0 1 zero_le_one t)
      have hg'c : Continuous g' := hgc.comp continuous_projIcc
      have hg'half : g' (1 / 2) = b / 2 := by
        change g (Set.projIcc 0 1 zero_le_one (1 / 2)) = _
        rw [← h2]
        congr 1
        apply Subtype.ext
        rw [Set.projIcc_of_mem _ (⟨by norm_num, by norm_num⟩ : (1 / 2 : ℝ) ∈ Set.Icc 0 1)]
        rfl
      have hg'v : g' v = g v := by
        change g (Set.projIcc 0 1 zero_le_one (v : ℝ)) = _
        rw [Set.projIcc_val]
      have h0mem : (0 : ℝ) ∈ Set.uIcc (g' (1 / 2)) (g' v) := by
        rw [hg'half, hg'v, Set.mem_uIcc]
        rcases le_total (b / 2) 0 with h | h
        · left; exact ⟨h, by nlinarith⟩
        · right; exact ⟨by nlinarith, h⟩
      obtain ⟨w, hw, hw0⟩ := intermediate_value_uIcc hg'c.continuousOn h0mem
      have hwI : w ∈ Set.Icc (0 : ℝ) 1 := by
        have h1 : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
        exact Set.uIcc_subset_Icc h1 v.property hw
      have hwd : |w - 1 / 2| < |b| / 2 := by
        have : |w - 1 / 2| ≤ |(v : ℝ) - 1 / 2| := by
          rw [Set.mem_uIcc] at hw
          rw [abs_le]
          rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [abs_of_nonneg (by linarith [h1] : (0 : ℝ) ≤ (v : ℝ) - 1 / 2) |> fun h => h] at *
            constructor <;> linarith
          · rw [abs_of_nonpos (by linarith [h1] : (v : ℝ) - 1 / 2 ≤ 0)] at *
            constructor <;> linarith
        linarith
      exact hne ⟨w, hwI⟩ hwd (by
        have : g' w = g ⟨w, hwI⟩ := by
          change g (Set.projIcc 0 1 zero_le_one w) = _
          rw [Set.projIcc_of_mem _ hwI]
        rw [← this]; exact hw0)
    have hsq' := hsq v
    have hte : tentG b v = sgn b * medianTent |b| v := rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq' with h | h
    · exact h
    · exfalso
      rw [h, hte] at hsign
      nlinarith [hsg]
  · -- outside the support both vanish
    have h0 : tentG b v = 0 := by
      unfold tentG medianTent
      rw [max_eq_left (by linarith [not_lt.mp hv]), mul_zero]
    have := hsq v
    rw [h0] at this
    rw [h0]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (by simpa using this)

end Papers.OrendayLaresRockel2026XiBeta
