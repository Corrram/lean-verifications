import Papers.OrendayLaresRockel2026XiBeta.TentTranspose
import Verification.StepDensity

/-! # Proposition 2: the actual Lebesgue density of the tent copula

Values on the finitely many strip edges are fixed explicitly. At full width
the version uses the median sign, which also supports the endpoint TP2 claim.
-/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

noncomputable def tentStart (r : I) : I :=
  ⟨(1 - (r : ℝ)) / 2, by constructor <;> linarith [r.property.1, r.property.2]⟩

noncomputable def tentEnd (r : I) : I :=
  ⟨(1 + (r : ℝ)) / 2, by constructor <;> linarith [r.property.1, r.property.2]⟩

noncomputable def tentSlope (r v : I) : ℝ :=
  if r = 1 then medianSign v else
    2 * lowerStep Copula.unitHalf v - lowerStep (tentStart r) v - lowerStep (tentEnd r) v

theorem measurable_tentSlope (r : I) : Measurable (tentSlope r) := by
  unfold tentSlope
  split_ifs
  · exact measurable_medianSign
  · exact (((measurable_lowerStep _).const_mul 2).sub (measurable_lowerStep _)).sub
      (measurable_lowerStep _)

theorem tentSlope_values (r v : I) : tentSlope r v = -1 ∨ tentSlope r v = 0 ∨ tentSlope r v = 1 := by
  have ha : tentStart r ≤ Copula.unitHalf := by change (1 - (r : ℝ)) / 2 ≤ (1 / 2 : ℝ); linarith [r.property.1]
  have hz : Copula.unitHalf ≤ tentEnd r := by change (1 / 2 : ℝ) ≤ (1 + (r : ℝ)) / 2; linarith [r.property.1]
  by_cases hr : r = 1
  · simp only [tentSlope, ite_eq_left hr, medianSign]
    split_ifs <;> norm_num
  · by_cases ha' : v ≤ tentStart r
    · norm_num [tentSlope, hr, lowerStep, ha', ha'.trans ha, (ha'.trans ha).trans hz]
    · by_cases hv : v ≤ Copula.unitHalf
      · norm_num [tentSlope, hr, lowerStep, ha', hv, hv.trans hz]
      · by_cases hz' : v ≤ tentEnd r <;> norm_num [tentSlope, hr, lowerStep, ha', hv, hz']

theorem tentSlope_abs_le (r v : I) : |tentSlope r v| ≤ 1 := by
  rcases tentSlope_values r v with h | h | h <;> rw [h] <;> norm_num

theorem integral_tentSlope (r v : I) :
    (∫ t in Iic v, tentSlope r t) = medianTent r v := by
  by_cases hr : r = 1
  · subst r
    simp only [tentSlope, ite_true]
    rw [integral_medianSign]
    change medianWedge v = medianTent (1 : ℝ) v
    by_cases hv : (v : ℝ) ≤ 1 / 2
    · simp only [medianWedge, medianTent, abs_of_nonpos (by linarith : (v : ℝ) - 1 / 2 ≤ 0)]
      rw [min_eq_left (by linarith), max_eq_right (by linarith [v.property.1])]
      ring
    · simp only [medianWedge, medianTent, abs_of_nonneg (by linarith : 0 ≤ (v : ℝ) - 1 / 2)]
      rw [min_eq_right (by linarith), max_eq_right (by linarith [v.property.2])]
      ring
  · simp only [tentSlope, ite_eq_right hr]
    rw [integral_sub, integral_sub, integral_const_mul,
      integral_lowerStep, integral_lowerStep, integral_lowerStep]
    · change 2 * min (v : ℝ) (1 / 2) - min (v : ℝ) ((1 - (r : ℝ)) / 2) -
        min (v : ℝ) ((1 + (r : ℝ)) / 2) = _
      by_cases hv : (v : ℝ) ≤ 1 / 2
      · rw [medianTent, abs_of_nonpos (by linarith)]
        simp only [min_def, max_def]
        split_ifs <;> linarith [r.property.1, r.property.2]
      · rw [medianTent, abs_of_nonneg (by linarith)]
        simp only [min_def, max_def]
        split_ifs <;> linarith [r.property.1, r.property.2]
    all_goals first
      | exact (integrable_lowerStep _).integrableOn
      | exact ((integrable_lowerStep _).const_mul 2).integrableOn
      | exact (((integrable_lowerStep _).const_mul 2).sub (integrable_lowerStep _)).integrableOn

noncomputable def signedTentSlope (b : ℝ) (hb : b ∈ Icc (-1) 1) (v : I) : ℝ :=
  if h : 0 ≤ b then tentSlope ⟨b, by constructor <;> linarith [hb.2]⟩ v
  else -tentSlope ⟨-b, by constructor <;> linarith [hb.1]⟩ v

noncomputable def tentDensity (b : ℝ) (hb : b ∈ Icc (-1) 1) (x : Fin 2 → I) : ℝ :=
  1 + medianSign (x 0) * signedTentSlope b hb (x 1)

theorem signedTentSlope_measurable (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    Measurable (signedTentSlope b hb) := by
  unfold signedTentSlope
  split_ifs
  · exact measurable_tentSlope _
  · exact (measurable_tentSlope _).neg

theorem signedTentSlope_abs_le (b : ℝ) (hb : b ∈ Icc (-1) 1) (v : I) :
    |signedTentSlope b hb v| ≤ 1 := by
  unfold signedTentSlope
  split_ifs
  · exact tentSlope_abs_le _ v
  · simpa only [abs_neg] using tentSlope_abs_le _ v

theorem integral_signedTentSlope (b : ℝ) (hb : b ∈ Icc (-1) 1) (v : I) :
    (∫ t in Iic v, signedTentSlope b hb t) = tentDisplacement b hb v := by
  unfold signedTentSlope tentDisplacement
  split_ifs
  · exact integral_tentSlope _ v
  · rw [integral_neg, integral_tentSlope]

theorem leftBoundary_density (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (tentDensity b hb x)) :=
  twoStrip_density (tentDisplacement b hb) (signedTentSlope b hb)
    (signedTentSlope_measurable b hb) (signedTentSlope_abs_le b hb) (integral_signedTentSlope b hb)

theorem leftBoundary_absolutelyContinuous (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).toMeasure ≪ (volume : Measure (Fin 2 → I)) := by
  rw [leftBoundary_density]
  exact withDensity_absolutelyContinuous _ _

theorem tentDensity_values (b : ℝ) (hb : b ∈ Icc (-1) 1) (x : Fin 2 → I) :
    tentDensity b hb x = 0 ∨ tentDensity b hb x = 1 ∨ tentDensity b hb x = 2 := by
  unfold tentDensity signedTentSlope
  split_ifs <;> rename_i h
  all_goals
    rcases tentSlope_values _ (x 1) with ht | ht | ht <;>
      rw [ht] <;> unfold medianSign <;> split_ifs <;> norm_num

end Papers.OrendayLaresRockel2026XiBeta
