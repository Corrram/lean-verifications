import Verification.MonotoneMomentEquality
import Verification.StepDensity

/-! # Equality in the decreasing-function diagonal moment bound

Vanishing of an elementary nonnegative defect gives three possible values.
The lengths of the one and positive level sets give canonical cut points.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def oneLevel (g : I → ℝ) (u : I) : ℝ := if g u = 1 then 1 else 0
noncomputable def positiveLevel (g : I → ℝ) (u : I) : ℝ := if 0 < g u then 1 else 0

theorem oneLevel_mem (g : I → ℝ) (u : I) : oneLevel g u ∈ Icc 0 1 := by
  unfold oneLevel; split_ifs <;> norm_num

theorem positiveLevel_mem (g : I → ℝ) (u : I) : positiveLevel g u ∈ Icc 0 1 := by
  unfold positiveLevel; split_ifs <;> norm_num

theorem measurable_oneLevel {g : I → ℝ} (hg : Measurable g) : Measurable (oneLevel g) :=
  measurable_const.ite (measurableSet_eq_fun hg measurable_const) measurable_const

theorem measurable_positiveLevel {g : I → ℝ} (hg : Measurable g) : Measurable (positiveLevel g) :=
  measurable_const.ite (measurableSet_lt measurable_const hg) measurable_const

theorem integral_unit_mem {g : I → ℝ} (hg : Measurable g) (hb : ∀ u, g u ∈ Icc 0 1) :
    (∫ u : I, g u) ∈ Icc 0 1 := by
  refine ⟨integral_nonneg (fun u => (hb u).1), ?_⟩
  have h := integral_mono (integrable_unit_bounded hg hb) (integrable_const (1 : ℝ))
    (fun u => (hb u).2)
  simpa using h

theorem oneLevel_le_self {g : I → ℝ} (hb : ∀ u, g u ∈ Icc 0 1) (u : I) :
    oneLevel g u ≤ g u := by
  unfold oneLevel; split_ifs with h
  · exact h.ge
  · exact (hb u).1

theorem self_le_positiveLevel {g : I → ℝ} (hb : ∀ u, g u ∈ Icc 0 1) (u : I) :
    g u ≤ positiveLevel g u := by
  unfold positiveLevel; split_ifs with h
  · exact (hb u).2
  · exact le_of_not_gt h

theorem oneLevel_antitone {g : I → ℝ} (hg : Antitone g) (hb : ∀ u, g u ∈ Icc 0 1) :
    Antitone (oneLevel g) := by
  intro u w huw
  unfold oneLevel
  by_cases hw : g w = 1
  · have hu : g u = 1 := le_antisymm (hb u).2 (by simpa only [hw] using hg huw)
    simp [hu, hw]
  · simp only [ite_eq_right hw]
    split_ifs <;> norm_num

theorem positiveLevel_antitone {g : I → ℝ} (hg : Antitone g) : Antitone (positiveLevel g) := by
  intro u w huw
  unfold positiveLevel
  by_cases hw : 0 < g w
  · simp [hw, hw.trans_le (hg huw)]
  · simp only [ite_eq_right hw]
    split_ifs <;> norm_num

noncomputable def threeLevel (A B : I) (a : ℝ) (u : I) : ℝ :=
  (1 - a) * lowerStep A u + a * lowerStep B u

theorem integrable_threeLevel (A B : I) (a : ℝ) : Integrable (threeLevel A B a) :=
  ((integrable_lowerStep A).const_mul _).add ((integrable_lowerStep B).const_mul _)

theorem integral_threeLevel_Iic (A B : I) (a : ℝ) (v : I) :
    (∫ u in Iic v, threeLevel A B a u) =
      (1 - a) * min (v : ℝ) A + a * min (v : ℝ) B := by
  unfold threeLevel
  rw [integral_add ((integrable_lowerStep A).const_mul _).integrableOn
    ((integrable_lowerStep B).const_mul _).integrableOn,
    integral_const_mul, integral_const_mul, integral_lowerStep, integral_lowerStep]

theorem integral_threeLevel (A B : I) (a : ℝ) :
    (∫ u : I, threeLevel A B a u) = (A : ℝ) + a * ((B : ℝ) - A) := by
  have h := integral_threeLevel_Iic A B a 1
  have ht : Iic (1 : I) = univ := by ext u; simp [unitInterval.le_one']
  rw [ht, setIntegral_univ] at h
  change (∫ u : I, threeLevel A B a u) = (1 - a) * min (1 : ℝ) A + a * min (1 : ℝ) B at h
  rw [min_eq_right A.property.2, min_eq_right B.property.2] at h
  linarith

theorem threeLevel_sq (A B : I) (hAB : A ≤ B) (a : ℝ) (u : I) :
    threeLevel A B a u ^ 2 = threeLevel A B (a ^ 2) u := by
  unfold threeLevel lowerStep
  by_cases hu : u ≤ A
  · simp only [ite_eq_left hu, ite_eq_left (hu.trans hAB), mul_one]
    ring
  · by_cases hv : u ≤ B <;> simp [hu, hv]

theorem threeLevel_moment_eq (A B : I) (hAB : A ≤ B) (a : I) (v : I)
    (hm : (∫ u : I, threeLevel A B a u) = (v : ℝ)) :
    (∫ u : I, threeLevel A B a u ^ 2) = ∫ u in Iic v, threeLevel A B a u := by
  rw [integral_threeLevel] at hm
  have hvA : (A : ℝ) ≤ v := by nlinarith [a.property.1, show (A : ℝ) ≤ B from hAB]
  have hvB : (v : ℝ) ≤ B := by nlinarith [a.property.2, show (A : ℝ) ≤ B from hAB]
  simp_rw [threeLevel_sq A B hAB]
  rw [integral_threeLevel, integral_threeLevel_Iic, min_eq_right hvA, min_eq_left hvB]
  rw [← hm]
  ring

/-- Equality forces at most one intermediate level, namely g(v). -/
theorem ae_three_values_of_diagonal_moment_eq {g : I → ℝ} (hg : Antitone g)
    (hb : ∀ u, g u ∈ Icc 0 1) (v : I) (hm : (∫ u : I, g u) = (v : ℝ))
    (heq : (∫ u : I, g u ^ 2) = ∫ u in Iic v, g u) :
    ∀ᵐ u : I, g u = 0 ∨ g u = g v ∨ g u = 1 := by
  classical
  let e : I → ℝ := (Iic v).indicator (fun _ => 1)
  have hi := integrable_unit_bounded hg.measurable hb
  have hsq : Integrable (fun u => g u ^ 2) := integrable_unit_bounded (hg.measurable.pow_const 2)
    (fun u => ⟨sq_nonneg _, by nlinarith [(hb u).1, (hb u).2]⟩)
  have hei : Integrable e := (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have he : (∫ u : I, e u) = (v : ℝ) := by
    simp [e, integral_indicator measurableSet_Iic, integral_const, Measure.real,
      unitInterval.volume_Iic, ENNReal.toReal_ofReal v.property.1]
  have heg : (fun u => e u * g u) = (Iic v).indicator g := by
    funext u; by_cases hu : u ∈ Iic v <;> simp [e, hu]
  have hegi : Integrable (fun u => e u * g u) := by rw [heg]; exact hi.indicator measurableSet_Iic
  let d (u : I) := g v * (g u - e u) - (g u ^ 2 - e u * g u)
  have hdi : Integrable d := ((hi.sub hei).const_mul _).sub (hsq.sub hegi)
  have hn (u : I) : 0 ≤ d u := by
    dsimp [d, e]
    by_cases hu : u ≤ v
    · simp only [indicator_of_mem (mem_Iic.mpr hu), one_mul]
      nlinarith [hg hu, (hb u).2]
    · simp only [indicator_of_notMem (show u ∉ Iic v from hu), zero_mul, sub_zero]
      nlinarith [hg (le_of_not_ge hu), (hb u).1]
  have hl : Integrable (fun u => g v * (g u - e u)) := (hi.sub hei).const_mul _
  have hr : Integrable (fun u => g u ^ 2 - e u * g u) := hsq.sub hegi
  have hz : (∫ u : I, d u) = 0 := by
    unfold d
    rw [integral_sub hl hr, integral_const_mul,
      integral_sub hi hei, integral_sub hsq hegi, hm, he, heg,
      integral_indicator measurableSet_Iic, heq]
    ring
  have ha := (integral_eq_zero_iff_of_nonneg hn hdi).mp hz
  filter_upwards [ha] with u hu
  change d u = 0 at hu
  dsimp [d, e] at hu
  by_cases huv : u ≤ v
  · simp only [indicator_of_mem (mem_Iic.mpr huv), one_mul] at hu
    have hp : (g u - g v) * (g u - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  · simp only [indicator_of_notMem (show u ∉ Iic v from huv), zero_mul, sub_zero] at hu
    have hp : g u * (g u - g v) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))

/-- Canonical level-set cuts recover an antitone three-valued function. -/
theorem ae_threeLevel_of_three_values {g : I → ℝ} (hg : Antitone g)
    (hb : ∀ u, g u ∈ Icc 0 1) (a : I)
    (hvals : ∀ᵐ u : I, g u = 0 ∨ g u = (a : ℝ) ∨ g u = 1)
    (A B : I) (hA : (∫ u : I, oneLevel g u) = (A : ℝ))
    (hB : (∫ u : I, positiveLevel g u) = (B : ℝ)) :
    g =ᵐ[volume] threeLevel A B a := by
  have hones := ae_lower_indicator_of_antitone_binary (oneLevel_antitone hg hb)
    (oneLevel_mem g) A hA (Filter.Eventually.of_forall fun u => by
      unfold oneLevel; split_ifs <;> simp)
  have hpos := ae_lower_indicator_of_antitone_binary (positiveLevel_antitone hg)
    (positiveLevel_mem g) B hB (Filter.Eventually.of_forall fun u => by
      unfold positiveLevel; split_ifs <;> simp)
  filter_upwards [hvals, hones, hpos] with u hu ho hp
  have hstep (b : I) : (Iic b).indicator (fun _ => (1 : ℝ)) u = lowerStep b u := rfl
  rw [hstep] at ho hp
  unfold threeLevel
  rw [← ho, ← hp]
  rcases hu with hu | hu | hu
  · simp [oneLevel, positiveLevel, hu]
  · rw [hu]
    by_cases ha0 : (a : ℝ) = 0
    · simp [oneLevel, positiveLevel, hu, ha0]
    by_cases ha1 : (a : ℝ) = 1
    · simp [oneLevel, positiveLevel, hu, ha1]
    have hap : 0 < (a : ℝ) := lt_of_le_of_ne a.property.1 (Ne.symm ha0)
    simp [oneLevel, positiveLevel, hu, ha1, hap]
  · simp [oneLevel, positiveLevel, hu]

/-- Changing the intermediate value to its value determined by the mean
also works when the two cut points coincide. -/
theorem threeLevel_eq_normalized (A B : I) (a : ℝ) (v : I)
    (hm : (∫ u : I, threeLevel A B a u) = (v : ℝ)) :
    threeLevel A B a = threeLevel A B (((v : ℝ) - A) / ((B : ℝ) - A)) := by
  rw [integral_threeLevel] at hm
  by_cases hAB : A = B
  · subst B
    funext u
    unfold threeLevel
    ring
  · have hd : (B : ℝ) - A ≠ 0 := sub_ne_zero.mpr (fun h => hAB (Subtype.ext h.symm))
    have ha : a = ((v : ℝ) - A) / ((B : ℝ) - A) := (eq_div_iff hd).mpr (by linarith)
    rw [← ha]

/-- The source's open-interval convention differs only at the two cuts. -/
noncomputable def threeLevelOpen (A B : I) (a : ℝ) (u : I) : ℝ :=
  (if u < A then 1 else 0) + a * (if A < u ∧ u < B then 1 else 0)

theorem threeLevel_eq_open_ae (A B : I) (hAB : A ≤ B) (a : ℝ) :
    threeLevel A B a =ᵐ[volume] threeLevelOpen A B a := by
  filter_upwards [volume.ae_ne A, volume.ae_ne B] with u huA huB
  unfold threeLevel threeLevelOpen lowerStep
  by_cases hu : u < A
  · have huB' := hu.trans_le hAB
    simp [hu, hu.le, huB'.le, not_lt_of_ge hu.le]
  · have hAu : A < u := lt_of_le_of_ne (le_of_not_gt hu) (Ne.symm huA)
    by_cases hv : u < B
    · simp [hu, not_le_of_gt hAu, hv, hv.le, hAu]
    · have hBu : B < u := lt_of_le_of_ne (le_of_not_gt hv) (Ne.symm huB)
      simp [hu, not_le_of_gt hAu, hv, not_le_of_gt hBu]

/-- Unordered cuts in the source formula can always be normalized by max. -/
theorem threeLevelOpen_max (A B : I) (a : ℝ) :
    threeLevelOpen A (max A B) a = threeLevelOpen A B a := by
  funext u
  by_cases hAu : A < u
  · have hn : ¬u < A := not_lt_of_ge hAu.le
    simp [threeLevelOpen, hAu, lt_max_iff, hn]
  · simp [threeLevelOpen, hAu]

end Verification
