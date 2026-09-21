import Verification.StochasticBounds

/-! # The scalar relaxation for the xi-footrule lower bound

The two values minimize a strictly convex weighted quadratic under a
uniform-mean constraint. The proof uses an exact quadratic remainder.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def jensenLow (μ : ℝ) (v : I) : ℝ :=
  if (v : ℝ) * (2 + μ) ≤ μ then 0
  else if (v : ℝ) * (2 + μ) ≤ 2 then (v : ℝ) - μ / 2 * (1 - v)
  else 2 - 1 / (v : ℝ)

noncomputable def jensenHigh (μ : ℝ) (v : I) : ℝ :=
  if (v : ℝ) * (2 + μ) ≤ μ then (v : ℝ) / (1 - v)
  else if (v : ℝ) * (2 + μ) ≤ 2 then (v : ℝ) + μ / 2 * v
  else 1

def splitObjective (μ v a b : ℝ) : ℝ := μ * v * a + v * a ^ 2 + (1 - v) * b ^ 2

theorem jensen_feasible (μ : ℝ) (hμ : μ ∈ Icc 0 2) (v : I) :
    jensenLow μ v ∈ Icc 0 1 ∧ jensenHigh μ v ∈ Icc 0 1 ∧
      (v : ℝ) * jensenLow μ v + (1 - v) * jensenHigh μ v = v := by
  unfold jensenLow jensenHigh
  by_cases h0 : (v : ℝ) * (2 + μ) ≤ μ
  · simp only [ite_eq_left h0]
    have hh : (v : ℝ) ≤ 1 / 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hμ.2) (sub_nonneg.mpr v.property.2)]
    have hd : 0 < 1 - (v : ℝ) := by linarith
    refine ⟨by norm_num, ⟨div_nonneg v.property.1 hd.le, (div_le_one hd).mpr (by linarith)⟩, ?_⟩
    field_simp
    ring
  · simp only [ite_eq_right h0]
    by_cases h1 : (v : ℝ) * (2 + μ) ≤ 2
    · simp only [ite_eq_left h1]
      have hp := mul_nonneg hμ.1 v.property.1
      have hq := mul_nonneg hμ.1 (sub_nonneg.mpr v.property.2)
      refine ⟨⟨by nlinarith, by nlinarith [v.property.2]⟩,
        ⟨by nlinarith [v.property.1], by nlinarith⟩, ?_⟩
      ring
    · simp only [ite_eq_right h1]
      have hh : 1 / 2 < (v : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hμ.2) v.property.1]
      have hv : 0 < (v : ℝ) := by linarith
      have hi : 1 / (v : ℝ) ≤ 2 := (div_le_iff₀ hv).mpr (by linarith)
      have hj : 1 ≤ 1 / (v : ℝ) := (le_div_iff₀ hv).mpr (by simpa using v.property.2)
      refine ⟨⟨by linarith, by linarith⟩, by norm_num, ?_⟩
      field_simp
      ring

theorem jensen_certificate (μ : ℝ) (hμ : μ ∈ Icc 0 2) (v : I) (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hm : (v : ℝ) * a + (1 - v) * b = v) :
    0 ≤ (μ + 2 * jensenLow μ v - 2 * jensenHigh μ v) * (a - jensenLow μ v) := by
  unfold jensenLow jensenHigh
  by_cases h0 : (v : ℝ) * (2 + μ) ≤ μ
  · simp only [ite_eq_left h0, mul_zero, add_zero, sub_zero]
    have hh : (v : ℝ) ≤ 1 / 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hμ.2) (sub_nonneg.mpr v.property.2)]
    have hd : 0 < 1 - (v : ℝ) := by linarith
    have he : (1 - (v : ℝ)) * ((v : ℝ) / (1 - v)) = v := by field_simp
    have hp : 0 ≤ μ - 2 * ((v : ℝ) / (1 - v)) := by
      apply nonneg_of_mul_nonneg_left (b := 1 - (v : ℝ)) _ hd
      nlinarith only [he, h0]
    exact mul_nonneg hp ha.1
  · simp only [ite_eq_right h0]
    by_cases h1 : (v : ℝ) * (2 + μ) ≤ 2
    · simp only [ite_eq_left h1]
      have he : μ + 2 * ((v : ℝ) - μ / 2 * (1 - v)) - 2 * ((v : ℝ) + μ / 2 * v) = 0 := by ring
      rw [he, zero_mul]
    · simp only [ite_eq_right h1, mul_one]
      have hh : 1 / 2 < (v : ℝ) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hμ.2) v.property.1]
      have hv : 0 < (v : ℝ) := by linarith
      have hi : 2 / (v : ℝ) ≤ μ + 2 := (div_le_iff₀ hv).mpr (by nlinarith)
      have hi' : 2 * (1 / (v : ℝ)) ≤ μ + 2 := by simpa [div_eq_mul_inv] using hi
      have hp : 0 ≤ μ + 2 * (2 - 1 / (v : ℝ)) - 2 := by linarith
      have he : (v : ℝ) * (2 - 1 / (v : ℝ)) = 2 * v - 1 := by field_simp
      have hqa : 2 - 1 / (v : ℝ) ≤ a := by
        apply (mul_le_mul_iff_right₀ hv).mp
        nlinarith [mul_nonneg (sub_nonneg.mpr v.property.2) (sub_nonneg.mpr hb.2)]
      exact mul_nonneg hp (sub_nonneg.mpr hqa)

theorem splitObjective_remainder (μ v a b x y : ℝ)
    (hm : v * a + (1 - v) * b = v) (ho : v * x + (1 - v) * y = v) :
    splitObjective μ v a b - splitObjective μ v x y =
      v * (a - x) ^ 2 + (1 - v) * (b - y) ^ 2 + v * (μ + 2 * x - 2 * y) * (a - x) := by
  unfold splitObjective
  calc
    _ = v * (a - x) ^ 2 + (1 - v) * (b - y) ^ 2 + v * (μ + 2 * x - 2 * y) * (a - x) +
        2 * y * ((v * a + (1 - v) * b) - (v * x + (1 - v) * y)) := by ring
    _ = _ := by rw [hm, ho]; ring

theorem jensen_optimal_gap (μ : ℝ) (hμ : μ ∈ Icc 0 2) (v : I) (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hm : (v : ℝ) * a + (1 - v) * b = v) :
    (v : ℝ) * (a - jensenLow μ v) ^ 2 + (1 - v) * (b - jensenHigh μ v) ^ 2 ≤
      splitObjective μ v a b - splitObjective μ v (jensenLow μ v) (jensenHigh μ v) := by
  rw [splitObjective_remainder μ (v : ℝ) a b _ _ hm (jensen_feasible μ hμ v).2.2]
  have h := mul_nonneg v.property.1 (jensen_certificate μ hμ v a b ha hb hm)
  nlinarith only [h]

theorem jensen_optimal (μ : ℝ) (hμ : μ ∈ Icc 0 2) (v : I) (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hm : (v : ℝ) * a + (1 - v) * b = v) :
    splitObjective μ v (jensenLow μ v) (jensenHigh μ v) ≤ splitObjective μ v a b := by
  have h := jensen_optimal_gap μ hμ v a b ha hb hm
  nlinarith [mul_nonneg v.property.1 (sq_nonneg (a - jensenLow μ v)),
    mul_nonneg (sub_nonneg.mpr v.property.2) (sq_nonneg (b - jensenHigh μ v))]

theorem jensen_optimal_eq_iff (μ : ℝ) (hμ : μ ∈ Icc 0 2) (v : I)
    (hv : 0 < (v : ℝ) ∧ (v : ℝ) < 1) (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1)
    (hm : (v : ℝ) * a + (1 - v) * b = v) :
    splitObjective μ v a b = splitObjective μ v (jensenLow μ v) (jensenHigh μ v) ↔
      a = jensenLow μ v ∧ b = jensenHigh μ v := by
  constructor
  · intro he
    have h := jensen_optimal_gap μ hμ v a b ha hb hm
    rw [he, sub_self] at h
    have hA := mul_nonneg v.property.1 (sq_nonneg (a - jensenLow μ v))
    have hB := mul_nonneg (sub_nonneg.mpr v.property.2) (sq_nonneg (b - jensenHigh μ v))
    have hqa : (a - jensenLow μ v) ^ 2 = 0 := by nlinarith [sq_nonneg (a - jensenLow μ v), hv.1]
    have hqb : (b - jensenHigh μ v) ^ 2 = 0 := by nlinarith [sq_nonneg (b - jensenHigh μ v), hv.2]
    exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hqa), sub_eq_zero.mp (sq_eq_zero_iff.mp hqb)⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem measurable_jensenLow (μ : ℝ) : Measurable (jensenLow μ) := by
  unfold jensenLow
  have h0 : MeasurableSet {v : I | (v : ℝ) * (2 + μ) ≤ μ} :=
    measurableSet_le (by fun_prop) measurable_const
  have h1 : MeasurableSet {v : I | (v : ℝ) * (2 + μ) ≤ 2} :=
    measurableSet_le (by fun_prop) measurable_const
  exact measurable_const.ite h0 ((show Measurable (fun v : I => (v : ℝ) - μ / 2 * (1 - v)) by fun_prop).ite h1 (by fun_prop))

theorem measurable_jensenHigh (μ : ℝ) : Measurable (jensenHigh μ) := by
  unfold jensenHigh
  have h0 : MeasurableSet {v : I | (v : ℝ) * (2 + μ) ≤ μ} :=
    measurableSet_le (by fun_prop) measurable_const
  have h1 : MeasurableSet {v : I | (v : ℝ) * (2 + μ) ≤ 2} :=
    measurableSet_le (by fun_prop) measurable_const
  exact (show Measurable (fun v : I => (v : ℝ) / (1 - v)) by fun_prop).ite h0
    ((show Measurable (fun v : I => (v : ℝ) + μ / 2 * v) by fun_prop).ite h1 measurable_const)

end Verification
