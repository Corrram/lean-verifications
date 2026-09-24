import Papers.Rockel2026ExactBlest.ExactBlestContact

/-! Identification of the explicit certificates with the manuscript's potentials. -/
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval Topology
namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

theorem hasDerivAt_cubic (A B C D x : ℝ) :
    HasDerivAt (fun y => A * y ^ 3 + B * y ^ 2 + C * y + D)
      (3 * A * x ^ 2 + 2 * B * x + C) x := by
  convert (((((hasDerivAt_id x).pow 3).const_mul A).add
    (((hasDerivAt_id x).pow 2).const_mul B)).add
    ((hasDerivAt_id x).const_mul C)).add_const D using 1
  · ext y; dsimp
  · dsimp; ring

theorem hasDerivAt_antiPhi (k x : ℝ) :
    HasDerivAt (antiPhi k) ((1 - x) * (2 * x - k * (1 - x))) x := by
  convert hasDerivAt_cubic (-(2 + k) / 3) (1 + k) (-k) 0 x using 1
  · ext y; unfold antiPhi; ring
  · ring

theorem hasDerivAt_linearPsi (k m b z : ℝ) :
    HasDerivAt (linearPsi k m b) ((m * z + b) * (m * z + b - 2 * k * z)) z := by
  convert hasDerivAt_cubic ((m ^ 2 - 2 * k * m) / 3) (b * (m - k)) (b ^ 2) 0 z using 1
  · ext y; unfold linearPsi; ring
  · ring

theorem hasDerivAt_graphPhi (w x : ℝ) :
    HasDerivAt (graphPhi w) ((x - w) * (2 * x - kA w * (x - w))) x := by
  convert hasDerivAt_cubic ((2 - kA w) / 3) (w * (kA w - 1)) (-kA w * w ^ 2) 0 x using 1
  · ext y; unfold graphPhi; ring
  · ring

theorem hasDerivAt_splitPhi (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (splitPhi a) (((x - a) / (2 * a)) *
      (2 * x - kB a * ((x - a) / (2 * a)))) x := by
  convert ((((hasDerivAt_id x).pow 3).div_const (3 * a)).sub
    (((hasDerivAt_id x).pow 2).div_const 2)).sub
    (((((hasDerivAt_id x).sub_const a).pow 3).const_mul (kB a)).div_const (12 * a ^ 2)) using 1
  · ext y; rfl
  · dsimp
    field_simp
    ring

theorem continuous_phiA (w : ℝ) : Continuous (phiA w) := by
  apply Continuous.if_le (by unfold phiA0 antiPhi; fun_prop)
    (by unfold phiA1 graphPhi; fun_prop) continuous_id continuous_const
  intro x hx
  change x = w at hx
  subst x
  simp [phiA0, phiA1]

theorem continuous_psiA (w : ℝ) : Continuous (psiA w) := by
  apply Continuous.if_le (by unfold psiA0 linearPsi; fun_prop)
    (by unfold psiA1 linearPsi; fun_prop) continuous_id continuous_const
  intro x hx
  change x = 1 - w at hx
  subst x
  simp [psiA1]

theorem potentialsA_normalized (w : ℝ) (hw : w ≤ 1) : phiA w w = 0 ∧ psiA w 0 = 0 := by
  simp [phiA, phiA0, psiA, sub_nonneg.mpr hw, psiA0, linearPsi]

theorem hasDerivAt_phiA (w x : ℝ) (hx : x ≠ w) :
    HasDerivAt (phiA w)
      (if x ≤ w then (1 - x) * (2 * x - kA w * (1 - x))
       else (x - w) * (2 * x - kA w * (x - w))) x := by
  by_cases h : x ≤ w
  · rw [ite_eq_left h]
    apply ((hasDerivAt_antiPhi (kA w) x).sub_const (antiPhi (kA w) w)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (lt_of_le_of_ne h hx)] with y hy
    change y < w at hy
    simp [phiA, phiA0, hy.le]
  · rw [ite_eq_right h]
    apply ((hasDerivAt_graphPhi w x).sub_const (graphPhi w w)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (lt_of_not_ge h)] with y hy
    change w < y at hy
    simp [phiA, phiA1, not_le.mpr hy]

theorem hasDerivAt_psiA (w z : ℝ) (hz : z ≠ 1 - w) :
    HasDerivAt (psiA w)
      (if z ≤ 1 - w then (z + w) * (z + w - 2 * kA w * z)
       else (1 - z) * (1 - z - 2 * kA w * z)) z := by
  by_cases h : z ≤ 1 - w
  · rw [ite_eq_left h]
    have hd := hasDerivAt_linearPsi (kA w) 1 w z
    simp only [one_mul] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (lt_of_le_of_ne h hz)] with y hy
    change y < 1 - w at hy
    simp [psiA, psiA0, hy.le]
  · rw [ite_eq_right h]
    have hd := ((hasDerivAt_linearPsi (kA w) (-1) 1 z).const_add (psiA0 w (1 - w))).sub_const
      (linearPsi (kA w) (-1) 1 (1 - w))
    convert hd.congr_of_eventuallyEq (show psiA w =ᶠ[𝓝 z] _ from ?_) using 1
    · ring
    · filter_upwards [Ioi_mem_nhds (lt_of_not_ge h)] with y hy
      change 1 - w < y at hy
      simp [psiA, psiA1, not_le.mpr hy]

theorem cutB_bounds (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    0 < cutB a ∧ cutB a < 1 - a := by
  have ha0 : 0 < a := by linarith
  constructor
  · unfold cutB; positivity
  · unfold cutB
    rw [div_lt_iff₀ (by positivity : 0 < 2 * a)]
    nlinarith

theorem continuous_phiB (a : ℝ) : Continuous (phiB a) := by
  apply Continuous.if_le (by unfold phiB0 antiPhi; fun_prop)
    (by unfold phiB1 splitPhi; fun_prop) continuous_id continuous_const
  intro x hx
  change x = a at hx
  subst x
  simp [phiB0, phiB1]

theorem continuous_psiB (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) : Continuous (psiB a) := by
  have hc := cutB_bounds a ha ha1
  apply Continuous.if_le (by unfold psiB0 linearPsi; fun_prop) ?_ continuous_id continuous_const
  · intro x hx
    change x = cutB a at hx
    subst x
    simp [hc.2.le, psiB1]
  · apply Continuous.if_le (by unfold psiB1 linearPsi; fun_prop)
      (by unfold psiB2 linearPsi; fun_prop) continuous_id continuous_const
    intro x hx
    change x = 1 - a at hx
    subst x
    simp [psiB2]

theorem potentialsB_normalized (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    phiB a a = 0 ∧ psiB a 0 = 0 := by
  simp [phiB, phiB0, psiB, (cutB_bounds a ha ha1).1.le, psiB0, linearPsi]

theorem hasDerivAt_phiB (a x : ℝ) (ha : a ≠ 0) (hx : x ≠ a) :
    HasDerivAt (phiB a)
      (if x ≤ a then (1 - x) * (2 * x - kB a * (1 - x))
       else ((x - a) / (2 * a)) * (2 * x - kB a * ((x - a) / (2 * a)))) x := by
  by_cases h : x ≤ a
  · rw [ite_eq_left h]
    apply ((hasDerivAt_antiPhi (kB a) x).sub_const (antiPhi (kB a) a)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (lt_of_le_of_ne h hx)] with y hy
    change y < a at hy
    simp [phiB, phiB0, hy.le]
  · rw [ite_eq_right h]
    apply ((hasDerivAt_splitPhi a x ha).sub_const (splitPhi a a)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds (lt_of_not_ge h)] with y hy
    change a < y at hy
    simp [phiB, phiB1, not_le.mpr hy]

theorem hasDerivAt_psiB1 (a z : ℝ) :
    HasDerivAt (psiB1 a) ((a * (1 - 2 * z) / (2 * a - 1)) *
      (a * (1 - 2 * z) / (2 * a - 1) - 2 * kB a * z)) z := by
  convert ((hasDerivAt_linearPsi (kB a) (-2 * a / (2 * a - 1)) (a / (2 * a - 1)) z).const_add
    (psiB0 a (cutB a))).sub_const
    (linearPsi (kB a) (-2 * a / (2 * a - 1)) (a / (2 * a - 1)) (cutB a)) using 1
  · ext y; rfl
  · ring

theorem hasDerivAt_psiB2 (a z : ℝ) :
    HasDerivAt (psiB2 a) ((1 - z) * (1 - z - 2 * kB a * z)) z := by
  convert ((hasDerivAt_linearPsi (kB a) (-1) 1 z).const_add
    (psiB1 a (1 - a))).sub_const (linearPsi (kB a) (-1) 1 (1 - a)) using 1
  · ext y; rfl
  · ring

theorem hasDerivAt_psiB (a z : ℝ) (hzc : z ≠ cutB a) (hza : z ≠ 1 - a) :
    HasDerivAt (psiB a) (randomRankReal a z * (randomRankReal a z - 2 * kB a * z)) z := by
  by_cases h0 : z ≤ cutB a
  · simp only [randomRankReal, ite_eq_left h0]
    apply (hasDerivAt_linearPsi (kB a) (2 * a) a z).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds (lt_of_le_of_ne h0 hzc)] with y hy
    change y < cutB a at hy
    simp [psiB, psiB0, hy.le]
  · by_cases h1 : z ≤ 1 - a
    · simp only [randomRankReal, ite_eq_right h0, ite_eq_left h1]
      apply (hasDerivAt_psiB1 a z).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds (lt_of_not_ge h0) (lt_of_le_of_ne h1 hza)] with y hy
      simp [psiB, not_le.mpr hy.1, hy.2.le]
    · simp only [randomRankReal, ite_eq_right h0, ite_eq_right h1]
      apply (hasDerivAt_psiB2 a z).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds (lt_of_not_ge h0), Ioi_mem_nhds (lt_of_not_ge h1)] with y hy0 hy1
      change cutB a < y at hy0
      change 1 - a < y at hy1
      simp [psiB, not_le.mpr hy0, not_le.mpr hy1]

theorem random_branches_root_sum (a x : ℝ) (ha : a ≠ 0) :
    (x - a) / (2 * a) + (a + x - 2 * a * x) / (2 * a) = x * (1 - a) / a := by
  field_simp
  ring

theorem random_branches_same_derivative (a x : ℝ) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    ((x - a) / (2 * a)) * (2 * x - kB a * ((x - a) / (2 * a))) =
      ((a + x - 2 * a * x) / (2 * a)) * (2 * x - kB a * ((a + x - 2 * a * x) / (2 * a))) := by
  have hd : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  unfold kB
  field_simp
  ring

theorem hasDerivAt_etaB (a : ℝ) (ha : a ≠ 0) :
    HasDerivAt etaB (-((1 - a) ^ 2 * (1 + a) * (3 * a ^ 2 + 2 * a + 1)) / (4 * a ^ 3)) a := by
  convert (hasDerivAt_const a (-1 : ℝ)).add
    (((((hasDerivAt_const a (1 : ℝ)).sub (hasDerivAt_id a)).pow 3).mul
      (((((hasDerivAt_id a).pow 2).const_mul 2).add ((hasDerivAt_id a).const_mul 5)).add_const 1)).div
      (((hasDerivAt_id a).pow 2).const_mul 8) (by simpa using mul_ne_zero (by norm_num : (8 : ℝ) ≠ 0) (pow_ne_zero 2 ha))) using 1
  · ext y; rfl
  · dsimp
    field_simp
    ring

theorem deriv_etaB_neg (a : ℝ) (ha : 1 / 2 ≤ a) (ha1 : a < 1) : deriv etaB a < 0 := by
  have ha0 : 0 < a := by linarith
  rw [(hasDerivAt_etaB a ha0.ne').deriv]
  have h1 : 0 < 1 - a := by linarith
  have h2 : 0 < 1 + a := by linarith
  have h3 : 0 < 3 * a ^ 2 + 2 * a + 1 := by positivity
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)

#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_psiB1
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_psiB2
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_psiB
#assert_standard_axioms Papers.Rockel2026ExactBlest.random_branches_root_sum
#assert_standard_axioms Papers.Rockel2026ExactBlest.random_branches_same_derivative
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_etaB
#assert_standard_axioms Papers.Rockel2026ExactBlest.deriv_etaB_neg
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_cubic
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_antiPhi
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_linearPsi
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_graphPhi
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_splitPhi
#assert_standard_axioms Papers.Rockel2026ExactBlest.continuous_phiA
#assert_standard_axioms Papers.Rockel2026ExactBlest.continuous_psiA
#assert_standard_axioms Papers.Rockel2026ExactBlest.potentialsA_normalized
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_phiA
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_psiA
#assert_standard_axioms Papers.Rockel2026ExactBlest.cutB_bounds
#assert_standard_axioms Papers.Rockel2026ExactBlest.continuous_phiB
#assert_standard_axioms Papers.Rockel2026ExactBlest.continuous_psiB
#assert_standard_axioms Papers.Rockel2026ExactBlest.potentialsB_normalized
#assert_standard_axioms Papers.Rockel2026ExactBlest.hasDerivAt_phiB

end
end Papers.Rockel2026ExactBlest
