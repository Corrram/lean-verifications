import Papers.AnsariRockelSteinmassl2026RhoGamma.ThetaBoundary
import Mathlib.Analysis.Calculus.Rademacher

/-! # Lemma 3.5: the source potential, including its almost-everywhere derivative bound -/

open MeasureTheory ProbabilityTheory Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

/-- Equation (34). -/
noncomputable def thetaWidth (theta : ℝ) : ℝ :=
  if theta ≤ 1 then 1 / theta - 1 else |thetaDelta theta|

/-- The library certificate has exactly the Lipschitz constant specified by the source. -/
theorem thetaCertificate_width (theta : ℝ) (ht : 0 < theta) :
    (thetaCertificate theta ht).w = thetaWidth theta := by
  unfold thetaCertificate
  split
  next h => simp only [thetaWidth, h, ite_true]; rfl
  next h =>
    simp only [thetaWidth, h, ite_false]
    split
    next hb =>
      change 1 / (⌊theta⌋₊ : ℝ) - 1 / theta = |thetaDelta theta|
      have he : thetaDelta theta = -(1 / (⌊theta⌋₊ : ℝ) - 1 / theta) := by
        simp only [thetaDelta, thetaEll, hb, ite_true]
        ring
      have hn : (0 : ℝ) < ⌊theta⌋₊ := by exact_mod_cast Nat.floor_pos.mpr (le_of_lt (lt_of_not_ge h))
      have hv : 0 ≤ 1 / (⌊theta⌋₊ : ℝ) - 1 / theta := sub_nonneg.mpr
        (one_div_le_one_div_of_le hn (Nat.floor_le ht.le))
      rw [he, abs_neg, abs_of_nonneg hv]
    next hb =>
      change 1 / theta - 1 / (⌊theta⌋₊ + 1 : ℝ) = |thetaDelta theta|
      have he : thetaDelta theta = 1 / theta - 1 / (⌊theta⌋₊ + 1 : ℝ) := by
        simp only [thetaDelta, thetaEll, hb, ite_false]
        field_simp
      have hv : 0 ≤ 1 / theta - 1 / (⌊theta⌋₊ + 1 : ℝ) := sub_nonneg.mpr
        (one_div_lt_one_div_of_lt ht (Nat.lt_floor_add_one theta)).le
      rw [he, abs_of_nonneg hv]

/-- Lemma 3.5: a genuine feasible potential, contact on the optimizer, and the source endpoint value. -/
theorem theta_auxiliary_potential (theta : ℝ) (ht : 0 < theta) :
    let A := thetaCertificate theta ht
    A.h 0 = thetaOffset theta ∧
      (∀ u v : I, A.h u + A.h v ≤ ((u : ℝ) - v) ^ 2 - (1 / theta) * |(u : ℝ) - v|) ∧
      (∀ᵐ x ∂A.D.toMeasure, A.h (x 0) + A.h (x 1) =
        ((x 0 : ℝ) - x 1) ^ 2 - (1 / theta) * |(x 0 : ℝ) - x 1|) := by
  dsimp only
  let A := thetaCertificate theta ht
  refine ⟨A.at_zero.trans (thetaCertificate_data theta ht).2.2, ?_, ?_⟩
  · simpa only [← thetaCertificate_s theta ht] using A.feasible
  · simpa only [← thetaCertificate_s theta ht] using A.contact

/-- Equation (37), with differentiability itself established almost everywhere. -/
theorem theta_potential_derivative (theta : ℝ) (ht : 0 < theta) :
    ∀ᵐ u : ℝ, DifferentiableAt ℝ (thetaCertificate theta ht).h u ∧
      |deriv (thetaCertificate theta ht).h u| ≤ thetaWidth theta := by
  let A := thetaCertificate theta ht
  filter_upwards [A.lipschitz.ae_differentiableAt] with u hu
  refine ⟨hu, ?_⟩
  have h := norm_deriv_le_of_lipschitz (x₀ := u) A.lipschitz
  change |deriv A.h u| ≤ A.w at h
  exact h.trans_eq (thetaCertificate_width theta ht)

/-- Lemma 3.7's discriminant and lower-root inequalities in the original theta variables. -/
theorem theta_discriminant_inequalities (theta : ℝ) (ht : 0 < theta) :
    theta ^ 2 * (thetaWidth theta) ^ 2 ≤ 1 + 2 * theta ^ 2 * thetaOffset theta ∧
      (1 + theta * thetaWidth theta) / 2 ≤ thetaAlpha theta := by
  have h := source_parameter_inequalities (thetaCertificate theta ht)
  rw [sourceTheta_thetaCertificate, thetaCertificate_width,
    (thetaCertificate_data theta ht).2.2, (theta_splitting theta ht).1] at h
  exact ⟨h.2.1, h.2.2.1⟩

end Papers.AnsariRockelSteinmassl2026RhoGamma
