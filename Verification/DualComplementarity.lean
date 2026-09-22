import Verification.DualOptimizerUniqueness
import Copula.Rank.Region.RhoFootrule.Moments

/-! # Complementary slackness for the rho--footrule dual -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval NNReal

namespace Verification

/-- An attained dual cost forces equality in the dual constraint almost everywhere. -/
theorem dual_contact_of_cost_eq (C : Copula 2) (g : ℝ → ℝ) (θ : ℝ) (hg : Continuous g)
    (hf : ∀ a b : ℝ, g a + g b ≤ (b-a)^2 - θ * |b-a|)
    (he : (∫ x, ((x 0 : ℝ)-x 1)^2 ∂C.toMeasure) -
      θ * (∫ x, |(x 0 : ℝ)-x 1| ∂C.toMeasure) = 2 * ∫ u : I, g u) :
    ∀ᵐ x ∂C.toMeasure,
      g (x 0) + g (x 1) = ((x 1 : ℝ)-x 0)^2 - θ * |(x 1 : ℝ)-x 0| := by
  let f := fun x : Fin 2 → I => ((x 0 : ℝ)-x 1)^2 -
    θ * |(x 0 : ℝ)-x 1| - (g (x 0) + g (x 1))
  have hi : Integrable f C.toMeasure := Copula.integrable_continuous_cube _ (by fun_prop)
  have hf0 : ∀ x, 0 ≤ f x := by
    intro x
    have h := hf (x 1) (x 0)
    dsimp [f]
    linarith
  have hgi : (∫ x, g (x 0) + g (x 1) ∂C.toMeasure) = 2 * ∫ u : I, g u := by
    rw [integral_add (Copula.integrable_continuous_cube _ (by fun_prop))
      (Copula.integrable_continuous_cube _ (by fun_prop)),
      C.integral_eval 0 (fun u : I => g u) (by fun_prop),
      C.integral_eval 1 (fun u : I => g u) (by fun_prop)]
    ring
  have hz : (∫ x, f x ∂C.toMeasure) = 0 := by
    dsimp [f]
    rw [integral_sub (Copula.integrable_continuous_cube _ (by fun_prop))
        (Copula.integrable_continuous_cube _ (by fun_prop)),
      integral_sub (Copula.integrable_continuous_cube _ (by fun_prop))
        (Copula.integrable_continuous_cube _ (by fun_prop)), integral_const_mul, hgi, he, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg hf0 hi).mp hz
  filter_upwards [hae] with x hx
  dsimp [f] at hx
  rw [sub_sq_comm, abs_sub_comm]
  linarith

/-- An attained strictly Lipschitz dual identifies every copula with the same two ranks. -/
theorem dual_ranks_unique (C D : Copula 2) (g : ℝ → ℝ) (v : ℝ≥0) (θ : ℝ)
    (hg : LipschitzWith v g) (hθ : (v : ℝ) < θ)
    (hf : ∀ a b : ℝ, g a + g b ≤ (b-a)^2 - θ * |b-a|)
    (he : (∫ x, ((x 0 : ℝ)-x 1)^2 ∂D.toMeasure) -
      θ * (∫ x, |(x 0 : ℝ)-x 1| ∂D.toMeasure) = 2 * ∫ u : I, g u)
    (hp : C.spearmanFootrule = D.spearmanFootrule)
    (hr : C.spearmanRho = D.spearmanRho) : C = D := by
  have hp' := hp
  have hr' := hr
  rw [Copula.RankRegion.footrule_eq_abs_moment,
    Copula.RankRegion.footrule_eq_abs_moment] at hp'
  rw [Copula.spearmanRho_eq_one_sub, Copula.spearmanRho_eq_one_sub] at hr'
  have hm₁ : (∫ x, |(x 0 : ℝ)-x 1| ∂C.toMeasure) =
      ∫ x, |(x 0 : ℝ)-x 1| ∂D.toMeasure := by linarith only [hp']
  have hm₂ : (∫ x, ((x 0 : ℝ)-x 1)^2 ∂C.toMeasure) =
      ∫ x, ((x 0 : ℝ)-x 1)^2 ∂D.toMeasure := by linarith only [hr']
  apply copula_dual_contact_unique C D g v θ hg hθ hf
  · apply dual_contact_of_cost_eq C g θ hg.continuous hf
    rwa [hm₁, hm₂]
  · exact dual_contact_of_cost_eq D g θ hg.continuous hf he

end Verification
