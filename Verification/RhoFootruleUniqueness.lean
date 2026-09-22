import Verification.DualComplementarity
import Copula.Rank.Region.RhoFootrule.UpperCoverage
import Copula.Rank.Extrema

/-! # Uniqueness along every exact rho--footrule upper arc -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval NNReal

namespace Verification

open Copula.RankRegion.RhoFootrule UpperSpline

private theorem period_gt_v {n v w : ℝ} (hn : 0 < n) (hv : 0 ≤ v)
    (hw : 0 ≤ w) (hp : 0 < period n v w) : v < period n v w := by
  rcases eq_or_lt_of_le hv with h | h
  · simpa only [← h] using hp
  · have hnv := mul_pos hn h
    unfold period
    nlinarith

theorem right_boundary_copula_unique (S : RightData) (C : Copula 2)
    (hp : C.spearmanFootrule = S.copula.spearmanFootrule)
    (hr : C.spearmanRho = S.copula.spearmanRho) : C = S.copula := by
  apply dual_ranks_unique C S.copula S.dual ⟨S.v, S.v_nonneg⟩ (period S.N S.v S.w)
    (potential_lipschitz (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos)
    (period_gt_v (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos)
    (potential_feasible (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos)
    S.cost_attained hp hr

theorem left_boundary_copula_unique (S : LeftData) (C : Copula 2)
    (hp : C.spearmanFootrule = S.copula.spearmanFootrule)
    (hr : C.spearmanRho = S.copula.spearmanRho) : C = S.copula := by
  have hg : LipschitzWith ⟨S.v, S.v_nonneg⟩ S.dual := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := (potential_lipschitz (by exact_mod_cast S.N_pos)
      S.v_nonneg S.w_nonneg S.period_pos).dist_le_mul (x+S.w) (y+S.w)
    simpa only [LeftData.dual, Real.dist_eq, add_sub_add_right_eq_sub] using h
  have hf (a b : ℝ) : S.dual a + S.dual b ≤
      (b-a)^2 - period S.N S.v S.w * |b-a| := by
    have h := potential_feasible (by exact_mod_cast S.N_pos)
      S.v_nonneg S.w_nonneg S.period_pos (a+S.w) (b+S.w)
    simpa only [LeftData.dual, add_sub_add_right_eq_sub] using h
  exact dual_ranks_unique C S.copula S.dual ⟨S.v, S.v_nonneg⟩ (period S.N S.v S.w)
    hg (period_gt_v (by exact_mod_cast S.N_pos) S.v_nonneg S.w_nonneg S.period_pos)
    hf S.cost_attained hp hr

/-- Every arithmetic upper-boundary parameter determines a unique optimizing copula. -/
theorem upper_parameter_copula_unique (a : UpperParameter) (C : Copula 2)
    (hp : C.spearmanFootrule = a.footrule) (hr : C.spearmanRho = a.rho) : C = a.copula := by
  cases a with
  | endpoint => exact C.spearmanRho_eq_one_iff.mp hr
  | right S =>
    exact right_boundary_copula_unique S C (hp.trans (UpperParameter.coefficients (.right S)).1.symm)
      (hr.trans (UpperParameter.coefficients (.right S)).2.symm)
  | left S =>
    exact left_boundary_copula_unique S C (hp.trans (UpperParameter.coefficients (.left S)).1.symm)
      (hr.trans (UpperParameter.coefficients (.left S)).2.symm)

end Verification
