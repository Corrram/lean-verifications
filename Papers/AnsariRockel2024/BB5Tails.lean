import Papers.AnsariRockel2024.BB5Dependence
import Verification.PickandsDiagonal

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem bb5_extremalCoefficient (θ δ : ℝ) (hθ : 1≤θ) (hδ : 0<δ) :
    (Verification.bb5 θ δ hθ hδ).extremalCoefficient=(2-(2:ℝ)^(-1/δ))^(1/θ) := by
  rw [Verification.extremalCoefficient_eq_twice_pickands _ (bb5_isExtremeValue θ δ hθ hδ),
    bb5_pickands_interior θ δ hθ hδ unitHalf (by norm_num [unitHalf])]
  norm_num only [unitHalf,show (1:ℝ)-1/2=1/2 by norm_num]
  have he := Verification.bb5TailKernel_homogeneous θ δ (1/2) 1 1 hθ hδ
    (by norm_num) (by norm_num) (by norm_num)
  simp only [mul_one] at he
  rw [he]
  simp only [Verification.bb5TailKernel,Verification.galambosTailKernel,Real.one_rpow]
  ring_nf

private theorem bb5_exponent_gt_one (θ δ : ℝ) (hθ : 1≤θ) (hδ : 0<δ) :
    1<(2-(2:ℝ)^(-1/δ))^(1/θ) := by
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2)
    (div_neg_of_neg_of_pos (by norm_num : (-1:ℝ)<0) hδ)
  rw [Real.rpow_zero] at h
  exact Real.one_lt_rpow (by linarith) (by positivity)

theorem bb5_tails (θ δ : ℝ) (hθ : 1≤θ) (hδ : 0<δ) :
    (Verification.bb5 θ δ hθ hδ).HasLowerTailDependence 0 ∧
    (Verification.bb5 θ δ hθ hδ).HasUpperTailDependence (2-(2-(2:ℝ)^(-1/δ))^(1/θ)) := by
  have hp := (bb5_isExtremeValue θ δ hθ hδ).hasPowerDiagonal
  rw [bb5_extremalCoefficient θ δ hθ hδ] at hp
  exact ⟨hp.hasLowerTailDependence_zero (bb5_exponent_gt_one θ δ hθ hδ),hp.hasUpperTailDependence⟩

end Papers.AnsariRockel2024
