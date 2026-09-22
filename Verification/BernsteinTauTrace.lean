import Verification.BernsteinTheta
import Verification.BernsteinTau
import Verification.RankOneTrace

open MeasureTheory ProbabilityTheory Matrix
open scoped unitInterval BigOperators

namespace Verification

noncomputable def bernsteinGridMatrix (C : Copula 2) (m n : ℕ) : Matrix (Fin (m+1)) (Fin (n+1)) ℝ :=
  fun i j => C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ]

noncomputable def bernsteinThetaMatrix (k : ℕ) : Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
  Matrix.of (bernsteinTheta k)

private theorem theta_boundary (k : ℕ) :
    bernsteinThetaMatrix k + (bernsteinThetaMatrix k)ᵀ =
      (2 : ℝ) • Matrix.single (Fin.last k) (Fin.last k) (1 : ℝ) := by
  ext i r
  simp only [Matrix.add_apply,Matrix.transpose_apply,bernsteinTheta_add_transpose,
    bernsteinThetaMatrix,Matrix.smul_apply,Matrix.single,Matrix.of_apply,smul_eq_mul,bernsteinTheta_add_transpose]
  simp only [eq_comm]
  split_ifs <;> norm_num

/-- Proposition 3.1's exact printed trace formula, including the exceptional corner convention. -/
theorem bernstein_tau_trace (C : Copula 2) (m n : ℕ) :
    (C.bernstein (m+1) (n+1) (by omega) (by omega)).kendallTau =
      1 - Matrix.trace (bernsteinThetaMatrix m * bernsteinGridMatrix C m n *
        bernsteinThetaMatrix n * (bernsteinGridMatrix C m n)ᵀ) := by
  let D := bernsteinGridMatrix C m n
  have hD : D (Fin.last m) (Fin.last n)=1 := by
    have hm : (Fin.last m).succ=Fin.last (m+1) := by ext; rfl
    have hn : (Fin.last n).succ=Fin.last (n+1) := by ext; rfl
    simp [D,bernsteinGridMatrix,hm,hn,_root_.bernstein.z_last]
  have ht := boundary_trace_identity (bernsteinThetaMatrix m) (bernsteinThetaMatrix n) D
    (Fin.last m) (Fin.last n) (theta_boundary m) (theta_boundary n) hD
  have hs : Matrix.trace (bernsteinThetaMatrix m * D * (bernsteinThetaMatrix n)ᵀ * Dᵀ) =
      4 * (∑ i : Fin (m+1), ∑ j : Fin (n+1), ∑ r : Fin (m+1), ∑ s : Fin (n+1),
        D i j * D r s * bernsteinMixedGram (m+1) i r * bernsteinMixedGram (n+1) j s) := by
    rw [trace_tensor_contraction]
    simp only [bernsteinThetaMatrix,Matrix.of_apply,bernsteinTheta_eq_mixedGram,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [bernstein_tau_finite_sum]
  change 4 * (∑ i, ∑ j, ∑ r, ∑ s,
    D i j * D r s * bernsteinMixedGram (m+1) i r * bernsteinMixedGram (n+1) j s) - 1 = _
  rw [← hs]
  linarith

end Verification
