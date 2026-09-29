import Papers.OrendayLaresRockel2026XiBeta.RBranchOrdinal
import Papers.OrendayLaresRockel2026XiBeta.RBranchRank

/-! # Proposition 5.3 (two-branch copulas `R_b`), assembled

* the law: `R_b` is the copula of `(U, V_b)` (`Rb_eq_ofMap`, `Rb_toMeasure_eq_lawVb`);
* (i) singular, SI, radially symmetric; for `b < 1` neither `R_b` exchangeable nor `R_bᵀ` SI;
  `R_1 = M`;
* (ii) ordinal sum of `M`, `R_0`, `M` for `0 < b < 1`;
* (iii) `β(R_b) = b`, `ξ(R_b) = 1 - (3/4)(1-b)²`;
* (iv) `τ(R_b) = 1 - (1/2)(1-b)²`, `ρ(R_b) = 1 - (1/2)(1-b)³`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- Proposition 5.3 (i): singular, SI and radially symmetric, for all `b ∈ [0,1]`; not exchangeable
and with non-SI transpose for `b < 1`; and `R_1 = M`. -/
theorem proposition_5_3_i (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    (Rb b hb).toMeasure ⟂ₘ (volume : Measure (Fin 2 → I)) ∧ (Rb b hb).IsSI ∧
      (Rb b hb).IsRadiallySymmetric ∧
      (b < 1 → ¬ (Rb b hb).IsExchangeable ∧ ¬ (Rb b hb).transpose.IsSI) ∧
      (b = 1 → Rb b hb = Copula.comonotonic 2) :=
  ⟨Rb_singular hb, Rb_isSI hb, Rb_isRadiallySymmetric hb,
    fun h => ⟨Rb_not_exchangeable hb h, Rb_transpose_not_isSI hb h⟩,
    fun h => by subst h; exact Rb_one_eq_comonotonic hb⟩

/-- Proposition 5.3 (ii): for `0 < b < 1`, `R_b` is the ordinal sum of `M`, `R_0`, `M` with
respect to the partition `{[0, b/2], [b/2, 1 - b/2], [1 - b/2, 1]}`. -/
theorem proposition_5_3_ii (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) (h0 : 0 < b) (h1 : b < 1) :
    Rb b hb = Copula.finiteOrdinalSum (rbPartition b h0 h1)
      ![Copula.comonotonic 2, Rb 0 zero_mem_Icc01, Copula.comonotonic 2] :=
  Rb_eq_finiteOrdinalSum hb h0 h1

/-- Proposition 5.3 (iii) and (iv): `β`, `ξ`, `τ`, `ρ` of `R_b`. -/
theorem proposition_5_3_iii_iv (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    (Rb b hb).blomqvistBeta = b ∧ (Rb b hb).chatterjeeXi = 1 - 3 / 4 * (1 - b) ^ 2 ∧
      (Rb b hb).kendallTau = 1 - 1 / 2 * (1 - b) ^ 2 ∧
      (Rb b hb).spearmanRho = 1 - 1 / 2 * (1 - b) ^ 3 :=
  ⟨Rb_beta hb, xi_Rb b hb, kendallTau_Rb hb, spearmanRho_Rb hb⟩

/-- Proposition 5.3, first statement: `R_b` is the copula of `(U, V_b)` for independent
`U ~ U(0,1)` and fair coin `ε`, and `V_b` is uniform. -/
theorem proposition_5_3_law (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    Rb b hb = Copula.ofMap probVb (Xb b) (measurable_Xb b) (marginals_Xb hb) ∧
      (Rb b hb).toMeasure = lawVb b :=
  ⟨Rb_eq_ofMap hb, Rb_toMeasure_eq_lawVb hb⟩

end Papers.OrendayLaresRockel2026XiBeta
