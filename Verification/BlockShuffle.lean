import Verification.Shuffle
import Copula.Rank.Benchmarks

/-! # Permuted finite copula blocks

Allowing arbitrary copulas inside the permuted squares proves the signed
shuffle formula by taking each component to be M or W. Degenerate blocks
have zero measure and require no limiting argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification
namespace ShuffleStrip

noncomputable def blockPoint (S : ShuffleStrip) (u : Fin 2 → I) : Fin 2 → I :=
  fun j => S.point (u j) j

@[fun_prop] theorem continuous_blockPoint (S : ShuffleStrip) : Continuous S.blockPoint := by
  unfold blockPoint
  fun_prop

noncomputable def blockLaw (S : ShuffleStrip) (C : Copula 2) : Measure (Fin 2 → I) :=
  ENNReal.ofReal S.width • C.toMeasure.map S.blockPoint

theorem blockLaw_univ (S : ShuffleStrip) (C : Copula 2) :
    S.blockLaw C univ = ENNReal.ofReal S.width := by
  simp [blockLaw, Measure.map_apply S.continuous_blockPoint.measurable]

instance (S : ShuffleStrip) (C : Copula 2) : IsFiniteMeasure (S.blockLaw C) :=
  ⟨by rw [S.blockLaw_univ]; exact ENNReal.ofReal_lt_top⟩

theorem blockLaw_marginal (S : ShuffleStrip) (C : Copula 2) (j : Fin 2) :
    (S.blockLaw C).map (fun x => x j) = S.law.map (fun x => x j) := by
  rw [blockLaw, law, Measure.map_smul _ (measurable_pi_apply j).aemeasurable,
    Measure.map_smul _ (measurable_pi_apply j).aemeasurable,
    Measure.map_map (measurable_pi_apply j) S.continuous_blockPoint.measurable,
    Measure.map_map (measurable_pi_apply j) S.continuous_point.measurable]
  change ENNReal.ofReal S.width • C.toMeasure.map ((fun u => S.point u j) ∘ (fun x => x j)) = _
  have hm : Measurable (fun u : I => S.point u j) := by fun_prop
  have he := congrArg (fun μ : Measure I => μ.map (fun u => S.point u j)) (C.map_eval j)
  rw [Measure.map_map hm (measurable_pi_apply j)] at he
  exact congrArg (fun μ => ENNReal.ofReal S.width • μ) he

theorem blockLaw_Iic_self (S : ShuffleStrip) (C : Copula 2) (u : Fin 2 → I) :
    (S.blockLaw C).real (Iic (S.blockPoint u)) = S.width * C.cdf u := by
  by_cases hs : S.width = 0
  · simp [blockLaw, hs]
  have hp : 0 < S.width := lt_of_le_of_ne S.width_nonneg (Ne.symm hs)
  have he : S.blockPoint ⁻¹' Iic (S.blockPoint u) = Iic u := by
    ext v
    simp only [mem_preimage, mem_Iic, Pi.le_def]
    apply forall_congr'
    intro j
    fin_cases j
    · change S.x + S.width * (v 0 : ℝ) ≤ S.x + S.width * (u 0 : ℝ) ↔ (v 0 : ℝ) ≤ u 0
      simp only [add_le_add_iff_left, mul_le_mul_iff_right₀ hp]
    · change S.y + S.width * (v 1 : ℝ) ≤ S.y + S.width * (u 1 : ℝ) ↔ (v 1 : ℝ) ≤ u 1
      simp only [add_le_add_iff_left, mul_le_mul_iff_right₀ hp]
  rw [blockLaw, measureReal_ennreal_smul_apply,
    map_measureReal_apply S.continuous_blockPoint.measurable measurableSet_Iic,
    he, ENNReal.toReal_ofReal S.width_nonneg]
  rfl

theorem blockPoint_bounds (S : ShuffleStrip) (u : Fin 2 → I) (j : Fin 2) :
    S.point 0 j ≤ S.blockPoint u j ∧ S.blockPoint u j ≤ S.point 1 j := by
  fin_cases j
  · change S.x + S.width * (0 : ℝ) ≤ S.x + S.width * (u 0 : ℝ) ∧
      S.x + S.width * (u 0 : ℝ) ≤ S.x + S.width * (1 : ℝ)
    constructor <;> nlinarith [S.width_nonneg, (u 0).property.1, (u 0).property.2]
  · change S.y + S.width * (0 : ℝ) ≤ S.y + S.width * (u 1 : ℝ) ∧
      S.y + S.width * (u 1 : ℝ) ≤ S.y + S.width * (1 : ℝ)
    constructor <;> nlinarith [S.width_nonneg, (u 1).property.1, (u 1).property.2]

theorem blockLaw_Iic_full (S : ShuffleStrip) (C : Copula 2) (z : Fin 2 → I)
    (hz : S.point 1 ≤ z) : (S.blockLaw C).real (Iic z) = S.width := by
  have he : S.blockPoint ⁻¹' Iic z = univ := by
    ext v
    simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
    intro j
    exact (S.blockPoint_bounds v j).2.trans (hz j)
  rw [blockLaw, measureReal_ennreal_smul_apply,
    map_measureReal_apply S.continuous_blockPoint.measurable measurableSet_Iic,
    he, probReal_univ, mul_one, ENNReal.toReal_ofReal S.width_nonneg]

theorem blockLaw_Iic_zero (S : ShuffleStrip) (C : Copula 2) (z : Fin 2 → I) (j : Fin 2)
    (hz : z j ≤ S.point 0 j) : (S.blockLaw C).real (Iic z) = 0 := by
  by_cases hs : S.width = 0
  · simp [blockLaw, hs]
  have hp : 0 < S.width := lt_of_le_of_ne S.width_nonneg (Ne.symm hs)
  have he : C.toMeasure (S.blockPoint ⁻¹' Iic z) = 0 := by
    apply measure_mono_null (t := {u | u j ≤ (0 : I)})
    · intro u hu
      have h := (hu j).trans hz
      fin_cases j <;> change (u _ : ℝ) ≤ 0
      all_goals change _ + S.width * (u _ : ℝ) ≤ _ + S.width * (0 : ℝ) at h
      all_goals nlinarith
    · exact (C.measure_eval_le j 0).trans (by norm_num)
  rw [blockLaw, measureReal_ennreal_smul_apply,
    map_measureReal_apply S.continuous_blockPoint.measurable measurableSet_Iic,
    Measure.real, he, ENNReal.toReal_zero, mul_zero]

theorem integral_blockLaw (S : ShuffleStrip) (C : Copula 2)
    {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂S.blockLaw C) = S.width * ∫ u, f (S.blockPoint u) ∂C.toMeasure := by
  rw [blockLaw, integral_smul_measure,
    integral_map S.continuous_blockPoint.measurable.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal S.width_nonneg]
  rfl

end ShuffleStrip

namespace PositiveShuffle

variable {n : ℕ}

noncomputable def blockLaw (S : PositiveShuffle n) (C : Fin n → Copula 2) : Measure (Fin 2 → I) :=
  ∑ i, (S.strip i).blockLaw (C i)

instance (S : PositiveShuffle n) (C : Fin n → Copula 2) : IsFiniteMeasure (S.blockLaw C) := by
  unfold blockLaw
  infer_instance

instance (S : PositiveShuffle n) (C : Fin n → Copula 2) : IsProbabilityMeasure (S.blockLaw C) := by
  constructor
  simp only [blockLaw, Measure.finsetSum_apply, ShuffleStrip.blockLaw_univ]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (S.strip i).width_nonneg), S.total]
  norm_num

noncomputable def blockCopula (S : PositiveShuffle n) (C : Fin n → Copula 2) : Copula 2 where
  measure := ⟨S.blockLaw C, inferInstance⟩
  marginal_eq j := by
    change (∑ i, (S.strip i).blockLaw (C i)).map (fun x => x j) = volume
    rw [Measure.map_finset_sum]
    · simp_rw [ShuffleStrip.blockLaw_marginal]
      rw [← Measure.map_finset_sum]
      · exact S.marginal j
      · exact (measurable_pi_apply j).aemeasurable
    · exact (measurable_pi_apply j).aemeasurable

theorem block_cdf (S : PositiveShuffle n) (C : Fin n → Copula 2) (z : Fin 2 → I) :
    (S.blockCopula C).cdf z = ∑ i, ((S.strip i).blockLaw (C i)).real (Iic z) := by
  change (S.blockLaw C (Iic z)).toReal = _
  rw [blockLaw, Measure.finsetSum_apply, ENNReal.toReal_sum]
  · rfl
  · intro i _
    exact measure_ne_top _ _

theorem block_cdf_point (S : PositiveShuffle n) (C : Fin n → Copula 2) (π : Equiv.Perm (Fin n))
    (hx : ∀ i j, i < j → (S.strip i).x + (S.strip i).width ≤ (S.strip j).x)
    (hy : ∀ i j, π i < π j → (S.strip i).y + (S.strip i).width ≤ (S.strip j).y)
    (i : Fin n) (u : Fin 2 → I) :
    (S.blockCopula C).cdf ((S.strip i).blockPoint u) =
      (S.strip i).width * (C i).cdf u + ∑ j, if j < i ∧ π j < π i then (S.strip j).width else 0 := by
  rw [S.block_cdf]
  have ht (j : Fin n) : ((S.strip j).blockLaw (C j)).real (Iic ((S.strip i).blockPoint u)) =
      (if j = i then (S.strip i).width * (C i).cdf u else 0) +
        (if j < i ∧ π j < π i then (S.strip j).width else 0) := by
    have hw := (S.strip i).width_nonneg
    by_cases hij : j = i
    · subst j
      simp [ShuffleStrip.blockLaw_Iic_self]
    rw [ite_eq_right hij, zero_add]
    by_cases hji : j < i ∧ π j < π i
    · rw [ite_eq_left hji]
      apply ShuffleStrip.blockLaw_Iic_full
      intro k
      fin_cases k
      · change (S.strip j).x + (S.strip j).width * 1 ≤ (S.strip i).x + (S.strip i).width * (u 0 : ℝ)
        nlinarith [hx j i hji.1, (u 0).property.1]
      · change (S.strip j).y + (S.strip j).width * 1 ≤ (S.strip i).y + (S.strip i).width * (u 1 : ℝ)
        nlinarith [hy j i hji.2, (u 1).property.1]
    rw [ite_eq_right hji]
    by_cases hj : j < i
    · have hπ : π i < π j := lt_of_le_of_ne (le_of_not_gt (fun h => hji ⟨hj, h⟩))
        (fun he => hij (π.injective he.symm))
      apply ShuffleStrip.blockLaw_Iic_zero _ _ _ 1
      change (S.strip i).y + (S.strip i).width * (u 1 : ℝ) ≤ (S.strip j).y + (S.strip j).width * 0
      nlinarith [hy i j hπ, (u 1).property.2]
    · have hi : i < j := lt_of_le_of_ne (le_of_not_gt hj) (Ne.symm hij)
      apply ShuffleStrip.blockLaw_Iic_zero _ _ _ 0
      change (S.strip i).x + (S.strip i).width * (u 0 : ℝ) ≤ (S.strip j).x + (S.strip j).width * 0
      nlinarith [hx i j hi, (u 0).property.2]
  simp_rw [ht, Finset.sum_add_distrib]
  simp

theorem integral_blockCopula (S : PositiveShuffle n) (C : Fin n → Copula 2)
    {f : (Fin 2 → I) → ℝ} (hf : Continuous f) :
    (∫ x, f x ∂(S.blockCopula C).toMeasure) =
      ∑ i, (S.strip i).width * ∫ u, f ((S.strip i).blockPoint u) ∂(C i).toMeasure := by
  change (∫ x, f x ∂(∑ i, (S.strip i).blockLaw (C i))) = _
  rw [integral_finsetSum_measure]
  · exact Finset.sum_congr rfl fun i _ => (S.strip i).integral_blockLaw (C i) hf
  · intro i _
    exact Copula.integrable_continuous_cube _ hf

theorem block_tau_raw (S : PositiveShuffle n) (C : Fin n → Copula 2) (π : Equiv.Perm (Fin n))
    (hx : ∀ i j, i < j → (S.strip i).x + (S.strip i).width ≤ (S.strip j).x)
    (hy : ∀ i j, π i < π j → (S.strip i).y + (S.strip i).width ≤ (S.strip j).y) :
    (S.blockCopula C).kendallTau =
      (∑ i, ((S.strip i).width ^ 2 * ((C i).kendallTau + 1) +
        4 * (S.strip i).width * ∑ j, if j < i ∧ π j < π i then (S.strip j).width else 0)) - 1 := by
  rw [Copula.kendallTau, S.integral_blockCopula C (S.blockCopula C).continuous_cdf]
  simp_rw [S.block_cdf_point C π hx hy]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_add ((C i).integrable_cdf (C i).toMeasure |>.const_mul _) (integrable_const _),
    integral_const_mul, integral_const]
  simp only [probReal_univ, smul_eq_mul, one_mul, Copula.kendallTau]
  ring

private theorem sum_square_split (w : Fin n → ℝ) :
    (∑ i, w i) ^ 2 = (∑ i, w i ^ 2) +
      2 * ∑ i, ∑ j, if j < i then w i * w j else 0 := by
  classical
  have hp (i j : Fin n) : w i * w j =
      (if j = i then w i ^ 2 else 0) +
      (if j < i then w i * w j else 0) +
      (if i < j then w i * w j else 0) := by
    rcases lt_trichotomy j i with h | h | h <;> simp [h, ne_of_lt, ne_of_gt, not_lt_of_ge, le_of_lt, sq]
  have he : (∑ i, ∑ j, if i < j then w i * w j else 0) =
      ∑ i, ∑ j, if j < i then w i * w j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : j < i <;> simp [h, mul_comm]
  calc
    (∑ i, w i) ^ 2 = ∑ i, ∑ j, w i * w j := by rw [sq, Finset.sum_mul]; simp_rw [Finset.mul_sum]
    _ = (∑ i, w i ^ 2) + (∑ i, ∑ j, if j < i then w i * w j else 0) +
        (∑ i, ∑ j, if i < j then w i * w j else 0) := by
      conv_lhs =>
        arg 2
        ext i
        arg 2
        ext j
        rw [hp]
      simp only [Finset.sum_add_distrib]
      simp
    _ = _ := by rw [he]; ring

theorem block_tau (S : PositiveShuffle n) (C : Fin n → Copula 2) (π : Equiv.Perm (Fin n))
    (hx : ∀ i j, i < j → (S.strip i).x + (S.strip i).width ≤ (S.strip j).x)
    (hy : ∀ i j, π i < π j → (S.strip i).y + (S.strip i).width ≤ (S.strip j).y) :
    (S.blockCopula C).kendallTau =
      (∑ i, (C i).kendallTau * (S.strip i).width ^ 2) +
      2 * ∑ i, ∑ j, if j < i then
        (if π j < π i then 1 else -1) * (S.strip j).width * (S.strip i).width else 0 := by
  classical
  let w := fun i => (S.strip i).width
  have hpart := sum_square_split w
  have htotal : ∑ i, w i = 1 := S.total
  rw [htotal, one_pow] at hpart
  have hsign : (∑ i, ∑ j, if j < i then
        (if π j < π i then (1 : ℝ) else -1) * w j * w i else 0) =
      2 * (∑ i, w i * ∑ j, if j < i ∧ π j < π i then w j else 0) -
        ∑ i, ∑ j, if j < i then w i * w j else 0 := by
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j < i <;> by_cases hπ : π j < π i <;> simp [hj, hπ] <;> ring
  have hraw := S.block_tau_raw C π hx hy
  change (S.blockCopula C).kendallTau =
    (∑ i, (w i ^ 2 * ((C i).kendallTau + 1) +
      4 * w i * ∑ j, if j < i ∧ π j < π i then w j else 0)) - 1 at hraw
  have hterms : (∑ i, w i ^ 2 * ((C i).kendallTau + 1)) =
      (∑ i, (C i).kendallTau * w i ^ 2) + ∑ i, w i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Finset.sum_add_distrib, hterms] at hraw
  simp_rw [mul_assoc (4 : ℝ)] at hraw
  rw [← Finset.mul_sum] at hraw
  change (S.blockCopula C).kendallTau = (∑ i, (C i).kendallTau * w i ^ 2) +
    2 * ∑ i, ∑ j, if j < i then
      (if π j < π i then 1 else -1) * w j * w i else 0
  rw [hsign]
  linarith

/-- A signed shuffle of M: `true` selects a diagonal and `false` an antidiagonal. -/
noncomputable def signedCopula (S : PositiveShuffle n) (ε : Fin n → Bool) : Copula 2 :=
  S.blockCopula (fun i => if ε i then Copula.comonotonic 2 else Copula.countermonotonic)

/-- The signed shuffle identity, with the pair sum written over `j < i`. -/
theorem signed_tau (S : PositiveShuffle n) (ε : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (hx : ∀ i j, i < j → (S.strip i).x + (S.strip i).width ≤ (S.strip j).x)
    (hy : ∀ i j, π i < π j → (S.strip i).y + (S.strip i).width ≤ (S.strip j).y) :
    (S.signedCopula ε).kendallTau =
      (∑ i, (if ε i then 1 else -1) * (S.strip i).width ^ 2) +
      2 * ∑ i, ∑ j, if j < i then
        (if π j < π i then 1 else -1) * (S.strip j).width * (S.strip i).width else 0 := by
  unfold signedCopula
  rw [S.block_tau _ π hx hy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases ε i <;> simp

end PositiveShuffle
end Verification
