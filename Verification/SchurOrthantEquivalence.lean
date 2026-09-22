import Verification.ConvexMajorization
import Verification.CopulaRowOrder
import Verification.RowConvexConvergence
import Verification.SchurOrthantBound

/-! # Equivalence of Schur and orthant order for monotone conditional distributions -/

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval BigOperators Topology

namespace Verification

/-- Ordered CDF prefixes imply every convex test inequality for finite row averages.
Only the smaller copula needs to be conditionally increasing. -/
theorem rowMeanTest_le_of_lowerOrthantLE (C D : Copula 2) (hC : C.IsSI)
    (h : C.LowerOrthantLE D) (m : ℕ) (hm : 0<m) (v : I)
    (φ : ℝ → ℝ) (hc : Continuous φ) (hφ : ConvexOn ℝ (Icc 0 1) φ) :
    rowMeanTest (IntervalPartition.uniform m hm) C v φ ≤
      rowMeanTest (IntervalPartition.uniform m hm) D v φ := by
  let P := IntervalPartition.uniform m hm
  have hp (k : Fin (m+1)) :
      (∑ i : Fin m, if i.val < k.val then copulaRowMean P C i v else 0) ≤
        ∑ i : Fin m, if i.val < k.val then copulaRowMean P D i v else 0 := by
    rw [uniform_rowMean_prefix,uniform_rowMean_prefix]
    exact mul_le_mul_of_nonneg_left (h _) (Nat.cast_nonneg m)
  have ht : (∑ i, copulaRowMean P D i v) = ∑ i, copulaRowMean P C i v := by
    have ha := uniform_rowMean_prefix C m hm (Fin.last m) v
    have hb := uniform_rowMean_prefix D m hm (Fin.last m) v
    simp only [Fin.val_last,Fin.is_lt,ite_true] at ha hb
    rw [ha,hb]
    simp only [IntervalPartition.one,Copula.cdf_two_one_left]
  have he := majorization_fin_sum_convex (fun i => copulaRowMean P D i v)
    (fun i => copulaRowMean P C i v) (uniform_rowMean_antitone C hC m hm v) hp ht
    (fun i => copulaRowMean_mem P D i v) (fun i => copulaRowMean_mem P C i v) φ hc hφ
  unfold rowMeanTest
  simp only [IntervalPartition.width_uniform,← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left he (by positivity)

/-- CDF order above a conditionally increasing copula implies Schur order;
the larger copula need not be conditionally increasing. -/
theorem schurLE_of_lowerOrthantLE_isSI (C D : Copula 2) (hC : C.IsSI)
    (h : C.LowerOrthantLE D) : C.SchurLE D := by
  intro v φ hc hφ
  exact le_of_tendsto_of_tendsto (rowMeanTest_tendsto C v φ hc)
    (rowMeanTest_tendsto D v φ hc) (Eventually.of_forall fun k =>
      rowMeanTest_le_of_lowerOrthantLE C D hC h (k+1) (by omega) v φ hc hφ)

/-- Lemma 2.6(ii), including singular conditionally increasing copulas. -/
theorem schurLE_iff_lowerOrthantLE_isSI (C D : Copula 2) (hC : C.IsSI) (hD : D.IsSI) :
    C.SchurLE D ↔ C.LowerOrthantLE D :=
  ⟨fun h => lowerOrthantLE_of_schurLE_isSI C D h hD,
    fun h => schurLE_of_lowerOrthantLE_isSI C D hC h⟩

/-- Lemma 2.8(ii): for conditionally decreasing copulas the CDF direction reverses. -/
theorem schurLE_iff_lowerOrthantLE_isSD (C D : Copula 2) (hC : C.IsSD) (hD : D.IsSD) :
    C.SchurLE D ↔ D.LowerOrthantLE C := by
  constructor
  · exact fun h => lowerOrthantLE_of_schurLE_isSD C D h hD
  · intro h
    apply (schurLE_reflect_second_iff C D).mp
    apply schurLE_of_lowerOrthantLE_isSI _ _ ((Copula.isSI_reflect_second_iff C).mpr hC)
    intro x
    have hh := h ![x 0,unitInterval.symm (x 1)]
    have hx : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
    rw [hx,Copula.cdf_reflect_second,Copula.cdf_reflect_second]
    linarith

end Verification
