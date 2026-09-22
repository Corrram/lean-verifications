import Verification.PatchworkLaw
import Copula.Rank.Benchmarks

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Verification

theorem affine_product_integral (C : Copula 2) (a b w z : ℝ) :
    (∫ x, (a+w*(x 0 : ℝ))*(b+z*(x 1 : ℝ)) ∂C.toMeasure) =
      (a+w/2)*(b+z/2)+w*z*C.spearmanRho/12 := by
  have he (x : Fin 2 → I) : (a+w*(x 0 : ℝ))*(b+z*(x 1 : ℝ)) =
      a*b + (a*z)*(x 1 : ℝ) + (w*b)*(x 0 : ℝ) + (w*z)*((x 0 : ℝ)*(x 1 : ℝ)) := by ring
  simp_rw [he]
  rw [integral_add,integral_add,integral_add]
  · simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,integral_const_mul,
      Copula.integral_coe_eval,Copula.spearmanRho]
    ring
  all_goals exact Copula.integrable_continuous_cube _ (by fun_prop)

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

theorem patchwork_rho_formula (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) :
    (A.patchwork C).spearmanRho =
      12*(∑ i, ∑ j, A.mass i j *
        (((P.point i.castSucc : ℝ)+P.width i/2)*((Q.point j.castSucc : ℝ)+Q.width j/2)+
          P.width i*Q.width j*(C i j).spearmanRho/12))-3 := by
  rw [Copula.spearmanRho,integral_patchwork A C (by fun_prop)]
  simp only [partitionCellMap,partitionEmbed,Matrix.cons_val_zero,Matrix.cons_val_one,
    affine_product_integral]

theorem patchwork_rho_correction (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) :
    (A.patchwork C).spearmanRho = A.checkerboard.spearmanRho +
      ∑ i, ∑ j, A.mass i j * P.width i * Q.width j * (C i j).spearmanRho := by
  rw [patchwork_rho_formula,CellMass.checkerboard,patchwork_rho_formula]
  simp only [Copula.spearmanRho_independence,mul_zero,zero_div,add_zero]
  have hs : (∑ i, ∑ j, A.mass i j *
        (((P.point i.castSucc : ℝ)+P.width i/2)*((Q.point j.castSucc : ℝ)+Q.width j/2)+
          P.width i*Q.width j*(C i j).spearmanRho/12)) =
      (∑ i, ∑ j, A.mass i j * ((P.point i.castSucc : ℝ)+P.width i/2)*((Q.point j.castSucc : ℝ)+Q.width j/2)) +
      (∑ i, ∑ j, A.mass i j * P.width i * Q.width j * (C i j).spearmanRho)/12 := by
    simp only [Finset.sum_div,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  simp only [mul_assoc]
  ring

end Verification
