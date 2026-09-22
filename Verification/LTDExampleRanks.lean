import Verification.LTDExample

open MeasureTheory ProbabilityTheory Set Matrix
open Copula
open scoped unitInterval BigOperators

namespace Verification.LTDExample

theorem thirdMatrix_footrule (p : ℝ) (hp : p ∈ Icc 0 1) :
    (thirdMatrix p hp).checkerboard.spearmanFootrule=(2+4*p)/9 := by
  let A := thirdMatrix p hp
  let P := IntervalPartition.uniform 3 (by omega)
  rw [Copula.spearmanFootrule]
  change 6*(∫ u : I, A.checkerboard.cdf ![u,u])-2=_
  have hm : Measurable (fun u : I => A.checkerboard.cdf ![u,u]) :=
    A.checkerboard.continuous_cdf.measurable.comp (by fun_prop)
  have hi (i : Fin 3) : Integrable (fun u : I => A.checkerboard.cdf ![partitionEmbed P i u,partitionEmbed P i u]) :=
    Copula.integrable_continuous_unit volume (A.checkerboard.continuous_cdf.comp (by have hc := partitionEmbed_continuous P i; fun_prop))
  rw [integral_partition P _ hm hi]
  have he (i : Fin 3) (u : I) : A.checkerboard.cdf ![partitionEmbed P i u,partitionEmbed P i u]=
      ![(u : ℝ)^2/3,1/3+p/3*(u : ℝ)^2,1/3+p/3+2*(1-p)/3*(u : ℝ)+p/3*(u : ℝ)^2] i := by
    rw [CellMass.cdf_checkerboard]
    have hc (j : Fin 3) : (IntervalPartition.uniform 3 (by omega)).coord j (partitionEmbed P i u)=
        if j < i then 1 else if j=i then u else 0 := partition_coord_embed P i j u
    simp only [hc]
    fin_cases i
    · norm_num [A,thirdMatrix,Fin.sum_univ_succ,partition_coord_embed]
      ring
    · norm_num [A,thirdMatrix,Fin.sum_univ_succ,partition_coord_embed]
      ring
      simp
    · norm_num [A,thirdMatrix,Fin.sum_univ_succ,partition_coord_embed]
      ring
  simp_rw [he]
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero,add_zero]
  have hw (i : Fin 3) : P.width i=1/3 := IntervalPartition.width_uniform _ _ _
  simp only [hw]
  have hi : Integrable (fun u : I => (u : ℝ)) := Copula.integrable_continuous_unit volume (by fun_prop)
  have hs : Integrable (fun u : I => (u : ℝ)^2) := Copula.integrable_continuous_unit volume (by fun_prop)
  norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,Fin.reduceFinMk]
  rw [integral_div,integral_add (integrable_const _) (hs.const_mul _),
    integral_add (f := fun u : I => 1/3+p/3+2*(1-p)/3*(u : ℝ))
      ((integrable_const _).add (hi.const_mul _)) (hs.const_mul _),
    integral_add (f := fun _ : I => 1/3+p/3) (integrable_const _) (hi.const_mul _)]
  simp only [integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul,
    Copula.integral_unit_id,Copula.integral_unit_pow]
  norm_num
  ring

end Verification.LTDExample
