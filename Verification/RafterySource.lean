import Copula.Classical
import Copula.TailDependence.Examples
import Copula.Dependence.TotalPositivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

/-- Literal Raftery expression in arXiv v3 Table 1, before correcting its coefficient. -/
noncomputable def rafteryPrintedCDF (δ u v : ℝ) : ℝ :=
  min u v + (1-δ)*(u*v)^(1/(1-δ))*(1-(max u v)^(-(1+δ)/(1-δ)))

theorem rafteryPrintedCDF_half_witness :
    rafteryPrintedCDF (1/2) (7/8) (7/8) = 5985/8192 := by
  norm_num [rafteryPrintedCDF]

/-- The literal printed formula cannot be the CDF of a copula. -/
theorem raftery_printed_cdf_not_copula :
    ¬∃ C : Copula 2, ∀ u v : I,
      C.cdf ![u,v] = rafteryPrintedCDF (1/2) u v := by
  rintro ⟨C,hC⟩
  let t : I := ⟨7/8, by norm_num⟩
  have hb := C.sum_sub_dim_add_one_le_cdf ![t,t]
  rw [hC] at hb
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_ofNat] at hb
  change (7/8:ℝ)+(7/8)-2+1 ≤ rafteryPrintedCDF (1/2) (7/8) (7/8) at hb
  rw [rafteryPrintedCDF_half_witness] at hb
  norm_num at hb

/-- The declared independence endpoint has a TP2 Lebesgue density. -/
theorem raftery_zero_density {C : Copula 2} (hC : C = independence 2) :
    C.HasMTP2Density := by
  rw [hC]
  exact hasMTP2Density_independence 2

/-- The declared comonotonic endpoint has upper-tail coefficient one, not zero. -/
theorem raftery_one_upperTail {C : Copula 2} (hC : C = comonotonic 2) :
    C.HasUpperTailDependence 1 ∧ ¬C.HasUpperTailDependence 0 := by
  rw [hC]
  refine ⟨hasUpperTailDependence_comonotonic, ?_⟩
  intro hz
  have he := hasUpperTailDependence_comonotonic.unique hz
  norm_num at he

end Verification
