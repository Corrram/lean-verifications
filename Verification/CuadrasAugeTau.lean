import Verification.CuadrasAugeXi
import Verification.SymmetricTriangleIntegral

/-! # Exact Kendall tau of the Cuadras–Augé family -/

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval

namespace Verification

theorem cuadrasAuge_kendallTau (δ : I) :
    (cuadrasAuge δ).kendallTau=(δ:ℝ)/(2-(δ:ℝ)) := by
  let C := cuadrasAuge δ
  have hCt : C.transpose=C := marshallOlkin_transpose δ δ
  have hm : Measurable (fun p : I × I => C.conditionalCDF p.1 p.2*C.conditionalCDF p.2 p.1) :=
    (C.measurable_conditionalCDF.comp measurable_swap).mul C.measurable_conditionalCDF
  have hb (p : I × I) : C.conditionalCDF p.1 p.2*C.conditionalCDF p.2 p.1 ∈ Icc (0:ℝ) 1 :=
    ⟨mul_nonneg (C.conditionalCDF_nonneg _ _) (C.conditionalCDF_nonneg _ _),
      (mul_le_of_le_one_left (C.conditionalCDF_nonneg _ _) (C.conditionalCDF_le_one _ _)).trans (C.conditionalCDF_le_one _ _)⟩
  have htriangle := integral_symmetric_triangle _ hm hb (fun p => mul_comm _ _)
  have ha : ∀ᵐ u : I,∀ᵐ v : I,C.conditionalCDF u v=cuadrasConditional δ u v :=
    (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun v u => C.conditionalCDF u v=cuadrasConditional δ u v)
      (measurableSet_eq_fun C.measurable_conditionalCDF
        ((cuadrasConditional_measurable δ).comp measurable_swap))).mp
      (Eventually.of_forall (conditionalCDF_cuadrasAuge δ))
  have he : (∫ u : I,∫ v in Iic u,C.conditionalCDF u v*C.conditionalCDF v u)=
      ∫ u : I,(1-(δ:ℝ))*(u:ℝ)^(3-2*(δ:ℝ))/2 := by
    apply integral_congr_ae
    filter_upwards [ha,Measure.ae_ne volume (0:I)] with u hu hu0
    have hup : (0:ℝ)<u := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu0 (Subtype.ext h)))
    have hprod : (fun v : I => C.conditionalCDF u v*C.conditionalCDF v u) =ᵐ[volume.restrict (Iic u)]
        fun v => ((1-(δ:ℝ))*(u:ℝ)^(1-2*(δ:ℝ)))*(v:ℝ) := by
      filter_upwards [ae_restrict_of_ae hu,ae_restrict_of_ae (conditionalCDF_cuadrasAuge δ u),
        ae_restrict_of_ae (Measure.ae_ne volume u),ae_restrict_mem measurableSet_Iic] with v huv hvu hne hv
      have hvu' : v<u := lt_of_le_of_ne hv hne
      rw [huv,hvu,cuadrasConditional,cuadrasConditional,
        ite_eq_right (not_lt.mpr hv),ite_eq_left hvu']
      calc
        _ = (1-(δ:ℝ))*((u:ℝ)^(-(δ:ℝ))*(u:ℝ)^(1-(δ:ℝ)))*(v:ℝ) := by ring
        _ = _ := by
          rw [← Real.rpow_add hup]
          congr 2
          congr 1
          ring
    rw [integral_congr_ae hprod,integral_const_mul,Copula.integral_unit_Iic (fun v : ℝ => v),integral_id]
    have hp : (u:ℝ)^(1-2*(δ:ℝ))*(u:ℝ)^2=(u:ℝ)^(3-2*(δ:ℝ)) := by
      rw [← Real.rpow_natCast,← Real.rpow_add hup]
      congr 1
      norm_num
      ring
    calc
      _ = (1-(δ:ℝ))*((u:ℝ)^(1-2*(δ:ℝ))*(u:ℝ)^2)/2 := by ring
      _ = _ := by rw [hp]
  change C.kendallTau=_
  rw [kendallTau_conditional_product,hCt,htriangle,he,integral_div,integral_const_mul,
    integral_unit_rpow_nonneg _ (show 0≤3-2*(δ:ℝ) by linarith [δ.property.2])]
  have h2 : 2-(δ:ℝ)≠0 := by linarith [δ.property.2]
  have h4 : 3-2*(δ:ℝ)+1≠0 := by linarith [δ.property.2]
  field_simp
  ring

end Verification
