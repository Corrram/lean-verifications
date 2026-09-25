import Verification.ClaytonTau
import Verification.EulerHypergeometric

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem claytonPartial_regular {θ u v : ℝ} (hθ : 0<θ) (hu : 0<u) (hv : v∈Ioc 0 1) :
    claytonPartial θ u v=(1-(1-v^(-θ))*u^θ)^(-1/θ-1) := by
  let B := 1-(1-v^(-θ))*u^θ
  have hv' : 1≤v^(-θ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv.1 hv.2 (by linarith)
  have hB : 0<B := by
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv') (Real.rpow_nonneg hu.le θ)
    dsimp [B]
    linarith
  have hm : u^(-θ)*u^θ=1 := by rw [← Real.rpow_add hu]; simp
  have he : u^(-θ)+v^(-θ)-1=u^(-θ)*B := by
    dsimp [B]
    linear_combination (1-v^(-θ))*hm
  unfold claytonPartial
  rw [he,Real.mul_rpow (Real.rpow_nonneg hu.le _) hB.le,← Real.rpow_mul hu.le]
  rw [← mul_assoc,← Real.rpow_add hu]
  have hp : -θ-1+(-θ)*(-1/θ-1)=0 := by field_simp; ring
  rw [hp,Real.rpow_zero,one_mul]

theorem claytonPartial_sq_regular {θ u v : ℝ} (hθ : 0<θ) (hu : 0<u) (hv : v∈Ioc 0 1) :
    (claytonPartial θ u v)^2=(1-(1-v^(-θ))*u^θ)^(-2-2/θ) := by
  rw [claytonPartial_regular hθ hu hv,pow_two]
  have hv' : 1≤v^(-θ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv.1 hv.2 (by linarith)
  have hB : 0<1-(1-v^(-θ))*u^θ := by
    have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv') (Real.rpow_nonneg hu.le θ)
    linarith
  rw [← Real.rpow_add hB]
  congr 1
  ring

theorem clayton_xi_regular_integral {θ : ℝ} (hθ : 0<θ) :
    (clayton 2 θ hθ).chatterjeeXi=
      6*(∫ v : I, ∫ u : I, (1-(1-(v:ℝ)^(-θ))*(u:ℝ)^θ)^(-2-2/θ))-2 := by
  unfold Copula.chatterjeeXi
  congr 2
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with v hv0
  have hv : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv0 (Subtype.ext h)))
  apply integral_congr_ae
  filter_upwards [clayton_conditionalCDF hθ v hv,Measure.ae_ne (volume : Measure I) 0] with u hu hu0
  have hup : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu0 (Subtype.ext h)))
  rw [hu,claytonPartial_sq_regular hθ hup ⟨hv,v.property.2⟩]

theorem clayton_chatterjeeXi {θ : ℝ} (hθ : 0<θ) :
    (clayton 2 θ hθ).chatterjeeXi =
      6*(∫ v : I, eulerHypergeometric (1/θ) (2+2/θ) (1/θ+1)
        (1-(v:ℝ)^(-θ)))-2 := by
  rw [clayton_xi_regular_integral hθ]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with v
  rw [eulerHypergeometric_successor (one_div_pos.mpr hθ)]
  have hh := integral_unit_rpow_substitution hθ
    (fun t => (1-(1-(v:ℝ)^(-θ))*t)^(-2-2/θ))
  convert hh using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  ring_nf

end Verification
