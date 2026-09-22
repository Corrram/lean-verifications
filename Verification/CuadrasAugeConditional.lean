import Verification.CuadrasAugeRho
import Copula.Rank.ConditionalDerivative

/-! # An explicit conditional CDF for Cuadras–Augé -/

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def cuadrasConditional (δ u v : I) : ℝ :=
  if u<v then (v:ℝ)^(1-(δ:ℝ)) else (1-(δ:ℝ))*(u:ℝ)^(-(δ:ℝ))*(v:ℝ)

theorem conditionalCDF_cuadrasAuge (δ v : I) :
    (fun u => (cuadrasAuge δ).conditionalCDF u v) =ᵐ[volume]
      fun u => cuadrasConditional δ u v := by
  filter_upwards [(cuadrasAuge δ).conditionalCDF_eq_deriv v,Measure.ae_ne volume (0:I),
    Measure.ae_ne volume (1:I),Measure.ae_ne volume v] with u hu hu0 hu1 huv
  rw [hu]
  have h0 : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have h1 : (u:ℝ)<1 := lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h))
  rcases lt_or_gt_of_ne huv with huv | hvu
  · rw [cuadrasConditional,ite_eq_left huv]
    have he : Copula.cdfSection (cuadrasAuge δ) v =ᶠ[𝓝 (u:ℝ)]
        (fun x => x*(v:ℝ)^(1-(δ:ℝ))) := by
      filter_upwards [Ioo_mem_nhds h0 h1,eventually_lt_nhds (show (u:ℝ)<v from huv)] with x hx hxv
      have hh := cuadrasAuge_cdf_of_le δ (⟨x,hx.1.le,hx.2.le⟩:I) v hxv.le
      simpa only [Copula.cdfSection,projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩] using hh
    simpa using (((hasDerivAt_id (u:ℝ)).mul_const ((v:ℝ)^(1-(δ:ℝ)))).congr_of_eventuallyEq he).deriv
  · rw [cuadrasConditional,ite_eq_right (not_lt.mpr hvu.le)]
    have he : Copula.cdfSection (cuadrasAuge δ) v =ᶠ[𝓝 (u:ℝ)]
        (fun x => x^(1-(δ:ℝ))*(v:ℝ)) := by
      filter_upwards [Ioo_mem_nhds h0 h1,eventually_gt_nhds (show (v:ℝ)<u from hvu)] with x hx hxv
      have hh := cuadrasAuge_cdf_of_ge δ (⟨x,hx.1.le,hx.2.le⟩:I) v hxv.le
      simpa only [Copula.cdfSection,projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩] using hh
    have hd := ((hasDerivAt_id (u:ℝ)).rpow_const (p := 1-(δ:ℝ)) (Or.inl h0.ne')).mul_const (v:ℝ)
    simpa only [id_eq,one_mul,show 1-(δ:ℝ)-1= -(δ:ℝ) by ring] using (hd.congr_of_eventuallyEq he).deriv

theorem cuadrasConditional_measurable (δ : I) :
    Measurable (fun p : I × I => cuadrasConditional δ p.1 p.2) := by
  unfold cuadrasConditional
  exact ((measurable_subtype_coe.comp measurable_snd).pow_const _).ite
    (measurableSet_lt measurable_fst measurable_snd)
    ((measurable_const.mul ((measurable_subtype_coe.comp measurable_fst).pow_const _)).mul
      (measurable_subtype_coe.comp measurable_snd))

theorem cuadrasConditional_sq_joint_integrable (δ : I) :
    Integrable (fun p : I × I => cuadrasConditional δ p.2 p.1^2) := by
  have hc : Integrable (fun p : I × I => (cuadrasAuge δ).conditionalCDF p.2 p.1^2) := by
    refine (integrable_const (1:ℝ)).mono'
      ((cuadrasAuge δ).measurable_conditionalCDF.pow_const 2).aestronglyMeasurable ?_
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [(cuadrasAuge δ).conditionalCDF_nonneg p.2 p.1,(cuadrasAuge δ).conditionalCDF_le_one p.2 p.1]
  apply hc.congr
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    ((cuadrasAuge δ).measurable_conditionalCDF.pow_const 2)
    (((cuadrasConditional_measurable δ).comp measurable_swap).pow_const 2))).mpr
  exact Eventually.of_forall fun v => (conditionalCDF_cuadrasAuge δ v).fun_comp (fun z => z^2)

end Verification
