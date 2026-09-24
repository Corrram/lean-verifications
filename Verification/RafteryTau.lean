import Verification.RafteryDensity
import Verification.CuadrasAugeRho
import Verification.SymmetricTriangleIntegral

/-! # Kendall tau of the corrected Raftery family

The identified copula density turns Kendall's integral into a Lebesgue integral.
Symmetry reduces it to one triangle, where exact power integration gives the
Table 6 formula on the full parameter interval, including both endpoints.
-/

open MeasureTheory ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

theorem integral_raftery_cdf_density_triangle {a : ℝ} (ha : 1<a) (v : I)
    (hv : 0<(v:ℝ)) :
    (∫ u in Iic v, (rafteryPower a ha).cdf ![u,v]*rafteryDensity a u v) =
      (a*(a-1)/((2*a-1)*(a+1))-(a-1)/(2*(2*a-1)^2))*(v:ℝ) +
      (a^2/((2*a-1)*(a+1))-1/(2*(2*a-1)^2))*(v:ℝ)^(2*a) +
      a/(2*(2*a-1)^2)*(v:ℝ)^(4*a-1) := by
  have he : (fun u : I => (rafteryPower a ha).cdf ![u,v]*rafteryDensity a u v)
      =ᵐ[volume.restrict (Iic v)] fun u =>
      (a/(2*a-1)*(a*(v:ℝ)^(a-1)+(a-1)*(v:ℝ)^(-a))) *
      ((u:ℝ)^a+((v:ℝ)^a-(v:ℝ)^(1-a))/(2*a-1)*(u:ℝ)^(2*a-1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Iic,
      ae_restrict_of_ae (Measure.ae_ne (volume : Measure I) 0)] with u huv hu
    have hup : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
    rw [rafteryPower_cdf_min,rafteryDensity,min_eq_left huv,max_eq_right huv]
    have hA : (u:ℝ)*(u:ℝ)^(a-1)=(u:ℝ)^a := by
      calc
        _ = (u:ℝ)^1*(u:ℝ)^(a-1) := by rw [Real.rpow_one]
        _ = (u:ℝ)^(1+(a-1)) := (Real.rpow_add hup _ _).symm
        _ = _ := by congr 1; ring
    have hB : (u:ℝ)^a*(u:ℝ)^(a-1)=(u:ℝ)^(2*a-1) := by
      rw [← Real.rpow_add hup]
      congr 1
      ring
    calc
      _ = (a/(2*a-1)*(a*(v:ℝ)^(a-1)+(a-1)*(v:ℝ)^(-a))) *
          ((u:ℝ)*(u:ℝ)^(a-1)+((v:ℝ)^a-(v:ℝ)^(1-a))/(2*a-1)*
            ((u:ℝ)^a*(u:ℝ)^(a-1))) := by ring
      _ = _ := by rw [hA,hB]
  have hi (p : ℝ) (hp : 0≤p) : Integrable (fun u : I => (u:ℝ)^p) :=
    Copula.integrable_continuous_unit volume (continuous_subtype_val.rpow_const (fun _ => Or.inr hp))
  rw [integral_congr_ae he,integral_const_mul,
    integral_add (hi a (by linarith)).integrableOn
      (((hi (2*a-1) (by linarith)).const_mul _).integrableOn),integral_const_mul,
    integral_unit_Iic_rpow_nonneg a (by linarith),
    integral_unit_Iic_rpow_nonneg (2*a-1) (by linarith)]
  have hvA : (v:ℝ)^a≠0 := (Real.rpow_pos_of_pos hv a).ne'
  have h2 : (v:ℝ)^(2*a)=((v:ℝ)^a)^2 := by
    rw [show 2*a=a+a by ring,Real.rpow_add hv,pow_two]
  have h4 : (v:ℝ)^(4*a)=((v:ℝ)^a)^4 := by
    rw [show 4*a=2*a+2*a by ring,Real.rpow_add hv,h2]
    ring
  rw [show 2*a-1+1=2*a by ring,Real.rpow_sub hv a 1,Real.rpow_one,
    Real.rpow_neg hv.le,Real.rpow_sub hv 1 a,Real.rpow_one,
    Real.rpow_add hv a 1,Real.rpow_one,Real.rpow_sub hv (4*a) 1,Real.rpow_one,h4,h2]
  field_simp [hv.ne',hvA,show 2*a-1≠0 by linarith,show a*2-1≠0 by linarith,
    show -1+a*2≠0 by linarith,show a+1≠0 by linarith,
    show a≠0 by linarith]
  ring

theorem rafteryPower_kendallTau {a : ℝ} (ha : 1<a) :
    (rafteryPower a ha).kendallTau=2*(a-1)/(2*a+1) := by
  let C := rafteryPower a ha
  let D : (Fin 2 → I) → ℝ := fun x => rafteryDensity a (x 0) (x 1)
  have hm : Measurable D := by unfold D rafteryDensity; fun_prop
  have hn (x : Fin 2 → I) : 0≤D x := rafteryDensity_nonneg ha.le _ _
  have hmeasure : C.toMeasure=volume.withDensity (fun x => ENNReal.ofReal (D x)) :=
    rafteryPower_toMeasure_density ha
  have hi := C.integrable_cdf C.toMeasure
  rw [hmeasure,integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal (by simp)] at hi
  simp only [ENNReal.toReal_ofReal (hn _),smul_eq_mul] at hi
  have hi' : Integrable (fun x => C.cdf x*D x) := by simpa only [mul_comm] using hi
  let f : I × I → ℝ := fun p => C.cdf ![p.1,p.2]*D ![p.1,p.2]
  have hp := (volume_preserving_finTwoArrow I).symm MeasurableEquiv.finTwoArrow
  have hfi : Integrable f := hp.integrable_comp_of_integrable hi'
  have hs (p : I × I) : f p.swap=f p := by
    change C.cdf ![p.2,p.1]*rafteryDensity a p.2 p.1 =
      C.cdf ![p.1,p.2]*rafteryDensity a p.1 p.2
    simp only [C,rafteryPower_cdf_min,rafteryDensity,min_comm,max_comm]
  have he : (∫ x, C.cdf x*D x)=(∫ u : I,∫ v : I,f (u,v)) := by
    have hh := hp.integral_comp' (fun x => C.cdf x*D x)
    change (∫ p : I × I,f p)=(∫ x, C.cdf x*D x) at hh
    rw [← hh,Measure.volume_eq_prod,integral_prod _ hfi]
  have hinner : (∫ u : I,∫ v in Iic u,f (u,v)) =
      ∫ v : I, (a*(a-1)/((2*a-1)*(a+1))-(a-1)/(2*(2*a-1)^2))*(v:ℝ) +
        (a^2/((2*a-1)*(a+1))-1/(2*(2*a-1)^2))*(v:ℝ)^(2*a) +
        a/(2*(2*a-1)^2)*(v:ℝ)^(4*a-1) := by
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne (volume : Measure I) 0] with v hv
    have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
    have hsym (u : I) : f (v,u)=C.cdf ![u,v]*rafteryDensity a u v := hs (u,v)
    simp_rw [hsym]
    exact integral_raftery_cdf_density_triangle ha v hvp
  have hip (p : ℝ) (h : 0≤p) : Integrable (fun v : I => (v:ℝ)^p) :=
    Copula.integrable_continuous_unit volume (continuous_subtype_val.rpow_const (fun _ => Or.inr h))
  have hid : Integrable (fun v : I => (v:ℝ)) :=
    Copula.integrable_continuous_unit volume continuous_subtype_val
  have hiAB : Integrable (fun v : I =>
      (a*(a-1)/((2*a-1)*(a+1))-(a-1)/(2*(2*a-1)^2))*(v:ℝ) +
      (a^2/((2*a-1)*(a+1))-1/(2*(2*a-1)^2))*(v:ℝ)^(2*a)) :=
    (hid.const_mul _).add ((hip (2*a) (by linarith)).const_mul _)
  change C.kendallTau=_
  rw [kendallTau,hmeasure,integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (hn _),smul_eq_mul]
  simp_rw [mul_comm (D _) (C.cdf _)]
  rw [he,integral_symmetric_triangle_of_integrable f hfi hs,hinner,
    integral_add hiAB
      ((hip (4*a-1) (by linarith)).const_mul _),
    integral_add (hid.const_mul _) ((hip (2*a) (by linarith)).const_mul _)]
  simp only [integral_const_mul,Copula.integral_unit_id,
    integral_unit_rpow_nonneg (2*a) (by linarith),
    integral_unit_rpow_nonneg (4*a-1) (by linarith)]
  field_simp [show 2*a-1≠0 by linarith,show a*2-1≠0 by linarith,
    show a+1≠0 by linarith,show 2*a+1≠0 by linarith,
    show a*2+1≠0 by linarith,show 4*a-1+1≠0 by linarith,show a≠0 by linarith]
  ring

theorem raftery_kendallTau (δ : I) :
    (raftery δ).kendallTau=2*(δ:ℝ)/(3-(δ:ℝ)) := by
  by_cases h0 : δ=0
  · subst δ; rw [raftery_zero]; norm_num
  by_cases h1 : δ=1
  · subst δ; rw [raftery_one]; norm_num
  simp only [raftery,h0,h1,dite_false]
  rw [rafteryPower_kendallTau]
  have hd : 1-(δ:ℝ)≠0 := sub_ne_zero.mpr (fun h => h1 (Subtype.ext h.symm))
  have hp : 3-(δ:ℝ)≠0 := by linarith [δ.property.2]
  have he : 2*(1/(1-(δ:ℝ)))+1=(3-(δ:ℝ))/(1-(δ:ℝ)) := by field_simp; ring
  rw [he]
  field_simp [hd,hp]
  ring

end Verification
