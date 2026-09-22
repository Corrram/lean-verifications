import Verification.MarshallOlkinOrder
import Verification.CubeFubini
import Copula.Rank.SpearmanCDF

/-! # Exact Spearman rho of the Cuadras–Augé family -/

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

theorem integral_unit_rpow_nonneg (p : ℝ) (hp : 0≤p) :
    (∫ u : I,(u:ℝ)^p)=1/(p+1) := by
  rw [Copula.integral_unitInterval (fun t : ℝ => t^p),integral_rpow (Or.inl (by linarith))]
  simp only [Real.one_rpow,Real.zero_rpow (show p+1≠0 by linarith),sub_zero]

theorem integral_unit_Iic_rpow_nonneg (p : ℝ) (hp : 0≤p) (v : I) :
    (∫ u in Iic v,(u:ℝ)^p)=(v:ℝ)^(p+1)/(p+1) := by
  rw [Copula.integral_unit_Iic (fun t : ℝ => t^p) v,integral_rpow (Or.inl (by linarith))]
  simp only [Real.zero_rpow (show p+1≠0 by linarith),sub_zero]

theorem cuadrasAuge_cdf_of_le (δ u v : I) (h : u≤v) :
    (cuadrasAuge δ).cdf ![u,v]=(u:ℝ)*(v:ℝ)^(1-(δ:ℝ)) := by
  by_cases hu : u=0
  · simp [hu]
  have hup : (0:ℝ)<u := lt_of_le_of_ne u.property.1 (Ne.symm (fun he => hu (Subtype.ext he)))
  have hvp : (0:ℝ)<v := hup.trans_le h
  rw [cuadrasAuge,cdf_marshallOlkin]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [min_eq_left (Real.rpow_le_rpow u.property.1 h δ.property.1),← mul_assoc,← Real.rpow_add hup]
  simp

theorem cuadrasAuge_cdf_of_ge (δ u v : I) (h : v≤u) :
    (cuadrasAuge δ).cdf ![u,v]=(u:ℝ)^(1-(δ:ℝ))*(v:ℝ) := by
  have he : (cuadrasAuge δ).cdf ![u,v]=(cuadrasAuge δ).cdf ![v,u] := by
    simp only [cuadrasAuge,marshallOlkin_cdf_min,mul_comm,min_comm]
  rw [he,cuadrasAuge_cdf_of_le δ v u h,mul_comm]

theorem integral_cuadrasAuge_section (δ v : I) :
    (∫ u : I,(cuadrasAuge δ).cdf ![u,v]) =
      (v:ℝ)^(3-(δ:ℝ))/2+(v:ℝ)/(2-(δ:ℝ))-(v:ℝ)^(3-(δ:ℝ))/(2-(δ:ℝ)) := by
  let p := 1-(δ:ℝ)
  have hp : 0≤p := by dsimp [p]; linarith [δ.property.2]
  have hc : Continuous (fun u : I => (u:ℝ)^p) :=
    (Real.continuous_rpow_const hp).comp continuous_subtype_val
  have hi := Copula.integrable_continuous_unit volume hc
  have hiC : Integrable (fun u : I => (cuadrasAuge δ).cdf ![u,v]) :=
    Copula.integrable_continuous_unit volume ((cuadrasAuge δ).continuous_cdf.comp (by fun_prop))
  have hsplit := integral_add_compl (s := Iic v) measurableSet_Iic hiC
  rw [compl_Iic] at hsplit
  have hleft : (∫ u in Iic v,(cuadrasAuge δ).cdf ![u,v])=(v:ℝ)^p*((v:ℝ)^2/2) := by
    rw [setIntegral_congr_fun measurableSet_Iic (fun u hu => cuadrasAuge_cdf_of_le δ u v hu),integral_mul_const,
      Copula.integral_unit_Iic (fun u : ℝ => u),integral_id]
    ring
  have hright : (∫ u in Ioi v,(cuadrasAuge δ).cdf ![u,v])=
      (v:ℝ)*(1/(p+1)-(v:ℝ)^(p+1)/(p+1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => cuadrasAuge_cdf_of_ge δ u v (le_of_lt hu)),integral_mul_const]
    have he := integral_add_compl (s := Iic v) measurableSet_Iic hi
    rw [compl_Iic] at he
    rw [integral_unit_Iic_rpow_nonneg p hp v,integral_unit_rpow_nonneg p hp] at he
    change (∫ u in Ioi v,(u:ℝ)^p)*(v:ℝ)=_
    have he' : (∫ u in Ioi v,(u:ℝ)^p)=1/(p+1)-(v:ℝ)^(p+1)/(p+1) := by linarith only [he]
    rw [he']
    ring
  have hpow : (v:ℝ)^p*(v:ℝ)^2=(v:ℝ)^(3-(δ:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_add_of_nonneg v.property.1 hp (by norm_num)]
    congr 1
    dsimp [p]
    ring
  have hpow' : (v:ℝ)*(v:ℝ)^(p+1)=(v:ℝ)^(3-(δ:ℝ)) := by
    calc
      _ = (v:ℝ)^(1:ℝ)*(v:ℝ)^(p+1) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add_of_nonneg v.property.1 (by norm_num : (0:ℝ)≤1) (by linarith : 0≤p+1)]
        congr 1
        dsimp [p]
        ring
  rw [hleft,hright] at hsplit
  have hd : p+1=2-(δ:ℝ) := by dsimp [p]; ring
  calc
    _ = (v:ℝ)^p*((v:ℝ)^2/2)+(v:ℝ)*(1/(p+1)-(v:ℝ)^(p+1)/(p+1)) := hsplit.symm
    _ = ((v:ℝ)^p*(v:ℝ)^2)/2+(v:ℝ)/(p+1)-((v:ℝ)*(v:ℝ)^(p+1))/(p+1) := by ring
    _ = _ := by rw [hpow,hpow',hd]

theorem integral_cuadrasAuge_cdf (δ : I) :
    (∫ x : Fin 2 → I,(cuadrasAuge δ).cdf x)=1/(4-(δ:ℝ)) := by
  have hi := (cuadrasAuge δ).integrable_cdf volume
  have he := integral_cube_Iic_iterated hi 1 1
  have htop : Iic (![(1:I),1])=Set.univ := by
    ext x
    simp only [mem_Iic,mem_univ,iff_true,Pi.le_def,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    exact ⟨(x 0).property.2,(x 1).property.2⟩
  simp only [htop,Measure.restrict_univ,show Iic (1:I)=Set.univ from Set.Iic_top] at he
  rw [he]
  have hs (u : I) : (∫ v : I,(cuadrasAuge δ).cdf ![u,v]) =
      (∫ v : I,(cuadrasAuge δ).cdf ![v,u]) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      simp only [cuadrasAuge,marshallOlkin_cdf_min,mul_comm,min_comm]
  simp_rw [hs,integral_cuadrasAuge_section]
  have hp : 0≤3-(δ:ℝ) := by linarith [δ.property.2]
  have hpow : Integrable (fun u : I => (u:ℝ)^(3-(δ:ℝ))) := Copula.integrable_continuous_unit volume ((Real.continuous_rpow_const hp).comp continuous_subtype_val)
  have hid := Copula.integrable_continuous_unit volume (f := fun u : I => (u:ℝ)) continuous_subtype_val
  rw [integral_sub (f := fun u : I => (u:ℝ)^(3-(δ:ℝ))/2+(u:ℝ)/(2-(δ:ℝ))) (g := fun u : I => (u:ℝ)^(3-(δ:ℝ))/(2-(δ:ℝ))) ((hpow.div_const 2).add (hid.div_const _)) (hpow.div_const _),
    integral_add (f := fun u : I => (u:ℝ)^(3-(δ:ℝ))/2) (g := fun u : I => (u:ℝ)/(2-(δ:ℝ))) (hpow.div_const 2) (hid.div_const _),integral_div,integral_div,integral_div,
    integral_unit_rpow_nonneg _ hp,Copula.integral_unit_id]
  have h2 : 2-(δ:ℝ)≠0 := by linarith [δ.property.2]
  have h4 : 3-(δ:ℝ)+1≠0 := by linarith [δ.property.2]
  have h4' : 4-(δ:ℝ)≠0 := by linarith [δ.property.2]
  field_simp
  ring

theorem cuadrasAuge_spearmanRho (δ : I) :
    (cuadrasAuge δ).spearmanRho=3*(δ:ℝ)/(4-(δ:ℝ)) := by
  rw [Copula.spearmanRho_eq_integral_cdf,Copula.toMeasure_independence]
  change 12*(∫ x : Fin 2 → I,(cuadrasAuge δ).cdf x)-3=_
  rw [integral_cuadrasAuge_cdf]
  have hd : 4-(δ:ℝ)≠0 := by linarith [δ.property.2]
  field_simp
  ring

end Verification
