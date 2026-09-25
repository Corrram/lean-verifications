import Verification.GaussianQuantileConditional
import Copula.Dependence.ConditionalMonotonicity
import Copula.Order.StrictSpearman

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem antitone_unit_extension {f : I → ℝ} (hf : ∀ u, f u∈Icc (0:ℝ) 1)
    (ha : AntitoneOn f {u : I | (u:ℝ)∈Ioo (0:ℝ) 1}) :
    Antitone (fun u : I => if u=0 then (1:ℝ) else if u=1 then 0 else f u) := by
  intro a b hab
  by_cases ha0 : a=0
  · simp only [ha0,ite_true]
    split_ifs <;> first | exact (hf b).2 | norm_num
  by_cases hb1 : b=1
  · simp only [hb1,ite_true,ite_false,one_ne_zero,ha0]
    split_ifs <;> first | exact (hf a).1 | norm_num
  have hb0 : b≠0 := by
    intro h
    apply ha0
    exact le_antisymm (h ▸ hab) (unitInterval.nonneg a)
  have ha1 : a≠1 := by
    intro h
    apply hb1
    exact le_antisymm (unitInterval.le_one b) (h ▸ hab)
  simp only [ha0,ha1,hb0,hb1,ite_false]
  exact ha ⟨unitInterval.pos_iff_ne_zero.mpr ha0,unitInterval.lt_one_iff_ne_one.mpr ha1⟩
    ⟨unitInterval.pos_iff_ne_zero.mpr hb0,unitInterval.lt_one_iff_ne_one.mpr hb1⟩ hab

theorem gaussianBivariate_isSI {r : ℝ} (hr : r∈Icc (-1) 1) (hpos : 0≤r) :
    (gaussianBivariate r hr).IsSI := by
  by_cases hone : r=1
  · subst r
    rw [gaussianBivariate_one]
    exact isCI_comonotonic.1
  have hi : r∈Ioo (-1) 1 := ⟨by linarith,lt_of_le_of_ne hr.2 hone⟩
  let C := gaussianBivariate r hr
  intro a b c v hab hbc
  change ((b:ℝ)-(a:ℝ))*C.cdf ![c,v]+((c:ℝ)-(b:ℝ))*C.cdf ![a,v]≤
    ((c:ℝ)-(a:ℝ))*C.cdf ![b,v]
  by_cases hv0 : v=0
  · subst v
    have hz (u : I) : C.cdf ![u,0]=0 := C.cdf_eq_zero_of_coord_eq_zero _ 1 rfl
    simp only [hz,mul_zero,add_zero,le_refl]
  by_cases hv1 : v=1
  · subst v
    simp only [cdf_two_one_right]
    nlinarith
  have hv : (v:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨unitInterval.pos_iff_ne_zero.mpr hv0,unitInterval.lt_one_iff_ne_one.mpr hv1⟩
  let f := fun u : I => if u=0 then (1:ℝ) else if u=1 then 0 else gaussianQuantileConditional r v u
  have hbnd (u : I) : gaussianQuantileConditional r v u∈Icc (0:ℝ) 1 :=
    ⟨ProbabilityTheory.cdf_nonneg _ _,ProbabilityTheory.cdf_le_one _ _⟩
  have ha : Antitone f := antitone_unit_extension hbnd (gaussianQuantileConditional_antitoneOn hpos v)
  have he : (fun u => C.conditionalCDF u v)=ᵐ[volume] f := by
    filter_upwards [gaussianBivariate_conditionalCDF_quantile hi hv,
      Measure.ae_ne (volume : Measure I) 0,Measure.ae_ne (volume : Measure I) 1] with u hu hu0 hu1
    simpa only [f,hu0,hu1,ite_false] using hu
  have hf : Integrable f := (C.integrable_conditionalCDF v).congr he
  have hF (u : I) : C.cdf ![u,v]=∫ t in Iic u, f t := by
    rw [C.cdf_eq_integral_conditionalCDF]
    exact integral_congr_ae (ae_restrict_of_ae he)
  simp_rw [hF]
  exact integral_Iic_concave_of_antitone hf ha a b c hab hbc

theorem gaussianBivariate_isCI {r : ℝ} (hr : r∈Icc (-1) 1) (hpos : 0≤r) :
    (gaussianBivariate r hr).IsCI := by
  have h := gaussianBivariate_isSI hr hpos
  exact ⟨h,by rwa [gaussianBivariate_transpose]⟩

theorem gaussianBivariate_isSD {r : ℝ} (hr : r∈Icc (-1) 1) (hneg : r≤0) :
    (gaussianBivariate r hr).IsSD := by
  have hn : -r∈Icc (-1) 1 := by constructor <;> linarith [hr.1,hr.2]
  have h := (isSD_reflect_second_iff (gaussianBivariate (-r) hn)).mpr
    (gaussianBivariate_isSI hn (by linarith))
  have he := gaussianBivariate_neg hn
  simp only [neg_neg] at he
  rwa [← he] at h

theorem gaussianBivariate_isCD {r : ℝ} (hr : r∈Icc (-1) 1) (hneg : r≤0) :
    (gaussianBivariate r hr).IsCD := by
  have h := gaussianBivariate_isSD hr hneg
  exact ⟨h,by rwa [gaussianBivariate_transpose]⟩

theorem gaussianBivariate_isPQD_iff {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).IsPQD ↔ 0≤r := by
  constructor
  · intro h
    have hh := h.spearmanRho_nonneg
    rw [gaussianBivariate_spearmanRho hr] at hh
    have hp : 0<(6:ℝ)/Real.pi := div_pos (by norm_num) Real.pi_pos
    have ha : 0≤Real.arcsin (r/2) := by nlinarith
    have := Real.arcsin_nonneg.mp ha
    linarith
  · intro h
    exact (gaussianBivariate_isCI hr h).isPQD

theorem gaussianBivariate_isNQD_iff {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).IsNQD ↔ r≤0 := by
  constructor
  · intro h
    have hh := h.spearmanRho_nonpos
    rw [gaussianBivariate_spearmanRho hr] at hh
    have hp : 0<(6:ℝ)/Real.pi := div_pos (by norm_num) Real.pi_pos
    have ha : Real.arcsin (r/2)≤0 := by nlinarith
    have := Real.arcsin_nonpos.mp ha
    linarith
  · intro h
    exact (gaussianBivariate_isCD hr h).isNQD

theorem gaussianBivariate_isCI_iff {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).IsCI ↔ 0≤r :=
  ⟨fun h => (gaussianBivariate_isPQD_iff hr).mp h.isPQD,gaussianBivariate_isCI hr⟩

theorem gaussianBivariate_isCD_iff {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).IsCD ↔ r≤0 :=
  ⟨fun h => (gaussianBivariate_isNQD_iff hr).mp h.isNQD,gaussianBivariate_isCD hr⟩

end Verification
