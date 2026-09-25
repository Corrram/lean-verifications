import Verification.GaussianQuantileConditional
import Verification.GaussianDependence
import Copula.Order.Rank
import Verification.GaussianTau
import Verification.SchurOrthantEquivalence
import Copula.Order.SymmetricSchur

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem integral_Iic_le_of_affine_single_crossing {μ : Measure ℝ} {H : ℝ → ℝ}
    (hH : Monotone H) {p q r s : ℝ} (hqs : q≤s)
    (hf : Integrable (fun x => H (p-q*x)) μ)
    (hg : Integrable (fun x => H (r-s*x)) μ)
    (he : (∫ x, H (p-q*x) ∂μ)=∫ x, H (r-s*x) ∂μ) (a : ℝ) :
    (∫ x in Iic a, H (p-q*x) ∂μ) ≤ ∫ x in Iic a, H (r-s*x) ∂μ := by
  by_cases ha : p-q*a≤r-s*a
  · apply setIntegral_mono_on hf.integrableOn hg.integrableOn measurableSet_Iic
    intro x hx
    apply hH
    nlinarith [mul_nonneg (sub_nonneg.mpr hqs) (sub_nonneg.mpr hx)]
  · have hc : (∫ x in (Iic a)ᶜ, H (r-s*x) ∂μ) ≤ ∫ x in (Iic a)ᶜ, H (p-q*x) ∂μ := by
      apply setIntegral_mono_on hg.integrableOn hf.integrableOn measurableSet_Iic.compl
      intro x hx
      have hax : a≤x := le_of_lt (by simpa using hx)
      apply hH
      nlinarith [mul_nonneg (sub_nonneg.mpr hqs) (sub_nonneg.mpr hax)]
    have h1 := integral_add_compl (measurableSet_Iic (a := a)) hf
    have h2 := integral_add_compl (measurableSet_Iic (a := a)) hg
    linarith

theorem gaussian_standardized_slope_monotone {r s : ℝ}
    (hr : r∈Ioo (-1) 1) (hs : s∈Ioo (-1) 1) (hrs : r≤s) :
    r/Real.sqrt (1-r^2) ≤ s/Real.sqrt (1-s^2) := by
  have hR : 0<Real.sqrt (1-r^2) := Real.sqrt_pos.mpr (by nlinarith [hr.1,hr.2])
  have hS : 0<Real.sqrt (1-s^2) := Real.sqrt_pos.mpr (by nlinarith [hs.1,hs.2])
  have hR2 := Real.sq_sqrt (le_of_lt (show 0<1-r^2 by nlinarith [hr.1,hr.2]))
  have hS2 := Real.sq_sqrt (le_of_lt (show 0<1-s^2 by nlinarith [hs.1,hs.2]))
  apply (div_le_div_iff₀ hR hS).mpr
  have he : (s*Real.sqrt (1-r^2))^2-(r*Real.sqrt (1-s^2))^2=s^2-r^2 := by
    rw [mul_pow,mul_pow,hR2,hS2]
    ring
  by_cases h0 : 0≤r
  · have hsr : r^2≤s^2 := by nlinarith
    have h1 := mul_nonneg h0 hS.le
    have h2 := mul_nonneg (h0.trans hrs) hR.le
    nlinarith [sq_nonneg (s*Real.sqrt (1-r^2)-r*Real.sqrt (1-s^2))]
  by_cases h1 : 0≤s
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h0) hS.le).trans
      (mul_nonneg h1 hR.le)
  have hsr : s^2≤r^2 := by nlinarith
  have h2 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h0) hS.le
  have h3 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h1) hR.le
  nlinarith [sq_nonneg (s*Real.sqrt (1-r^2)-r*Real.sqrt (1-s^2))]

theorem gaussianConditional_normal_integral {r : ℝ} (hr : r∈Ioo (-1) 1) (b : ℝ) :
    (∫ x, ProbabilityTheory.cdf (gaussianReal 0 1) ((b-r*x)/Real.sqrt (1-r^2))
      ∂gaussianReal 0 1)=ProbabilityTheory.cdf (gaussianReal 0 1) b := by
  let C := gaussianBivariate r ⟨hr.1.le,hr.2.le⟩
  rw [← integral_congr_ae (gaussianBivariate_conditionalCDF_normal hr b)]
  rw [← integral_standardNormal_transform
    ((C.measurable_conditionalCDF_left _).aestronglyMeasurable),C.integral_conditionalCDF]
  rfl

theorem gaussianBivariate_cdf_normal_monotone {r s : ℝ}
    (hr : r∈Ioo (-1) 1) (hs : s∈Ioo (-1) 1) (hrs : r≤s) (a b : ℝ) :
    (gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).cdf
      ![cdfUnit (gaussianReal 0 1) a,cdfUnit (gaussianReal 0 1) b] ≤
    (gaussianBivariate s ⟨hs.1.le,hs.2.le⟩).cdf
      ![cdfUnit (gaussianReal 0 1) a,cdfUnit (gaussianReal 0 1) b] := by
  let μ := gaussianReal 0 1
  have hi (t : ℝ) : Integrable (fun x : ℝ => ProbabilityTheory.cdf μ
      (b/Real.sqrt (1-t^2)-(t/Real.sqrt (1-t^2))*x)) μ := by
    apply Integrable.of_bound
      (((monotone_cdf μ).measurable.comp (by fun_prop)).aestronglyMeasurable) 1
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Function.comp_def]
      rw [Real.norm_eq_abs,abs_of_nonneg (cdf_nonneg μ _)]
      exact cdf_le_one μ _
  have he (t x : ℝ) : b/Real.sqrt (1-t^2)-(t/Real.sqrt (1-t^2))*x=
      (b-t*x)/Real.sqrt (1-t^2) := by ring
  have hh := integral_Iic_le_of_affine_single_crossing (monotone_cdf μ)
    (gaussian_standardized_slope_monotone hr hs hrs) (hi r) (hi s)
    (by
      simp_rw [he]
      exact (gaussianConditional_normal_integral hr b).trans
        (gaussianConditional_normal_integral hs b).symm) a
  simp_rw [he] at hh
  rw [gaussianBivariate_cdf_normal hr,gaussianBivariate_cdf_normal hs]
  exact hh

theorem gaussianBivariate_lowerOrthant_monotone {r s : ℝ}
    (hr : r∈Icc (-1) 1) (hs : s∈Icc (-1) 1) (hrs : r≤s) :
    (gaussianBivariate r hr).LowerOrthantLE (gaussianBivariate s hs) := by
  by_cases hrn : r=-1
  · subst r
    rw [gaussianBivariate_negative_one]
    exact lowerOrthantLE_countermonotonic _
  by_cases hs1 : s=1
  · subst s
    rw [gaussianBivariate_one]
    exact lowerOrthantLE_comonotonic _
  have hri : r∈Ioo (-1) 1 := ⟨lt_of_le_of_ne hr.1 (Ne.symm hrn),
    hrs.trans_lt (lt_of_le_of_ne hs.2 hs1)⟩
  have hsi : s∈Ioo (-1) 1 := ⟨hri.1.trans_le hrs,lt_of_le_of_ne hs.2 hs1⟩
  intro z
  have hz : z=![z 0,z 1] := by ext i; fin_cases i <;> rfl
  rw [hz]
  by_cases h0 : z 0=0
  · simp only [h0,cdf_two_zero_left,le_refl]
  by_cases h1 : z 1=0
  · rw [(gaussianBivariate r hr).cdf_eq_zero_of_coord_eq_zero _ 1 (by simpa using h1),
      (gaussianBivariate s hs).cdf_eq_zero_of_coord_eq_zero _ 1 (by simpa using h1)]
  by_cases h2 : z 0=1
  · simp only [h2,cdf_two_one_left,le_refl]
  by_cases h3 : z 1=1
  · simp only [h3,cdf_two_one_right,le_refl]
  have hu : (z 0:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨unitInterval.pos_iff_ne_zero.mpr h0,unitInterval.lt_one_iff_ne_one.mpr h2⟩
  have hv : (z 1:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨unitInterval.pos_iff_ne_zero.mpr h1,unitInterval.lt_one_iff_ne_one.mpr h3⟩
  have he0 : cdfUnit (gaussianReal 0 1) (normalQuantile (z 0))=z 0 := Subtype.ext (cdf_normalQuantile hu)
  have he1 : cdfUnit (gaussianReal 0 1) (normalQuantile (z 1))=z 1 := Subtype.ext (cdf_normalQuantile hv)
  have h := gaussianBivariate_cdf_normal_monotone hri hsi hrs (normalQuantile (z 0)) (normalQuantile (z 1))
  rw [he0,he1] at h
  exact h

theorem gaussianBivariate_lowerOrthant_iff {r s : ℝ}
    (hr : r∈Icc (-1) 1) (hs : s∈Icc (-1) 1) :
    (gaussianBivariate r hr).LowerOrthantLE (gaussianBivariate s hs) ↔ r≤s := by
  refine ⟨?_,gaussianBivariate_lowerOrthant_monotone hr hs⟩
  intro h
  have ht := h.kendallTau_le
  rw [gaussianBivariate_kendallTau hr,gaussianBivariate_kendallTau hs] at ht
  exact (Real.strictMonoOn_arcsin.le_iff_le hr hs).mp
    ((mul_le_mul_iff_right₀ (div_pos (by norm_num) Real.pi_pos)).mp ht)

theorem gaussianBivariate_schur_neg {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])).SchurLE (gaussianBivariate r hr) ∧
    (gaussianBivariate r hr).SchurLE (gaussianBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])) := by
  have hn : -r∈Icc (-1) 1 := by constructor <;> linarith [hr.1,hr.2]
  have hf : (gaussianBivariate r hr).reflect {0}=gaussianBivariate (-r) hn := by
    have h := transpose_reflect_first (gaussianBivariate r hr)
    rw [gaussianBivariate_transpose hr,← gaussianBivariate_neg hr] at h
    have he := congrArg Copula.transpose h
    simpa only [transpose_transpose,gaussianBivariate_transpose hn] using he
  rw [← hf]
  exact Copula.schurLE_of_rearrangement _ _ unitInterval.measurePreserving_symm
    (conditionalCDF_reflect_first _)

theorem gaussianBivariate_schur_abs {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate |r| ⟨by linarith [abs_nonneg r],abs_le.mpr hr⟩).SchurLE (gaussianBivariate r hr) ∧
    (gaussianBivariate r hr).SchurLE (gaussianBivariate |r| ⟨by linarith [abs_nonneg r],abs_le.mpr hr⟩) := by
  by_cases h : 0≤r
  · simp only [abs_of_nonneg h]
    exact ⟨SchurLE.refl _,SchurLE.refl _⟩
  simpa only [abs_of_neg (lt_of_not_ge h)] using gaussianBivariate_schur_neg hr

theorem gaussianBivariate_schur_iff {r s : ℝ}
    (hr : r∈Icc (-1) 1) (hs : s∈Icc (-1) 1) :
    (gaussianBivariate r hr).SchurLE (gaussianBivariate s hs) ↔ |r|≤|s| := by
  have har : |r|∈Icc (-1) 1 := ⟨by linarith [abs_nonneg r],abs_le.mpr hr⟩
  have has : |s|∈Icc (-1) 1 := ⟨by linarith [abs_nonneg s],abs_le.mpr hs⟩
  have ha := gaussianBivariate_schur_abs hr
  have hb := gaussianBivariate_schur_abs hs
  have he := (schurLE_iff_lowerOrthantLE_isSI _ _
    ((gaussianBivariate_isCI_iff har).mpr (abs_nonneg r)).1
    ((gaussianBivariate_isCI_iff has).mpr (abs_nonneg s)).1).trans
      (gaussianBivariate_lowerOrthant_iff har has)
  exact ⟨fun h => he.mp (ha.1.trans (h.trans hb.2)),
    fun h => ha.2.trans ((he.mpr h).trans hb.1)⟩

theorem gaussianBivariate_schurBoth_iff {r s : ℝ}
    (hr : r∈Icc (-1) 1) (hs : s∈Icc (-1) 1) :
    (gaussianBivariate r hr).SchurBothLE (gaussianBivariate s hs) ↔ |r|≤|s| := by
  change ((gaussianBivariate r hr).SchurLE (gaussianBivariate s hs) ∧
    (gaussianBivariate r hr).transpose.SchurLE (gaussianBivariate s hs).transpose) ↔ _
  rw [gaussianBivariate_transpose hr,gaussianBivariate_transpose hs,and_self,
    gaussianBivariate_schur_iff hr hs]

end Verification
