import Verification.StudentCopulaConditional
import Verification.ScaleMixtureReflection
import Verification.StudentNegativeEndpoint
import Verification.ScaleMixtureAbsoluteContinuity
import Verification.MTP2ConditionalIncreasing
import Copula.Rank.Region.XiRho.Support.StochasticBounds
import Copula.Dependence.ConditionalMonotonicity
import Mathlib.MeasureTheory.Measure.OpenPos

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped ENNReal unitInterval

namespace Verification

theorem antitone_of_continuous_ae_eq {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Antitone g) (he : f=ᵐ[volume]g) : Antitone f := by
  have hd := (volume.dense_of_ae he).prod (volume.dense_of_ae he)
  have hc : IsClosed {p : ℝ×ℝ | p.1<p.2 → f p.2≤f p.1} := by
    simp only [imp_iff_not_or,not_lt,ofPred_or]
    exact (isClosed_le continuous_snd continuous_fst).union
      (isClosed_le (hf.comp continuous_snd) (hf.comp continuous_fst))
  have hp (p : ℝ×ℝ) : p.1<p.2 → f p.2≤f p.1 := by
    apply (closure_minimal (t := {q : ℝ×ℝ | q.1<q.2 → f q.2≤f q.1}) ?_ hc) (hd p)
    intro q hq hlt
    rw [hq.1,hq.2]
    exact hg hlt.le
  intro x y hxy
  rcases eq_or_lt_of_le hxy with rfl|hlt
  · rfl
  · exact hp (x,y) hlt

noncomputable def studentConditionalScore (r ν b x : ℝ) : ℝ :=
  (b-r*x)/Real.sqrt ((ν+x^2)*(1-r^2)/(ν+1))

theorem continuous_studentConditionalScore {r : ℝ} (hr : r∈Ioo (-1) 1)
    {ν : ℝ} (hν : 0<ν) (b : ℝ) : Continuous (studentConditionalScore r ν b) := by
  have hd : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  unfold studentConditionalScore
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  exact (Real.sqrt_pos.mpr (by positivity)).ne'

theorem studentConditionalScore_not_antitone {r : ℝ} (hr : r∈Ioo (-1) 1)
    {ν : ℝ} (hν : 0<ν) : ¬Antitone (studentConditionalScore r ν (3*Real.sqrt ν)) := by
  intro h
  have he := h (show -Real.sqrt ν≤0 from neg_nonpos.mpr (Real.sqrt_nonneg ν))
  have hd : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have hbase : 0<ν*(1-r^2)/(ν+1) := by positivity
  have hs := Real.sqrt_pos.mpr hbase
  have hn := Real.sqrt_pos.mpr hν
  have htwo : 0<Real.sqrt 2 := by positivity
  dsimp only [studentConditionalScore] at he
  rw [zero_pow (by norm_num : (2:ℕ)≠0),add_zero,mul_zero,sub_zero,
    neg_sq,Real.sq_sqrt hν.le] at he
  have heq : (ν+ν)*(1-r^2)/(ν+1)=2*(ν*(1-r^2)/(ν+1)) := by ring
  rw [heq,Real.sqrt_mul (by norm_num : (0:ℝ)≤2),div_le_div_iff₀ hs (mul_pos htwo hs)] at he
  have hi : (3*Real.sqrt 2)*(Real.sqrt ν*Real.sqrt (ν*(1-r^2)/(ν+1)))≤
      (3+r)*(Real.sqrt ν*Real.sqrt (ν*(1-r^2)/(ν+1))) := by nlinarith [he]
  have hh := (mul_le_mul_iff_left₀ (mul_pos hn hs)).mp hi
  have ht := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  nlinarith [hr.2]

theorem studentBivariate_not_isSI {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) : ¬(studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).IsSI := by
  intro hSI
  let C := studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν
  let μ := marginal (studentTLaw (bivariateCorrelation r) ν hν) 0
  let b := 3*Real.sqrt ν
  let v := cdfUnit (marginal (studentTLaw (bivariateCorrelation r) ν hν) 1) b
  let N := normalScaleMixtureMarginal
    (gammaProbability ((ν+1)/2) ((ν+1)/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)
  have hN : marginal (studentTLaw (bivariateCorrelation 0) (ν+1) (by positivity)) 0=N :=
    gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef (by norm_num))
      (by intro j; fin_cases j <;> rfl) _ _ (by fun_prop) 0
  have hNc := student_marginal_cdf_continuous (r := 0) (by norm_num) (ν+1) (by positivity) 0
  have hNs := student_marginal_cdf_strictMono (r := 0) (by norm_num) (ν+1) (by positivity) 0
  rw [hN] at hNc hNs
  have hmp := measurePreserving_cdfUnit μ
    (student_marginal_cdf_continuous ⟨hr.1.le,hr.2.le⟩ ν hν 0)
  obtain ⟨g,hg,_,he⟩ := RankRegion.XiRho.Support.conditionalCDF_antitone_version C hSI v
  have heμ := hmp.quasiMeasurePreserving.ae_eq_comp he
  have hk := studentBivariate_conditionalCDF hr ν hν b
  have hfg : (fun x => ProbabilityTheory.cdf N (studentConditionalScore r ν b x))=ᵐ[μ]
      fun x => g (cdfUnit μ x) := by
    filter_upwards [hk,heμ] with x hx hxg
    have hs := studentConditionalDensity_cdf_standard hr ν hν x b
    exact (hx.trans hs).symm.trans hxg
  have hac : volume ≪ μ := by
    change volume ≪ marginal (studentTLaw (bivariateCorrelation r) ν hν) 0
    rw [student_marginal_density ⟨hr.1.le,hr.2.le⟩ ν hν 0]
    apply withDensity_absolutelyContinuous' (by
      apply Measurable.aemeasurable
      unfold studentMarginalPDF
      fun_prop)
    exact Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (studentMarginalPDF_pos hν x)).ne'
  have hcm : Monotone (cdfUnit μ) := by
    intro x y hxy
    exact (monotone_cdf μ) hxy
  have hm := antitone_of_continuous_ae_eq
    (hNc.comp (continuous_studentConditionalScore hr hν b)) (hg.comp_monotone hcm) (hac.ae_eq hfg)
  apply studentConditionalScore_not_antitone hr hν
  intro x y hxy
  exact hNs.le_iff_le.mp (hm hxy)

theorem studentBivariate_not_isCI {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) : ¬(studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).IsCI :=
  fun h => studentBivariate_not_isSI hr ν hν h.isSI

theorem studentBivariate_not_isSD {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) : ¬(studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).IsSD := by
  intro h
  have hneg : -r∈Ioo (-1) 1 := by constructor <;> linarith [hr.1,hr.2]
  apply studentBivariate_not_isSI hneg ν hν
  rw [studentBivariate_neg ⟨hr.1.le,hr.2.le⟩ ν hν]
  exact (isSI_reflect_second_iff _).mpr h

theorem studentBivariate_not_isCD {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) : ¬(studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).IsCD :=
  fun h => studentBivariate_not_isSD hr ν hν h.isSD

theorem studentBivariate_isSI_iff {r : ℝ} (hr : r∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) : (studentBivariate r hr ν hν).IsSI ↔ r=1 := by
  constructor
  · intro h
    by_contra hn
    have hm : r≠ -1 := by
      intro he
      subst r
      rw [studentBivariate_negative_one ν hν] at h
      exact not_isSI_countermonotonic h
    exact studentBivariate_not_isSI ⟨lt_of_le_of_ne hr.1 (Ne.symm hm),lt_of_le_of_ne hr.2 hn⟩ ν hν h
  · rintro rfl
    rw [studentBivariate_one ν hν]
    exact isSI_comonotonic

theorem studentBivariate_isCI_iff {r : ℝ} (hr : r∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) : (studentBivariate r hr ν hν).IsCI ↔ r=1 := by
  constructor
  · exact fun h => (studentBivariate_isSI_iff hr ν hν).mp h.isSI
  · rintro rfl
    rw [studentBivariate_one ν hν]
    exact isCI_comonotonic

theorem studentBivariate_isSD_iff {r : ℝ} (hr : r∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) : (studentBivariate r hr ν hν).IsSD ↔ r= -1 := by
  have hn : -r∈Icc (-1) 1 := by constructor <;> linarith [hr.1,hr.2]
  have he := studentBivariate_isSI_iff hn ν hν
  rw [studentBivariate_neg hr ν hν,isSI_reflect_second_iff] at he
  exact he.trans (by constructor <;> intro h <;> linarith)

theorem studentBivariate_isCD_iff {r : ℝ} (hr : r∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) : (studentBivariate r hr ν hν).IsCD ↔ r= -1 := by
  constructor
  · exact fun h => (studentBivariate_isSD_iff hr ν hν).mp h.isSD
  · rintro rfl
    rw [studentBivariate_negative_one ν hν]
    exact isCD_countermonotonic

theorem studentBivariate_not_hasMTP2Density {r : ℝ} (hr : r∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) : ¬(studentBivariate r hr ν hν).HasMTP2Density := by
  intro h
  have hi := (gaussianScaleMixture_absolutelyContinuous_iff hr
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)
    (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.mpr ht))).mp h.absolutelyContinuous
  exact studentBivariate_not_isCI hi ν hν (mtp2_isCI h)

end Verification
