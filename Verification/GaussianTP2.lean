import Verification.GaussianCopulaDensity
import Verification.GaussianDependence
import Copula.Dependence.DensityTotalPositivity
import Copula.Dependence.Density

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem gaussianConditionalPDF_isTP2 {r : ℝ} (hr : 0≤r) (v : NNReal) (hv : 0<v) :
    IsTP2 (fun x y : ℝ => gaussianPDFReal (r*x) v y) := by
  intro a b c d hab hcd
  have hvR : 0<(v:ℝ) := hv
  have he : -(d-r*a)^2/(2*(v:ℝ)) + -(c-r*b)^2/(2*(v:ℝ)) ≤
      -(c-r*a)^2/(2*(v:ℝ)) + -(d-r*b)^2/(2*(v:ℝ)) := by
    rw [← add_div,← add_div]
    apply (div_le_div_iff_of_pos_right (by positivity : 0<2*(v:ℝ))).mpr
    nlinarith [mul_nonneg hr (mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hcd))]
  have hh := Real.exp_le_exp.mpr he
  simp only [Real.exp_add] at hh
  unfold gaussianPDFReal
  nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg ((Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹))]

theorem gaussianDensityRatio_isTP2 {r : ℝ} (hr : 0≤r) (v : NNReal) (hv : 0<v) :
    IsTP2 (fun x y : ℝ => gaussianPDFReal (r*x) v y / gaussianPDFReal 0 1 y) := by
  have hg : IsTP2 (fun _ y : ℝ => (gaussianPDFReal 0 1 y)⁻¹) := by
    intro a b c d hab hcd
    exact le_of_eq (mul_comm _ _)
  simpa only [div_eq_mul_inv] using
    (gaussianConditionalPDF_isTP2 hr v hv).mul hg
      (fun _ _ => gaussianPDFReal_nonneg _ _ _)
      (fun _ _ => inv_nonneg.mpr (gaussianPDFReal_nonneg _ _ _))

theorem gaussianCopulaDensity_isTP2 {r : ℝ} (hr : r∈Ioo (-1) 1) (hp : 0≤r) :
    IsTP2 (fun u v : I => gaussianCopulaDensity r ![u,v]) := by
  intro a b c d hab hcd
  dsimp only
  have hn (u v : I) := gaussianCopulaDensity_nonneg r ![u,v]
  by_cases had : gaussianCopulaDensity r ![a,d]=0
  · rw [had,zero_mul]
    exact mul_nonneg (hn _ _) (hn _ _)
  by_cases hbc : gaussianCopulaDensity r ![b,c]=0
  · rw [hbc,mul_zero]
    exact mul_nonneg (hn _ _) (hn _ _)
  have hinter (u v : I) (h : gaussianCopulaDensity r ![u,v]≠0) :
      (u:ℝ)∈Ioo (0:ℝ) 1 ∧ (v:ℝ)∈Ioo (0:ℝ) 1 := by
    by_contra hnot
    apply h
    have hh : ¬((( ![u,v] 0:I):ℝ)∈Ioo (0:ℝ) 1 ∧ ((![u,v] 1:I):ℝ)∈Ioo (0:ℝ) 1) := hnot
    rw [gaussianCopulaDensity,ite_eq_right hh]
  have hformula (u v : I) (hu : (u:ℝ)∈Ioo (0:ℝ) 1) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
      gaussianCopulaDensity r ![u,v]=
        gaussianPDFReal (r*normalQuantile u) (1-r^2).toNNReal (normalQuantile v) /
          gaussianPDFReal 0 1 (normalQuantile v) := by
    have hh : ((![u,v] 0:I):ℝ)∈Ioo (0:ℝ) 1 ∧ ((![u,v] 1:I):ℝ)∈Ioo (0:ℝ) 1 := ⟨hu,hv⟩
    rw [gaussianCopulaDensity,ite_eq_left hh]
    rfl
  obtain ⟨ha,hd⟩ := hinter a d had
  obtain ⟨hb,hc⟩ := hinter b c hbc
  have hv : 0<(1-r^2).toNNReal := Real.toNNReal_pos.mpr (by nlinarith [hr.1,hr.2])
  have hq := gaussianDensityRatio_isTP2 hp (1-r^2).toNNReal hv
    (normalQuantile a) (normalQuantile b) (normalQuantile c) (normalQuantile d)
    (normalQuantile_strictMonoOn.monotoneOn ha hb hab)
    (normalQuantile_strictMonoOn.monotoneOn hc hd hcd)
  rw [hformula a d ha hd,hformula b c hb hc,hformula a c ha hc,hformula b d hb hd]
  exact hq

theorem gaussianBivariate_hasMTP2Density {r : ℝ} (hr : r∈Ioo (-1) 1) (hp : 0≤r) :
    (gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).HasMTP2Density := by
  exact ⟨gaussianCopulaDensity r,measurable_gaussianCopulaDensity r,
    gaussianCopulaDensity_nonneg r,(isMTP2_fin_two_iff _).mpr (gaussianCopulaDensity_isTP2 hr hp),
    gaussianBivariate_density hr⟩

theorem gaussianBivariate_hasMTP2Density_iff {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).HasMTP2Density ↔ 0≤r ∧ r<1 := by
  constructor
  · intro h
    exact ⟨(gaussianBivariate_isPQD_iff hr).mp (hasMTP2Density_isPQD _ h),
      ((gaussianBivariate_absolutelyContinuous_iff hr).mp h.absolutelyContinuous).2⟩
  · rintro ⟨hp,h1⟩
    exact gaussianBivariate_hasMTP2Density ⟨by linarith,h1⟩ hp

end Verification
