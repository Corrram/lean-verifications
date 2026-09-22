import Papers.AnsariRockel2026XiRho.BandOrder

/-! # Ordering across zero and the decreasing negative branch -/

open ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

theorem sourceBand_isSI (b : ℝ) (hb : 0 < b) : (sourceBand b hb).IsSI := by
  rw [sourceBand_eq_normalizedBand]
  exact normalizedBand_isSI b hb.le

theorem negativeSourceBand_isSD (b : ℝ) (hb : 0 < b) : (negativeSourceBand b hb).IsSD := by
  rw [negativeSourceBand_eq_response_reflection, Copula.isSD_reflect_second_iff]
  exact sourceBand_isSI b hb

theorem sourceBand_independence_order (b : ℝ) (hb : 0 < b) (u v : I) :
    (u : ℝ)*(v : ℝ) ≤ (sourceBand b hb).cdf ![u,v] := (sourceBand_isSI b hb).isPQD u v

theorem negativeSourceBand_independence_order (b : ℝ) (hb : 0 < b) (u v : I) :
    (negativeSourceBand b hb).cdf ![u,v] ≤ (u : ℝ)*(v : ℝ) := by
  rw [negativeSourceBand_cdf]
  have h := sourceBand_independence_order b hb (unitInterval.symm u) v
  change (1-(u : ℝ))*(v : ℝ) ≤ _ at h
  nlinarith only [h]

/-- This supplies the cross-zero case missing from same-sign parameter ordering. -/
theorem sourceBand_cross_sign_order (b d : ℝ) (hb : 0 < b) (hd : 0 < d) (u v : I) :
    (negativeSourceBand b hb).cdf ![u,v] ≤ (sourceBand d hd).cdf ![u,v] :=
  (negativeSourceBand_independence_order b hb u v).trans (sourceBand_independence_order d hd u v)

/-- Remark 3(c): explicit clamped conditional sections of the negative branch. -/
theorem negativeSourceBand_conditionalCDF (b : ℝ) (hb : 0 < b) (v : I) :
    (fun u => (negativeSourceBand b hb).conditionalCDF u v) =ᵐ[MeasureTheory.volume]
      fun u => unitClamp (sourceBandIntercept b v-b*(1-(u : ℝ))) := by
  have h := (unitInterval.measurePreserving_symm.quasiMeasurePreserving.ae_eq_comp
    (sourceBand_conditionalCDF b hb v))
  exact (conditionalCDF_reflect_first (sourceBand b hb) v).trans h

end Papers.AnsariRockel2026XiRho
