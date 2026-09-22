import Verification.IncreasingBandCDF
import Verification.IncreasingBandTP2
import Verification.QuadraticMeanInverse

/-! # An MTP2 density for the actual quadratic-band copula -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def quadraticRawBand (b : ℝ) (hb : 0 ≤ b) : IncreasingBand where
  width := 1/(b+1)
  width_pos := by positivity
  width_le_one := (div_le_one (by positivity)).mpr (by linarith)
  lower := fun u => b/(b+1)*(1-(1-(u:ℝ))^2)
  lower_measurable := by fun_prop
  lower_nonneg u := mul_nonneg (by positivity) (by nlinarith [u.property.1,u.property.2])
  lower_le u := by
    have h : 1-(1-(u:ℝ))^2 ≤ 1 := by nlinarith [sq_nonneg (1-(u:ℝ))]
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ b/(b+1) by positivity)
    have he : b/(b+1) = 1-1/(b+1) := by field_simp; ring
    simpa only [mul_one,he] using hh

theorem quadraticRawBand_lower_monotone (b : ℝ) (hb : 0 ≤ b) :
    Monotone (quadraticRawBand b hb).lower := by
  intro u v huv
  apply mul_le_mul_of_nonneg_left _ (show 0 ≤ b/(b+1) by positivity)
  nlinarith [u.property.2,v.property.2,show (u:ℝ) ≤ v from huv]

theorem quadraticRawBand_ratio (b : ℝ) (hb : 0 ≤ b) (t u : I) :
    ((t:ℝ)-(quadraticRawBand b hb).lower u)/(quadraticRawBand b hb).width =
      ((b+1)*(t:ℝ)-b)+b*(1-(u:ℝ))^2 := by
  dsimp [quadraticRawBand]
  have hn : b+1 ≠ 0 := by linarith
  field_simp
  ring

theorem quadraticRawBand_intercept_mem (b : ℝ) (hb : 0 ≤ b) (t : I) :
    (b+1)*(t:ℝ)-b ∈ Icc (-b) 1 := by
  constructor
  · nlinarith [mul_nonneg (show 0 ≤ b+1 by linarith) t.property.1]
  · nlinarith [mul_nonneg (show 0 ≤ b+1 by linarith) (sub_nonneg.mpr t.property.2)]

theorem quadraticRawBand_marginal (b : ℝ) (hb : 0 ≤ b) (t : I) :
    unitCDF (quadraticRawBand b hb).marginal t = quadraticMeanUnit b ((b+1)*(t:ℝ)-b) := by
  apply Subtype.ext
  change (quadraticRawBand b hb).marginal.real (Iic t) = quadraticMean b _
  rw [IncreasingBand.marginal_prefix]
  simp_rw [quadraticRawBand_ratio]
  rfl

/-- The positive band construction equals the previously constructed extremal copula. -/
theorem quadraticRawBand_copula (b : ℝ) (hb : 0 ≤ b) :
    (quadraticRawBand b hb).copula = quadraticBand b hb := by
  apply Copula.cdf_injective
  funext x
  have he : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
  rw [he,IncreasingBand.copula_cdf,quadraticBand_cdf]
  simp_rw [quadraticRawBand_ratio]
  let t := unitQuantile (quadraticRawBand b hb).marginal (x 1)
  have hm : quadraticMean b ((b+1)*(t:ℝ)-b) = (x 1:ℝ) := by
    have hh := unitCDF_quantile (quadraticRawBand b hb).marginal (x 1)
    rw [quadraticRawBand_marginal] at hh
    exact congrArg ((↑) : I → ℝ) hh
  have ha : (b+1)*(t:ℝ)-b = quadraticIntercept b hb (x 1) := by
    apply (quadraticMean_strictMonoOn hb).injOn (quadraticRawBand_intercept_mem b hb t)
      (quadraticIntercept_mem b hb (x 1))
    rw [hm,quadraticIntercept_mean]
  change (∫ u in Iic (x 0), unitClamp (((b+1)*(t:ℝ)-b)+b*(1-(u:ℝ))^2)) = _
  rw [ha]

/-- Every finite nonnegative parameter has a genuine Lebesgue MTP2 density. -/
theorem quadraticBand_hasMTP2Density (b : ℝ) (hb : 0 ≤ b) :
    (quadraticBand b hb).HasMTP2Density := by
  rw [← quadraticRawBand_copula b hb]
  exact IncreasingBand.copula_hasMTP2Density _ (quadraticRawBand_lower_monotone b hb)

end Verification
