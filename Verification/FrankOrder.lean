import Verification.FrankContinuity
import Verification.Nelsen17Order

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def frankOrderCoordinate (u : I) : I :=
  ⟨(2:ℝ)^(u:ℝ)-1,sub_nonneg.mpr (Real.one_le_rpow (by norm_num) u.property.1),
    by have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) u.property.2
       norm_num at h ⊢; linarith⟩

theorem frank_log_base_pos {θ : ℝ} (hθ : θ ≠ 0) (u v : I) :
    0 < 1+(Real.exp (-θ*(u:ℝ))-1)*(Real.exp (-θ*(v:ℝ))-1)/(Real.exp (-θ)-1) := by
  rcases lt_or_gt_of_ne hθ with hn | hp
  · have he : 0 < Real.exp (-θ)-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))
    have hu : 0 ≤ Real.exp (-θ*(u:ℝ))-1 := sub_nonneg.mpr
      (Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) u.property.1))
    have hv : 0 ≤ Real.exp (-θ*(v:ℝ))-1 := sub_nonneg.mpr
      (Real.one_le_exp_iff.mpr (mul_nonneg (by linarith) v.property.1))
    linarith [div_nonneg (mul_nonneg hu hv) he.le]
  · have hd : 0 < 1-Real.exp (-θ) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
    have hh := div_pos (frankDen_pos hp u.property v.property) hd
    have he : Real.exp (-θ)-1 ≠ 0 := by linarith
    convert hh using 1
    unfold frankDen
    field_simp [he,hd.ne']
    ring

theorem frank_nelsen17_identity {θ : ℝ} (hθ : θ ≠ 0) (u v : I) :
    frankRegularCDF u v θ =
      Real.log (1+(nelsen17 (θ/Real.log 2) (div_ne_zero hθ (Real.log_pos (by norm_num)).ne')).cdf
        ![frankOrderCoordinate u,frankOrderCoordinate v])/Real.log 2 := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he (x : ℝ) : ((2:ℝ)^x)^(-(θ/Real.log 2)) = Real.exp (-θ*x) := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),Real.rpow_def_of_pos (by norm_num)]
    congr 1
    field_simp
  have he1 : (2:ℝ)^(-(θ/Real.log 2)) = Real.exp (-θ) := by
    simpa only [Real.rpow_one,mul_one] using he 1
  rw [frankRegularCDF_formula hθ,nelsen17_cdf_full]
  change _ = Real.log (1+((1+(((1+((2:ℝ)^(u:ℝ)-1))^(-(θ/Real.log 2))-1)*
    ((1+((2:ℝ)^(v:ℝ)-1))^(-(θ/Real.log 2))-1))/((2:ℝ)^(-(θ/Real.log 2))-1))^
      (-(θ/Real.log 2)⁻¹)-1))/Real.log 2
  have hc (x : ℝ) : 1+(x-1)=x := by ring
  simp only [hc,he,he1]
  rw [Real.log_rpow (frank_log_base_pos hθ u v)]
  field_simp

theorem frankRegularCDF_monotone_nonzero {θ η : ℝ} (hθ : θ ≠ 0) (hη : η ≠ 0)
    (hθη : θ ≤ η) (u v : I) : frankRegularCDF u v θ ≤ frankRegularCDF u v η := by
  rw [frank_nelsen17_identity hθ,frank_nelsen17_identity hη]
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply div_le_div_of_nonneg_right _ hL.le
  apply Real.log_le_log
  · linarith [(nelsen17 (θ/Real.log 2) (div_ne_zero hθ hL.ne')).cdf_nonneg
      ![frankOrderCoordinate u,frankOrderCoordinate v]]
  · exact add_le_add_right (nelsen17_lowerOrthant_monotone (div_ne_zero hθ hL.ne')
      (div_ne_zero hη hL.ne') (div_le_div_of_nonneg_right hθη hL.le) _) 1

end Verification
