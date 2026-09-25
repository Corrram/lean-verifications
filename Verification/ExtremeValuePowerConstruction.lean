import Verification.ExtremeValuePowerRectangle
import Copula.Classical.Bivariate
import Copula.Classical.Characterization

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Verification

private theorem neg_log_nonneg (u : I) : 0≤-Real.log (u:ℝ) :=
  neg_nonneg.mpr (Real.log_nonpos u.property.1 u.property.2)

noncomputable def extremeValuePowerCDF (C : Copula 2) (θ : ℝ) (u v : I) : ℝ :=
  if u=0 ∨ v=0 then 0 else
    Real.exp (-extremeValuePowerLog C θ (-Real.log (u:ℝ)) (-Real.log (v:ℝ))
      (neg_log_nonneg u) (neg_log_nonneg v))

theorem extremeValuePowerCDF_zero_left (C : Copula 2) (θ : ℝ) (v : I) :
    extremeValuePowerCDF C θ 0 v=0 := by simp [extremeValuePowerCDF]

theorem extremeValuePowerCDF_zero_right (C : Copula 2) (θ : ℝ) (u : I) :
    extremeValuePowerCDF C θ u 0=0 := by simp [extremeValuePowerCDF]

theorem extremeValuePowerCDF_nonneg (C : Copula 2) (θ : ℝ) (u v : I) :
    0≤extremeValuePowerCDF C θ u v := by
  unfold extremeValuePowerCDF
  split_ifs <;> positivity

theorem extremeValuePowerCDF_positive_coords (C : Copula 2) (θ : ℝ) (u v : I)
    (hu : 0<(u:ℝ)) (hv : 0<(v:ℝ)) :
    extremeValuePowerCDF C θ u v=
      Real.exp (-extremeValuePowerLog C θ (-Real.log (u:ℝ)) (-Real.log (v:ℝ))
        (neg_log_nonneg u) (neg_log_nonneg v)) := by
  apply ite_eq_right
  rintro (h|h)
  · exact hu.ne' (congrArg Subtype.val h)
  · exact hv.ne' (congrArg Subtype.val h)

theorem extremeValuePowerLog_zero_left (C : Copula 2) (θ : ℝ) (hθ : 0<θ)
    (y : ℝ) (hy : 0≤y) : extremeValuePowerLog C θ 0 y (by norm_num) hy=y := by
  unfold extremeValuePowerLog
  simp only [Real.zero_rpow hθ.ne',extremeValueLog_zero_left,one_div,Real.rpow_rpow_inv hy hθ.ne']

theorem extremeValuePowerLog_zero_right (C : Copula 2) (θ : ℝ) (hθ : 0<θ)
    (x : ℝ) (hx : 0≤x) : extremeValuePowerLog C θ x 0 hx (by norm_num)=x := by
  unfold extremeValuePowerLog
  simp only [Real.zero_rpow hθ.ne',extremeValueLog_zero_right,one_div,Real.rpow_rpow_inv hx hθ.ne']

theorem extremeValuePowerCDF_one_left (C : Copula 2) (θ : ℝ) (hθ : 0<θ) (v : I) :
    extremeValuePowerCDF C θ 1 v=(v:ℝ) := by
  by_cases hv : v=0
  · simp [hv,extremeValuePowerCDF_zero_right]
  have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (fun h => hv (Subtype.ext h.symm))
  rw [extremeValuePowerCDF_positive_coords C θ 1 v (by norm_num) hvp]
  simp only [Set.Icc.coe_one,Real.log_one,neg_zero]
  rw [extremeValuePowerLog_zero_left C θ hθ,neg_neg,Real.exp_log hvp]

theorem extremeValuePowerCDF_one_right (C : Copula 2) (θ : ℝ) (hθ : 0<θ) (u : I) :
    extremeValuePowerCDF C θ u 1=(u:ℝ) := by
  by_cases hu : u=0
  · simp [hu,extremeValuePowerCDF_zero_left]
  have hup : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (fun h => hu (Subtype.ext h.symm))
  rw [extremeValuePowerCDF_positive_coords C θ u 1 hup (by norm_num)]
  simp only [Set.Icc.coe_one,Real.log_one,neg_zero]
  rw [extremeValuePowerLog_zero_right C θ hθ,neg_neg,Real.exp_log hup]

theorem extremeValuePowerCDF_mono (C : Copula 2) (hC : C.IsExtremeValue) (θ : ℝ) (hθ : 1≤θ)
    (u v u' v' : I) (hu : u≤u') (hv : v≤v') :
    extremeValuePowerCDF C θ u v≤extremeValuePowerCDF C θ u' v' := by
  by_cases hz : u=0 ∨ v=0
  · unfold extremeValuePowerCDF at *
    rw [ite_eq_left hz]
    exact extremeValuePowerCDF_nonneg C θ u' v'
  have hup : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (fun h => hz (Or.inl (Subtype.ext h.symm)))
  have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (fun h => hz (Or.inr (Subtype.ext h.symm)))
  rw [extremeValuePowerCDF_positive_coords C θ u v hup hvp,
    extremeValuePowerCDF_positive_coords C θ u' v' (hup.trans_le hu) (hvp.trans_le hv)]
  exact Real.exp_le_exp.mpr (neg_le_neg (extremeValuePowerLog_mono C hC θ hθ
    (neg_log_nonneg u') (neg_log_nonneg v')
    (neg_le_neg (Real.log_le_log hup hu)) (neg_le_neg (Real.log_le_log hvp hv))))

theorem extremeValuePowerCDF_rectangle (C : Copula 2) (hC : C.IsExtremeValue) (θ : ℝ) (hθ : 1≤θ)
    (a b c d : I) (hab : a≤b) (hcd : c≤d) :
    0≤extremeValuePowerCDF C θ b d-extremeValuePowerCDF C θ a d-
      extremeValuePowerCDF C θ b c+extremeValuePowerCDF C θ a c := by
  by_cases ha : a=0
  · rw [ha,extremeValuePowerCDF_zero_left,extremeValuePowerCDF_zero_left]
    linarith [extremeValuePowerCDF_mono C hC θ hθ b c b d le_rfl hcd]
  by_cases hc : c=0
  · rw [hc,extremeValuePowerCDF_zero_right,extremeValuePowerCDF_zero_right]
    linarith [extremeValuePowerCDF_mono C hC θ hθ a d b d hab le_rfl]
  have hap : 0<(a:ℝ) := lt_of_le_of_ne a.property.1 (fun h => ha (Subtype.ext h.symm))
  have hcp : 0<(c:ℝ) := lt_of_le_of_ne c.property.1 (fun h => hc (Subtype.ext h.symm))
  rw [extremeValuePowerCDF_positive_coords C θ b d (hap.trans_le hab) (hcp.trans_le hcd),
    extremeValuePowerCDF_positive_coords C θ a d hap (hcp.trans_le hcd),
    extremeValuePowerCDF_positive_coords C θ b c (hap.trans_le hab) hcp,
    extremeValuePowerCDF_positive_coords C θ a c hap hcp]
  have h := extremeValuePowerLog_exp_rectangle C hC θ hθ (neg_log_nonneg b) (neg_log_nonneg d)
    (neg_le_neg (Real.log_le_log hap hab)) (neg_le_neg (Real.log_le_log hcp hcd))
  linarith

theorem extremeValuePowerCDF_isClassical (C : Copula 2) (hC : C.IsExtremeValue) (θ : ℝ) (hθ : 1≤θ) :
    IsClassical (fun u : Fin 2→I => extremeValuePowerCDF C θ (u 0) (u 1)) := by
  exact IsClassical.ofBivariate _ (extremeValuePowerCDF_zero_left C θ) (extremeValuePowerCDF_zero_right C θ)
    (extremeValuePowerCDF_one_left C θ (by linarith)) (extremeValuePowerCDF_one_right C θ (by linarith))
    (extremeValuePowerCDF_rectangle C hC θ hθ)

noncomputable def extremeValuePower (C : Copula 2) (hC : C.IsExtremeValue) (θ : ℝ) (hθ : 1≤θ) : Copula 2 :=
  ofClassical _ (extremeValuePowerCDF_isClassical C hC θ hθ)

theorem extremeValuePower_cdf (C : Copula 2) (hC : C.IsExtremeValue) (θ : ℝ) (hθ : 1≤θ) (u v : I) :
    (extremeValuePower C hC θ hθ).cdf ![u,v]=extremeValuePowerCDF C θ u v := by
  rw [extremeValuePower,cdf_ofClassical]
  rfl

end Verification
