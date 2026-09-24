import Verification.FrankDependence
import Verification.CubeFubini

open ProbabilityTheory MeasureTheory Set
open scoped unitInterval

namespace Verification

noncomputable def frankDen (θ u v : ℝ) : ℝ :=
  1-Real.exp (-θ)-(1-Real.exp (-θ*u))*(1-Real.exp (-θ*v))

theorem frankDen_pos {θ : ℝ} (hθ : 0 < θ) {u v : ℝ}
    (hu : u ∈ Icc 0 1) (hv : v ∈ Icc 0 1) : 0 < frankDen θ u v := by
  have he : 0 < Real.exp (-θ) := Real.exp_pos _
  have he1 : Real.exp (-θ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hu0 : Real.exp (-θ) ≤ Real.exp (-θ*u) := Real.exp_le_exp.mpr (by nlinarith [hu.2])
  have hv0 : Real.exp (-θ) ≤ Real.exp (-θ*v) := Real.exp_le_exp.mpr (by nlinarith [hv.2])
  have hv1 : Real.exp (-θ*v) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hv.1])
  have hm := mul_nonneg (sub_nonneg.mpr hu0) (sub_nonneg.mpr hv1)
  have hp := mul_pos (lt_of_lt_of_le he hv0) (sub_pos.mpr he1)
  dsimp [frankDen]
  nlinarith

noncomputable def frankDensity (θ : ℝ) (x : Fin 2 → I) : ℝ :=
  θ*(1-Real.exp (-θ))*Real.exp (-θ*(x 0:ℝ))*Real.exp (-θ*(x 1:ℝ)) /
    frankDen θ (x 0) (x 1)^2

theorem frankDensity_nonneg {θ : ℝ} (hθ : 0 < θ) (x : Fin 2 → I) :
    0 ≤ frankDensity θ x := by
  have he : 0 < 1-Real.exp (-θ) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  unfold frankDensity
  positivity

theorem continuous_frankDensity {θ : ℝ} (hθ : 0 < θ) : Continuous (frankDensity θ) := by
  apply Continuous.div
  · fun_prop
  · unfold frankDen; fun_prop
  · intro x
    exact pow_ne_zero _ (frankDen_pos hθ (x 0).property (x 1).property).ne'

theorem frankDen_inv_tp2 {θ : ℝ} (hθ : 0 < θ) :
    IsTP2 (fun u v : I => 1/frankDen θ u v) := by
  intro a b c d hab hcd
  have hp (u v : I) := frankDen_pos hθ u.property v.property
  have he : 0 ≤ 1-Real.exp (-θ) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hx : Real.exp (-θ*(b:ℝ)) ≤ Real.exp (-θ*(a:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [show (a:ℝ) ≤ b from hab])
  have hy : Real.exp (-θ*(d:ℝ)) ≤ Real.exp (-θ*(c:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [show (c:ℝ) ≤ d from hcd])
  have hi : frankDen θ a d*frankDen θ b c-frankDen θ a c*frankDen θ b d =
      (1-Real.exp (-θ))*(Real.exp (-θ*(a:ℝ))-Real.exp (-θ*(b:ℝ)))*
        (Real.exp (-θ*(c:ℝ))-Real.exp (-θ*(d:ℝ))) := by unfold frankDen; ring
  have hn := mul_nonneg (mul_nonneg he (sub_nonneg.mpr hx)) (sub_nonneg.mpr hy)
  have hd : frankDen θ a c*frankDen θ b d ≤ frankDen θ a d*frankDen θ b c := by linarith
  simp only [div_mul_div_comm, one_mul]
  exact div_le_div_of_nonneg_left zero_le_one (mul_pos (hp a c) (hp b d)) hd

theorem isMTP2_frankDensity {θ : ℝ} (hθ : 0 < θ) : IsMTP2 (frankDensity θ) := by
  rw [Copula.isMTP2_fin_two_iff]
  have hn : IsTP2 (fun u v : I => θ*(1-Real.exp (-θ))*Real.exp (-θ*(u:ℝ))*Real.exp (-θ*(v:ℝ))) := by
    intro a b c d _ _
    apply le_of_eq
    ring
  have hn0 (u v : I) : 0 ≤ θ*(1-Real.exp (-θ))*Real.exp (-θ*(u:ℝ))*Real.exp (-θ*(v:ℝ)) := by
    have he : 0 ≤ 1-Real.exp (-θ) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    positivity
  have hd (u v : I) : 0 ≤ 1/frankDen θ u v := (one_div_pos.mpr (frankDen_pos hθ u.property v.property)).le
  have ht := frankDen_inv_tp2 hθ
  have hh := hn.mul (ht.mul ht hd hd) hn0 (fun u v => mul_nonneg (hd u v) (hd u v))
  convert hh using 1
  funext u v
  simp only [frankDensity, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

noncomputable def frankPartial (θ u v : ℝ) : ℝ :=
  Real.exp (-θ*u)*(1-Real.exp (-θ*v))/frankDen θ u v

theorem frank_partial_derivative {θ u v : ℝ} (hd : frankDen θ u v ≠ 0) :
    HasDerivAt (fun y => frankPartial θ u y)
      (θ*(1-Real.exp (-θ))*Real.exp (-θ*u)*Real.exp (-θ*v)/frankDen θ u v^2) v := by
  have he := ((hasDerivAt_id v).const_mul (-θ)).exp
  have hn := (he.const_sub 1).const_mul (Real.exp (-θ*u))
  have hden := ((he.const_sub 1).const_mul (1-Real.exp (-θ*u))).const_sub (1-Real.exp (-θ))
  convert hn.div hden hd using 1
  · rfl
  · dsimp
    unfold frankDen at hd ⊢
    field_simp [hd]
    ring

noncomputable def frankRealCDF (θ u v : ℝ) : ℝ :=
  -Real.log (frankDen θ u v/(1-Real.exp (-θ)))/θ

theorem frank_cdf_derivative {θ u v : ℝ} (hθ : θ ≠ 0)
    (hd : frankDen θ u v ≠ 0) (he : 1-Real.exp (-θ) ≠ 0) :
    HasDerivAt (fun x => frankRealCDF θ x v) (frankPartial θ u v) u := by
  have hex := ((hasDerivAt_id u).const_mul (-θ)).exp
  have hden := ((hex.const_sub 1).mul_const (1-Real.exp (-θ*v))).const_sub (1-Real.exp (-θ))
  have hl := (hden.div_const (1-Real.exp (-θ))).log (div_ne_zero hd he)
  convert hl.neg.div_const θ using 1
  · rfl
  · dsimp [frankPartial]
    unfold frankDen at hd ⊢
    field_simp

theorem integral_frankDensity_second {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    (∫ y in Iic v, frankDensity θ ![u,y]) = frankPartial θ u v := by
  change (∫ y in Iic v, θ*(1-Real.exp (-θ))*Real.exp (-θ*(u:ℝ))*Real.exp (-θ*(y:ℝ)) /
    frankDen θ u y^2) = _
  rw [Copula.integral_unit_Iic (fun y =>
    θ*(1-Real.exp (-θ))*Real.exp (-θ*(u:ℝ))*Real.exp (-θ*y)/frankDen θ u y^2)]
  have hmem (y : ℝ) (hy : y ∈ uIcc 0 (v:ℝ)) : y ∈ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le v.property.1] at hy
    exact ⟨hy.1, hy.2.trans v.property.2⟩
  have hc : ContinuousOn (fun y : ℝ =>
      θ*(1-Real.exp (-θ))*Real.exp (-θ*(u:ℝ))*Real.exp (-θ*y)/frankDen θ u y^2)
      (uIcc 0 (v:ℝ)) := by
    apply ContinuousOn.div
    · fun_prop
    · unfold frankDen; fun_prop
    · intro y hy
      exact pow_ne_zero _ (frankDen_pos hθ u.property (hmem y hy)).ne'
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => frank_partial_derivative (frankDen_pos hθ u.property (hmem y hy)).ne')
    hc.intervalIntegrable
  simpa [frankPartial] using he

theorem integral_frankPartial_first {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    (∫ x in Iic u, frankPartial θ x v) = frankRealCDF θ u v := by
  rw [Copula.integral_unit_Iic (fun x => frankPartial θ x v)]
  have hmem (x : ℝ) (hx : x ∈ uIcc 0 (u:ℝ)) : x ∈ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le u.property.1] at hx
    exact ⟨hx.1, hx.2.trans u.property.2⟩
  have hc : ContinuousOn (fun x : ℝ => frankPartial θ x v) (uIcc 0 (u:ℝ)) := by
    unfold frankPartial
    apply ContinuousOn.div
    · fun_prop
    · unfold frankDen; fun_prop
    · intro x hx
      exact (frankDen_pos hθ (hmem x hx) v.property).ne'
  have hd : 1-Real.exp (-θ) ≠ 0 := ne_of_gt
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => frank_cdf_derivative hθ.ne' (frankDen_pos hθ (hmem x hx) v.property).ne' hd)
    hc.intervalIntegrable
  simpa [frankRealCDF, frankDen, hd] using he

theorem frankRealCDF_eq {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    frankRealCDF θ u v = (Copula.frank θ hθ).cdf ![u,v] := by
  have hd : 1-Real.exp (-θ) ≠ 0 := ne_of_gt
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  rw [Copula.frank_cdf_full]
  by_cases hh : u = 0 ∨ v = 0
  · rcases hh with hu | hv
    · subst u; simp [frankRealCDF, frankDen, hd]
    · subst v; simp [frankRealCDF, frankDen, hd]
  · simp only [hh, ite_false]
    unfold frankRealCDF
    congr 2
    congr 1
    unfold frankDen
    field_simp

theorem frank_toMeasure_density {θ : ℝ} (hθ : 0 < θ) :
    (Copula.frank θ hθ).toMeasure =
      (volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal (frankDensity θ x)) := by
  apply Copula.toMeasure_eq_withDensity_of_cdf_integral _
    (Copula.integrable_continuous_cube volume (continuous_frankDensity hθ))
    (frankDensity_nonneg hθ)
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, integral_cube_Iic_iterated
    (Copula.integrable_continuous_cube volume (continuous_frankDensity hθ))]
  simp_rw [integral_frankDensity_second hθ]
  rw [integral_frankPartial_first hθ, frankRealCDF_eq hθ]

theorem frank_hasMTP2Density {θ : ℝ} (hθ : 0 < θ) :
    (Copula.frank θ hθ).HasMTP2Density :=
  ⟨frankDensity θ, (continuous_frankDensity hθ).measurable, frankDensity_nonneg hθ,
    isMTP2_frankDensity hθ, frank_toMeasure_density hθ⟩

end Verification
