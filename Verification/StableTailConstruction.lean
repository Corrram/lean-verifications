import Verification.ExtremeValuePowerRectangle
import Copula.Classical.Bivariate
import Copula.Classical.Characterization
import Verification.SpectralTail

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Verification

structure StableTail where
  value : ℝ→ℝ→ℝ
  nonneg : ∀ {x y},0≤x→0≤y→0≤value x y
  zero_left : ∀ {y},0≤y→value 0 y=y
  zero_right : ∀ {x},0≤x→value x 0=x
  mono : ∀ {x₁ x₂ y₁ y₂},0≤x₁→0≤y₁→x₁≤x₂→y₁≤y₂→value x₁ y₁≤value x₂ y₂
  submodular : ∀ {x₁ x₂ y₁ y₂},0≤x₁→0≤y₁→x₁≤x₂→y₁≤y₂→
    value x₁ y₁+value x₂ y₂≤value x₁ y₂+value x₂ y₁
  homogeneous : ∀ {x y c},0≤x→0≤y→0≤c→value (c*x) (c*y)=c*value x y

noncomputable def spectralStableTail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω→ℝ) (hXi : Integrable X μ) (hYi : Integrable Y μ)
    (hX : ∀ ω,0≤X ω) (hY : ∀ ω,0≤Y ω)
    (hXm : ∫ ω,X ω ∂μ=1) (hYm : ∫ ω,Y ω ∂μ=1) : StableTail where
  value := spectralTail μ X Y
  nonneg := fun hx _ => spectralTail_nonneg μ X Y hX hx
  zero_left := spectralTail_zero_left μ X Y hY hYm
  zero_right := spectralTail_zero_right μ X Y hX hXm
  mono := fun _ _ hx hy => spectralTail_mono μ X Y hXi hYi hX hY hx hy
  submodular := fun _ _ hx hy => spectralTail_submodular μ X Y hXi hYi hX hY hx hy
  homogeneous := fun _ _ hc => spectralTail_homogeneous μ X Y _ _ _ hc

theorem StableTail.exp_rectangle (L : StableTail) {x₁ x₂ y₁ y₂ : ℝ}
    (hx : 0≤x₁) (hy : 0≤y₁) (hxx : x₁≤x₂) (hyy : y₁≤y₂) :
    0≤Real.exp (-L.value x₁ y₁)-Real.exp (-L.value x₁ y₂)-
      Real.exp (-L.value x₂ y₁)+Real.exp (-L.value x₂ y₂) :=
  exp_neg_four_point (L.mono hx hy le_rfl hyy) (L.mono hx hy hxx le_rfl)
    (L.submodular hx hy hxx hyy)

private theorem neg_log_nonneg (u : I) : 0≤-Real.log (u:ℝ) :=
  neg_nonneg.mpr (Real.log_nonpos u.property.1 u.property.2)

noncomputable def stableTailCDF (L : StableTail) (u v : I) : ℝ :=
  if u=0 ∨ v=0 then 0 else
    Real.exp (-L.value (-Real.log (u:ℝ)) (-Real.log (v:ℝ)))

theorem stableTailCDF_zero_left (L : StableTail) (v : I) :
    stableTailCDF L 0 v=0 := by simp [stableTailCDF]

theorem stableTailCDF_zero_right (L : StableTail) (u : I) :
    stableTailCDF L u 0=0 := by simp [stableTailCDF]

theorem stableTailCDF_nonneg (L : StableTail) (u v : I) :
    0≤stableTailCDF L u v := by
  unfold stableTailCDF
  split_ifs <;> positivity

theorem stableTailCDF_positive_coords (L : StableTail) (u v : I)
    (hu : 0<(u:ℝ)) (hv : 0<(v:ℝ)) :
    stableTailCDF L u v=
      Real.exp (-L.value (-Real.log (u:ℝ)) (-Real.log (v:ℝ))) := by
  apply ite_eq_right
  rintro (h|h)
  · exact hu.ne' (congrArg Subtype.val h)
  · exact hv.ne' (congrArg Subtype.val h)

theorem stableTailCDF_one_left (L : StableTail) (v : I) :
    stableTailCDF L 1 v=(v:ℝ) := by
  by_cases hv : v=0
  · simp [hv,stableTailCDF_zero_right]
  have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (fun h => hv (Subtype.ext h.symm))
  rw [stableTailCDF_positive_coords L 1 v (by norm_num) hvp]
  simp only [Set.Icc.coe_one,Real.log_one,neg_zero]
  rw [L.zero_left (neg_log_nonneg v),neg_neg,Real.exp_log hvp]

theorem stableTailCDF_one_right (L : StableTail) (u : I) :
    stableTailCDF L u 1=(u:ℝ) := by
  by_cases hu : u=0
  · simp [hu,stableTailCDF_zero_left]
  have hup : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (fun h => hu (Subtype.ext h.symm))
  rw [stableTailCDF_positive_coords L u 1 hup (by norm_num)]
  simp only [Set.Icc.coe_one,Real.log_one,neg_zero]
  rw [L.zero_right (neg_log_nonneg u),neg_neg,Real.exp_log hup]

theorem stableTailCDF_mono (L : StableTail)
    (u v u' v' : I) (hu : u≤u') (hv : v≤v') :
    stableTailCDF L u v≤stableTailCDF L u' v' := by
  by_cases hz : u=0 ∨ v=0
  · unfold stableTailCDF at *
    rw [ite_eq_left hz]
    exact stableTailCDF_nonneg L u' v'
  have hup : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (fun h => hz (Or.inl (Subtype.ext h.symm)))
  have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (fun h => hz (Or.inr (Subtype.ext h.symm)))
  rw [stableTailCDF_positive_coords L u v hup hvp,
    stableTailCDF_positive_coords L u' v' (hup.trans_le hu) (hvp.trans_le hv)]
  exact Real.exp_le_exp.mpr (neg_le_neg (L.mono
    (neg_log_nonneg u') (neg_log_nonneg v')
    (neg_le_neg (Real.log_le_log hup hu)) (neg_le_neg (Real.log_le_log hvp hv))))

theorem stableTailCDF_rectangle (L : StableTail)
    (a b c d : I) (hab : a≤b) (hcd : c≤d) :
    0≤stableTailCDF L b d-stableTailCDF L a d-
      stableTailCDF L b c+stableTailCDF L a c := by
  by_cases ha : a=0
  · rw [ha,stableTailCDF_zero_left,stableTailCDF_zero_left]
    linarith [stableTailCDF_mono L b c b d le_rfl hcd]
  by_cases hc : c=0
  · rw [hc,stableTailCDF_zero_right,stableTailCDF_zero_right]
    linarith [stableTailCDF_mono L a d b d hab le_rfl]
  have hap : 0<(a:ℝ) := lt_of_le_of_ne a.property.1 (fun h => ha (Subtype.ext h.symm))
  have hcp : 0<(c:ℝ) := lt_of_le_of_ne c.property.1 (fun h => hc (Subtype.ext h.symm))
  rw [stableTailCDF_positive_coords L b d (hap.trans_le hab) (hcp.trans_le hcd),
    stableTailCDF_positive_coords L a d hap (hcp.trans_le hcd),
    stableTailCDF_positive_coords L b c (hap.trans_le hab) hcp,
    stableTailCDF_positive_coords L a c hap hcp]
  have h := L.exp_rectangle (neg_log_nonneg b) (neg_log_nonneg d)
    (neg_le_neg (Real.log_le_log hap hab)) (neg_le_neg (Real.log_le_log hcp hcd))
  linarith

theorem stableTailCDF_isClassical (L : StableTail) :
    IsClassical (fun u : Fin 2→I => stableTailCDF L (u 0) (u 1)) := by
  exact IsClassical.ofBivariate _ (stableTailCDF_zero_left L) (stableTailCDF_zero_right L)
    (stableTailCDF_one_left L) (stableTailCDF_one_right L)
    (stableTailCDF_rectangle L)

noncomputable def stableTailCopula (L : StableTail) : Copula 2 :=
  ofClassical _ (stableTailCDF_isClassical L)

theorem stableTailCopula_cdf (L : StableTail) (u v : I) :
    (stableTailCopula L).cdf ![u,v]=stableTailCDF L u v := by
  rw [stableTailCopula,cdf_ofClassical]
  rfl

end Verification
