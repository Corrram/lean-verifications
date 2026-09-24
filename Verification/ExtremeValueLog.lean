import Verification.ExtremeValuePickands
import Copula.Rectangle
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Logarithmic rectangle inequalities from max-stability

These results require only max-stability of an actual copula, without a density
or smoothness assumption. They support the general extreme-value CI proof.
-/

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem extremeValue_exp_cdf_pos (C : Copula 2) (hC : C.IsExtremeValue)
    (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    0<C.cdf ![unitNegExp x hx,unitNegExp y hy] := by
  by_cases h : 0<x+y
  · rw [extremeValue_exp_coordinates C hC x y hx hy h]
    exact Real.exp_pos _
  · have hx0 : x=0 := by linarith
    have hy0 : y=0 := by linarith
    subst x; subst y
    have he : unitNegExp 0 (le_refl 0)=1 := by apply Subtype.ext; simp [unitNegExp]
    rw [he]
    simp

theorem extremeValue_log_rectangle (C : Copula 2) (hC : C.IsExtremeValue)
    (u₁ u₂ v₁ v₂ : I) (hu : u₁≤u₂) (hv : v₁≤v₂)
    (hp : 0<C.cdf ![u₁,v₁]) :
    Real.log (C.cdf ![u₁,v₂])+Real.log (C.cdf ![u₂,v₁]) ≤
      Real.log (C.cdf ![u₁,v₁])+Real.log (C.cdf ![u₂,v₂]) := by
  have hp12 : 0<C.cdf ![u₁,v₂] := hp.trans_le (C.monotone_cdf (by intro i; fin_cases i <;> simp_all))
  have hp21 : 0<C.cdf ![u₂,v₁] := hp.trans_le (C.monotone_cdf (by intro i; fin_cases i <;> simp_all))
  have hp22 : 0<C.cdf ![u₂,v₂] := hp12.trans_le (C.monotone_cdf (by intro i; fin_cases i <;> simp_all))
  let g : ℝ → ℝ := fun t => (C.cdf ![u₂,v₂])^t-(C.cdf ![u₁,v₂])^t-
    (C.cdf ![u₂,v₁])^t+(C.cdf ![u₁,v₁])^t
  have hpow (u v : I) (t : ℝ) (ht : 0<t) :
      C.cdf ![unitPower u t ht.le,unitPower v t ht.le]=(C.cdf ![u,v])^t := by
    convert hC ![u,v] t ht using 1
    congr 1
    funext i
    fin_cases i <;> rfl
  have hg (t : ℝ) (ht : 0<t) : 0≤g t := by
    have hh := C.rectangleIncrement_cdf_nonneg
      ![unitPower u₁ t ht.le,unitPower v₁ t ht.le]
      ![unitPower u₂ t ht.le,unitPower v₂ t ht.le] (by
        intro i
        fin_cases i
        · exact Real.rpow_le_rpow u₁.property.1 hu ht.le
        · exact Real.rpow_le_rpow v₁.property.1 hv ht.le)
    rw [rectangleIncrement_two] at hh
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at hh
    rw [hpow _ _ t ht,hpow _ _ t ht,hpow _ _ t ht,hpow _ _ t ht] at hh
    exact hh
  have hd (b : ℝ) (hb : 0<b) : HasDerivAt (fun t : ℝ => b^t) (Real.log b) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_rpow hb
  have hdg : HasDerivAt g
      (Real.log (C.cdf ![u₂,v₂])-Real.log (C.cdf ![u₁,v₂])-
        Real.log (C.cdf ![u₂,v₁])+Real.log (C.cdf ![u₁,v₁])) 0 :=
    (((hd _ hp22).sub (hd _ hp12)).sub (hd _ hp21)).add (hd _ hp)
  have hlim := hdg.tendsto_slope_zero_right
  have hn := ge_of_tendsto hlim (show ∀ᶠ t in 𝓝[>] (0:ℝ),
      0≤t⁻¹ • (g (0+t)-g 0) from by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0<t := ht
    have hg0 : g 0=0 := by simp [g]
    simp only [zero_add,hg0,sub_zero,smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ht'.le) (hg t ht'))
  linarith

/-- The stable tail function in nonnegative logarithmic coordinates. -/
noncomputable def extremeValueLog (C : Copula 2) (x y : ℝ) (hx : 0≤x) (hy : 0≤y) : ℝ :=
  -Real.log (C.cdf ![unitNegExp x hx,unitNegExp y hy])

theorem extremeValueLog_submodular (C : Copula 2) (hC : C.IsExtremeValue)
    {x₁ x₂ y₁ y₂ : ℝ} (hx : 0≤x₁) (hy : 0≤y₁) (hxx : x₁≤x₂) (hyy : y₁≤y₂) :
    extremeValueLog C x₁ y₁ hx hy + extremeValueLog C x₂ y₂ (hx.trans hxx) (hy.trans hyy) ≤
      extremeValueLog C x₁ y₂ hx (hy.trans hyy) + extremeValueLog C x₂ y₁ (hx.trans hxx) hy := by
  have he {x y : ℝ} (hx : 0≤x) (hy : 0≤y) (h : x≤y) : unitNegExp y hy≤unitNegExp x hx :=
    Real.exp_le_exp.mpr (neg_le_neg h)
  have hh := extremeValue_log_rectangle C hC
    (unitNegExp x₂ (hx.trans hxx)) (unitNegExp x₁ hx)
    (unitNegExp y₂ (hy.trans hyy)) (unitNegExp y₁ hy)
    (he hx (hx.trans hxx) hxx) (he hy (hy.trans hyy) hyy)
    (extremeValue_exp_cdf_pos C hC _ _ _ _)
  unfold extremeValueLog
  linarith

theorem extremeValueLog_zero_right (C : Copula 2) (x : ℝ) (hx : 0≤x) :
    extremeValueLog C x 0 hx (le_refl 0)=x := by
  have he : unitNegExp 0 (le_refl 0)=1 := by apply Subtype.ext; simp [unitNegExp]
  rw [extremeValueLog,he,Copula.cdf_two_one_right]
  simp only [unitNegExp,Real.log_exp,neg_neg]

theorem extremeValueLog_zero_left (C : Copula 2) (y : ℝ) (hy : 0≤y) :
    extremeValueLog C 0 y (le_refl 0) hy=y := by
  have he : unitNegExp 0 (le_refl 0)=1 := by apply Subtype.ext; simp [unitNegExp]
  rw [extremeValueLog,he,Copula.cdf_two_one_left]
  simp only [unitNegExp,Real.log_exp,neg_neg]

theorem extremeValueLog_homogeneous (C : Copula 2) (hC : C.IsExtremeValue)
    (x y t : ℝ) (hx : 0≤x) (hy : 0≤y) (ht : 0≤t) :
    extremeValueLog C (t*x) (t*y) (mul_nonneg ht hx) (mul_nonneg ht hy)=
      t*extremeValueLog C x y hx hy := by
  rcases ht.eq_or_lt with ht0 | htp
  · subst t
    simp only [zero_mul,extremeValueLog_zero_right]
  have he (z : ℝ) (hz : 0≤z) :
      unitPower (unitNegExp z hz) t ht=unitNegExp (t*z) (mul_nonneg ht hz) := by
    apply Subtype.ext
    change (Real.exp (-z))^t=Real.exp (-(t*z))
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
    congr 1
    ring
  have hh := hC ![unitNegExp x hx,unitNegExp y hy] t htp
  have hv : (fun i => unitPower (![unitNegExp x hx,unitNegExp y hy] i) t ht)=
      ![unitNegExp (t*x) (mul_nonneg ht hx),unitNegExp (t*y) (mul_nonneg ht hy)] := by
    funext i
    fin_cases i
    · exact he x hx
    · exact he y hy
  rw [hv] at hh
  unfold extremeValueLog
  rw [hh,Real.log_rpow (extremeValue_exp_cdf_pos C hC x y hx hy)]
  ring

theorem extremeValueLog_increment_first (C : Copula 2) (hC : C.IsExtremeValue)
    {x₁ x₂ y : ℝ} (hx : 0≤x₁) (hy : 0≤y) (hxx : x₁≤x₂) :
    0≤extremeValueLog C x₂ y (hx.trans hxx) hy-extremeValueLog C x₁ y hx hy ∧
    extremeValueLog C x₂ y (hx.trans hxx) hy-extremeValueLog C x₁ y hx hy≤x₂-x₁ := by
  constructor
  · have he : unitNegExp x₂ (hx.trans hxx)≤unitNegExp x₁ hx :=
      Real.exp_le_exp.mpr (neg_le_neg hxx)
    have hm : C.cdf ![unitNegExp x₂ (hx.trans hxx),unitNegExp y hy] ≤
        C.cdf ![unitNegExp x₁ hx,unitNegExp y hy] := C.monotone_cdf (by
      intro i; fin_cases i
      · exact he
      · exact le_refl _)
    have hh := Real.log_le_log (extremeValue_exp_cdf_pos C hC _ _ _ _) hm
    unfold extremeValueLog
    linarith
  · have hh := extremeValueLog_submodular C hC hx (le_refl 0) hxx hy
    rw [extremeValueLog_zero_right,extremeValueLog_zero_right] at hh
    linarith

theorem extremeValueLog_increment_second (C : Copula 2) (hC : C.IsExtremeValue)
    {x y₁ y₂ : ℝ} (hx : 0≤x) (hy : 0≤y₁) (hyy : y₁≤y₂) :
    0≤extremeValueLog C x y₂ hx (hy.trans hyy)-extremeValueLog C x y₁ hx hy ∧
    extremeValueLog C x y₂ hx (hy.trans hyy)-extremeValueLog C x y₁ hx hy≤y₂-y₁ := by
  constructor
  · have he : unitNegExp y₂ (hy.trans hyy)≤unitNegExp y₁ hy :=
      Real.exp_le_exp.mpr (neg_le_neg hyy)
    have hm : C.cdf ![unitNegExp x hx,unitNegExp y₂ (hy.trans hyy)] ≤
        C.cdf ![unitNegExp x hx,unitNegExp y₁ hy] := C.monotone_cdf (by
      intro i; fin_cases i
      · exact le_refl _
      · exact he)
    have hh := Real.log_le_log (extremeValue_exp_cdf_pos C hC _ _ _ _) hm
    unfold extremeValueLog
    linarith
  · have hh := extremeValueLog_submodular C hC (le_refl 0) hy hx hyy
    rw [extremeValueLog_zero_left,extremeValueLog_zero_left] at hh
    linarith

theorem extremeValueLog_bounds (C : Copula 2) (hC : C.IsExtremeValue)
    (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    max x y≤extremeValueLog C x y hx hy ∧ extremeValueLog C x y hx hy≤x+y := by
  have hh := extremeValueLog_increment_first C hC (le_refl 0) hy hx
  have ht := extremeValueLog_increment_second C hC hx (le_refl 0) hy
  rw [extremeValueLog_zero_left] at hh
  rw [extremeValueLog_zero_right] at ht
  exact ⟨max_le (by linarith [ht.1]) (by linarith [hh.1]),by linarith [hh.2]⟩

theorem extremeValue_pickands_bounds (C : Copula 2) (hC : C.IsExtremeValue) (t : I) :
    max (1-(t:ℝ)) (t:ℝ)≤copulaPickands C t ∧ copulaPickands C t≤1 := by
  have hx : 0≤(1-(t:ℝ))/2 := by linarith [t.property.2]
  have hy : 0≤(t:ℝ)/2 := by linarith [t.property.1]
  have hh := extremeValueLog_bounds C hC ((1-(t:ℝ))/2) ((t:ℝ)/2) hx hy
  have he : copulaPickands C t=2*extremeValueLog C ((1-(t:ℝ))/2) ((t:ℝ)/2) hx hy := by
    unfold copulaPickands pickandsRay extremeValueLog
    ring
  rw [he]
  exact ⟨max_le (by linarith [le_max_left ((1-(t:ℝ))/2) ((t:ℝ)/2)])
    (by linarith [le_max_right ((1-(t:ℝ))/2) ((t:ℝ)/2)]),by linarith [hh.2]⟩

end Verification
