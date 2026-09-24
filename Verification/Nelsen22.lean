import Verification.Nelsen21Analytic
import Copula.Archimedean.Power
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n22Base (t : ℝ) : ℝ := 1-Real.sin (min t (Real.pi/2))

theorem n22Core_antitone : AntitoneOn (fun t : ℝ => 1-Real.sin t) (Icc 0 (Real.pi/2)) := by
  intro s hs t ht hst
  exact sub_le_sub_left (Real.monotoneOn_sin ⟨by linarith [Real.pi_pos,hs.1],hs.2⟩
    ⟨by linarith [Real.pi_pos,ht.1],ht.2⟩ hst) 1

theorem n22Core_convex : ConvexOn ℝ (Icc 0 (Real.pi/2)) (fun t => 1-Real.sin t) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
  · fun_prop
  · intro t _; exact ((Real.hasDerivAt_sin t).const_sub 1).hasDerivWithinAt
  · intro t _
    convert (Real.hasDerivAt_cos t).neg.hasDerivWithinAt using 1
  · intro t ht
    have ht' : t ∈ Ioo 0 (Real.pi/2) := by simpa only [interior_Icc] using ht
    simpa only [neg_neg] using Real.sin_nonneg_of_nonneg_of_le_pi ht'.1.le (by linarith [Real.pi_pos,ht'.2])

theorem n22Base_convex : ConvexOn ℝ (Ici 0) n22Base := by
  let k := Real.pi/2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  refine ⟨convex_Ici 0,?_⟩
  intro x hx y hy a b ha hb hab
  let X := min x k
  let Y := min y k
  let Z := min (a*x+b*y) k
  have hX : X ∈ Icc 0 k := ⟨le_min hx hk,min_le_right _ _⟩
  have hY : Y ∈ Icc 0 k := ⟨le_min hy hk,min_le_right _ _⟩
  have hZ : Z ∈ Icc 0 k := ⟨le_min (add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)) hk,min_le_right _ _⟩
  have hW : a*X+b*Y ∈ Icc 0 k := by
    constructor
    · exact add_nonneg (mul_nonneg ha hX.1) (mul_nonneg hb hY.1)
    · nlinarith [mul_le_mul_of_nonneg_left hX.2 ha,mul_le_mul_of_nonneg_left hY.2 hb]
  have hWZ : a*X+b*Y ≤ Z := by
    apply le_min
    · exact add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hb)
    · exact hW.2
  have hm := n22Core_antitone hW hZ hWZ
  have hc := n22Core_convex.2 hX hY ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  exact hm.trans hc

noncomputable def n22BaseGenerator : BivariateGenerator where
  toFun := n22Base
  invFun u := Real.arcsin (1-(u:ℝ))
  nonneg t _ := sub_nonneg.mpr (Real.sin_le_one _)
  antitone x hx y hy hxy := n22Core_antitone
    ⟨le_min hx (by positivity),min_le_right _ _⟩
    ⟨le_min hy (by positivity),min_le_right _ _⟩ (min_le_min_right _ hxy)
  convex := n22Base_convex
  inv_nonneg u _ := Real.arcsin_nonneg.mpr (sub_nonneg.mpr u.property.2)
  inv_antitone u v _ huv := Real.arcsin_le_arcsin (sub_le_sub_left (show (u:ℝ) ≤ v from huv) 1)
  inv_one := by simp
  right_inv u _ := by
    unfold n22Base
    rw [min_eq_left (Real.arcsin_le_pi_div_two _),Real.sin_arcsin (by linarith [u.property.2]) (by linarith [u.property.1])]
    ring

noncomputable def n22Generator (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) : BivariateGenerator :=
  n22BaseGenerator.innerPower θ⁻¹ ((one_le_inv₀ hθ).mpr hθ1)

noncomputable def nelsen22 (θ : ℝ) (hθ : θ ∈ Icc 0 1) : Copula 2 :=
  if hz : θ = 0 then independence 2 else
    (n22Generator θ (lt_of_le_of_ne hθ.1 (Ne.symm hz)) hθ.2).copula

theorem nelsen22_zero : nelsen22 0 (by norm_num) = independence 2 := by simp [nelsen22]

theorem nelsen22_cdf {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (u v : I) :
    (nelsen22 θ ⟨hθ.le,hθ1⟩).cdf ![u,v] = if u = 0 ∨ v = 0 then 0 else
      (1-Real.sin (min (Real.arcsin (1-(u:ℝ)^θ)+Real.arcsin (1-(v:ℝ)^θ)) (Real.pi/2)))^θ⁻¹ := by
  simp only [nelsen22,hθ.ne',dite_false,BivariateGenerator.cdf_copula,BivariateGenerator.cdf,
    Matrix.cons_val_zero,Matrix.cons_val_one,n22Generator,BivariateGenerator.innerPower,n22BaseGenerator,
    n22Base,coe_unitPower,inv_inv]
  rfl

theorem nelsen22_cdf_full {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (u v : I) :
    (nelsen22 θ ⟨hθ.le,hθ1⟩).cdf ![u,v] =
      (1-Real.sin (min (Real.arcsin (1-(u:ℝ)^θ)+Real.arcsin (1-(v:ℝ)^θ)) (Real.pi/2)))^θ⁻¹ := by
  have hn (t : I) : 0 ≤ Real.arcsin (1-(t:ℝ)^θ) :=
    Real.arcsin_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one t.property.1 t.property.2 hθ.le))
  rw [nelsen22_cdf hθ hθ1]
  split_ifs with hz
  · rcases hz with hu | hv
    · subst u
      simp only [show ((0:I):ℝ) = 0 from rfl,Real.zero_rpow hθ.ne',sub_zero,Real.arcsin_one]
      rw [min_eq_right (by linarith [hn v]),Real.sin_pi_div_two,sub_self,Real.zero_rpow (inv_ne_zero hθ.ne')]
    · subst v
      simp only [show ((0:I):ℝ) = 0 from rfl,Real.zero_rpow hθ.ne',sub_zero,Real.arcsin_one]
      rw [min_eq_right (by linarith [hn u]),Real.sin_pi_div_two,sub_self,Real.zero_rpow (inv_ne_zero hθ.ne')]
  · rfl

theorem nelsen22_cdf_printed {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (u v : I) :
    (nelsen22 θ ⟨hθ.le,hθ1⟩).cdf ![u,v] =
      if -(Real.pi/2) ≤ Real.arcsin ((u:ℝ)^θ-1)+Real.arcsin ((v:ℝ)^θ-1) then
        (1+Real.sin (Real.arcsin ((u:ℝ)^θ-1)+Real.arcsin ((v:ℝ)^θ-1)))^θ⁻¹ else 0 := by
  rw [nelsen22_cdf_full hθ hθ1]
  have he (t : I) : Real.arcsin ((t:ℝ)^θ-1) = -Real.arcsin (1-(t:ℝ)^θ) := by
    rw [show (t:ℝ)^θ-1 = -(1-(t:ℝ)^θ) by ring,Real.arcsin_neg]
  simp only [he]
  split_ifs with hs
  · rw [min_eq_left (by linarith),← neg_add,Real.sin_neg]
    rfl
  · rw [min_eq_right (by linarith),Real.sin_pi_div_two,sub_self,Real.zero_rpow (inv_ne_zero hθ.ne')]

end Verification
