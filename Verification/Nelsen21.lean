import Verification.Nelsen21Analytic
import Copula.Archimedean.Truncated

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n21Psi (θ t : ℝ) : ℝ := n21Core θ (min t 1)

theorem n21Psi_convex {θ : ℝ} (hθ : 1 ≤ θ) : ConvexOn ℝ (Ici 0) (n21Psi θ) := by
  have hp : 0 < θ := by linarith
  refine ⟨convex_Ici 0,?_⟩
  intro x hx y hy a b ha hb hab
  let X := min x (1:ℝ)
  let Y := min y (1:ℝ)
  let Z := min (a*x+b*y) (1:ℝ)
  have hX : X ∈ Icc (0:ℝ) 1 := ⟨le_min hx zero_le_one,min_le_right _ _⟩
  have hY : Y ∈ Icc (0:ℝ) 1 := ⟨le_min hy zero_le_one,min_le_right _ _⟩
  have hZ : Z ∈ Icc (0:ℝ) 1 := ⟨le_min (add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)) zero_le_one,min_le_right _ _⟩
  have hW : a*X+b*Y ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg ha hX.1) (mul_nonneg hb hY.1)
    · nlinarith [mul_le_mul_of_nonneg_left hX.2 ha,mul_le_mul_of_nonneg_left hY.2 hb]
  have hWZ : a*X+b*Y ≤ Z := by
    apply le_min
    · exact add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hb)
    · exact hW.2
  have hm := n21Core_antitone hp hW hZ hWZ
  have hc := (n21Core_convex hθ).2 hX hY ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  exact hm.trans hc

noncomputable def n21Generator (θ : ℝ) (hθ : 1 ≤ θ) : BivariateGenerator where
  toFun := n21Psi θ
  invFun u := n21Core θ u
  nonneg t ht := (n21Core_mem (by linarith) ⟨le_min ht zero_le_one,min_le_right _ _⟩).1
  antitone x hx y hy hxy := n21Core_antitone (by linarith)
    ⟨le_min hx zero_le_one,min_le_right _ _⟩ ⟨le_min hy zero_le_one,min_le_right _ _⟩ (min_le_min_right 1 hxy)
  convex := n21Psi_convex hθ
  inv_nonneg u _ := (n21Core_mem (by linarith) u.property).1
  inv_antitone u v _ huv := n21Core_antitone (by linarith) u.property v.property huv
  inv_one := by simp [n21Core,Real.zero_rpow (by linarith : θ ≠ 0)]
  right_inv u _ := by
    unfold n21Psi
    rw [min_eq_left (n21Core_mem (by linarith) u.property).2]
    exact n21Core_involutive (by linarith) u.property

noncomputable def nelsen21 (θ : ℝ) (hθ : 1 ≤ θ) : Copula 2 := (n21Generator θ hθ).copula

theorem n21Psi_formula (θ t : ℝ) : n21Psi θ t = 1-(1-(max 0 (1-t))^θ)^θ⁻¹ := by
  have he : 1-min t (1:ℝ) = max 0 (1-t) := by
    rcases le_total t 1 with ht | ht
    · rw [min_eq_left ht,max_eq_right (by linarith)]
    · rw [min_eq_right ht,max_eq_left (by linarith)]; ring
  simp only [n21Psi,n21Core,he]

theorem nelsen21_cdf (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (nelsen21 θ hθ).cdf ![u,v] = if u = 0 ∨ v = 0 then 0 else
      1-(1-(max 0 ((1-(1-(u:ℝ))^θ)^θ⁻¹+(1-(1-(v:ℝ))^θ)^θ⁻¹-1))^θ)^θ⁻¹ := by
  simp only [nelsen21,BivariateGenerator.cdf_copula,BivariateGenerator.cdf,Matrix.cons_val_zero,Matrix.cons_val_one]
  split_ifs with h
  · simp only [h,ite_true]
  · simp only [h,ite_false]
    change n21Psi θ (n21Core θ u+n21Core θ v) = _
    rw [n21Psi_formula]
    unfold n21Core
    congr 5
    ring

theorem nelsen21_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (nelsen21 θ hθ).cdf ![u,v] =
      1-(1-(max 0 ((1-(1-(u:ℝ))^θ)^θ⁻¹+(1-(1-(v:ℝ))^θ)^θ⁻¹-1))^θ)^θ⁻¹ := by
  have hp : 0 < θ := by linarith
  have hroot (t : I) : (1-(1-(t:ℝ))^θ)^θ⁻¹ ≤ 1 :=
    Real.rpow_le_one (n21_inner_mem hp t.property).1 (n21_inner_mem hp t.property).2 (inv_pos.mpr hp).le
  rw [nelsen21_cdf]
  split_ifs with hz
  · rcases hz with hu | hv
    · subst u
      simp only [show ((0:I):ℝ) = 0 from rfl,sub_zero,Real.one_rpow,sub_self,
        Real.zero_rpow (inv_ne_zero hp.ne'),zero_add]
      rw [max_eq_left (by linarith [hroot v])]
      simp [Real.zero_rpow hp.ne']
    · subst v
      simp only [show ((0:I):ℝ) = 0 from rfl,sub_zero,Real.one_rpow,sub_self,
        Real.zero_rpow (inv_ne_zero hp.ne'),add_zero]
      rw [max_eq_left (by linarith [hroot u])]
      simp [Real.zero_rpow hp.ne']
  · rfl

theorem nelsen21_one : nelsen21 1 (by norm_num) = countermonotonic := by
  apply Copula.ext_cdf_two
  intro u v
  rw [nelsen21_cdf_full,cdf_countermonotonic]
  norm_num

end Verification
