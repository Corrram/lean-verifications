import Verification.Nelsen18Analytic

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n18Psi (θ t : ℝ) : ℝ := n18Core θ (min t (Real.exp (-θ)))
noncomputable def n18Inv (θ : ℝ) (u : I) : ℝ :=
  if u = 1 then 0 else Real.exp (θ/((u:ℝ)-1))

theorem n18Psi_convex {θ : ℝ} (hθ : 2 ≤ θ) : ConvexOn ℝ (Ici 0) (n18Psi θ) := by
  have hp : 0 < θ := by linarith
  let k := Real.exp (-θ)
  have hk : 0 ≤ k := (Real.exp_pos _).le
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
  have hm := n18Core_antitone hp hW hZ hWZ
  have hc := (n18Core_convex hθ).2 hX hY ha hb hab
  simp only [smul_eq_mul] at hc ⊢
  exact hm.trans hc

theorem n18Inv_nonneg (θ : ℝ) (u : I) : 0 ≤ n18Inv θ u := by
  unfold n18Inv
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem n18Inv_le_cutoff {θ : ℝ} (hθ : 0 < θ) (u : I) : n18Inv θ u ≤ Real.exp (-θ) := by
  unfold n18Inv
  split_ifs with hu
  · exact (Real.exp_pos _).le
  · have hu1 : (u:ℝ) < 1 := lt_of_le_of_ne u.property.2 (by simpa using hu)
    apply Real.exp_le_exp.mpr
    apply (div_le_iff_of_neg (by linarith : (u:ℝ)-1 < 0)).mpr
    nlinarith [u.property.1]

theorem n18Inv_antitone {θ : ℝ} (hθ : 0 < θ) : Antitone (n18Inv θ) := by
  intro u v huv
  by_cases hv : v = 1
  · simp only [n18Inv,hv,ite_true]
    exact n18Inv_nonneg θ u
  have hu : u ≠ 1 := by intro he; subst u; exact hv (le_antisymm v.property.2 huv)
  have hu1 : (u:ℝ) < 1 := lt_of_le_of_ne u.property.2 (by simpa using hu)
  have hv1 : (v:ℝ) < 1 := lt_of_le_of_ne v.property.2 (by simpa using hv)
  simp only [n18Inv,hu,hv,ite_false]
  apply Real.exp_le_exp.mpr
  rw [show (v:ℝ)-1 = -(1-v) by ring,show (u:ℝ)-1 = -(1-u) by ring]
  simp only [div_neg]
  exact neg_le_neg (div_le_div_of_nonneg_left hθ.le (by linarith)
    (sub_le_sub_left (show (u:ℝ) ≤ v from huv) 1))

noncomputable def n18Generator (θ : ℝ) (hθ : 2 ≤ θ) : BivariateGenerator where
  toFun := n18Psi θ
  invFun := n18Inv θ
  nonneg t ht := n18Core_nonneg (by linarith) ⟨le_min ht (Real.exp_pos _).le,min_le_right _ _⟩
  antitone x hx y hy hxy := n18Core_antitone (by linarith)
    ⟨le_min hx (Real.exp_pos _).le,min_le_right _ _⟩
    ⟨le_min hy (Real.exp_pos _).le,min_le_right _ _⟩ (min_le_min_right _ hxy)
  convex := n18Psi_convex hθ
  inv_nonneg u _ := n18Inv_nonneg θ u
  inv_antitone u v _ huv := n18Inv_antitone (by linarith) huv
  inv_one := by simp [n18Inv]
  right_inv u _ := by
    unfold n18Psi
    rw [min_eq_left (n18Inv_le_cutoff (by linarith) u)]
    by_cases hu : u = 1
    · subst u; simp [n18Inv,n18Core]
    · simp only [n18Inv,hu,ite_false,n18Core,Real.log_exp]
      have ht : θ ≠ 0 := by linarith
      have hu' : (u:ℝ)-1 ≠ 0 := sub_ne_zero.mpr (by simpa using hu)
      field_simp
      ring

noncomputable def nelsen18 (θ : ℝ) (hθ : 2 ≤ θ) : Copula 2 := (n18Generator θ hθ).copula

theorem nelsen18_cdf (θ : ℝ) (hθ : 2 ≤ θ) (u v : I) :
    (nelsen18 θ hθ).cdf ![u,v] = if u = 0 ∨ v = 0 then 0 else
      n18Psi θ (n18Inv θ u+n18Inv θ v) := by
  simp only [nelsen18,BivariateGenerator.cdf_copula,BivariateGenerator.cdf,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  rfl

theorem n18Psi_eq_max {θ t : ℝ} (hθ : 0 < θ) (ht : 0 ≤ t) (ht1 : t < 1) :
    n18Psi θ t = max 0 (1+θ/Real.log t) := by
  by_cases hb : t ≤ Real.exp (-θ)
  · unfold n18Psi
    rw [min_eq_left hb]
    exact (max_eq_right (n18Core_nonneg hθ ⟨ht,hb⟩)).symm
  · have hb' : Real.exp (-θ) ≤ t := (lt_of_not_ge hb).le
    have hp : 0 < t := (Real.exp_pos _).trans_le hb'
    have hl : Real.log t < 0 := Real.log_neg hp ht1
    have hlog : -θ ≤ Real.log t := by simpa using Real.log_le_log (Real.exp_pos (-θ)) hb'
    have hn : 1+θ/Real.log t ≤ 0 := by
      have hh : θ/Real.log t ≤ -1 := (div_le_iff_of_neg hl).mpr (by linarith)
      linarith
    rw [n18Psi,min_eq_right hb',n18Core_cutoff hθ.ne',max_eq_left hn]

theorem n18_sum_lt_one {θ : ℝ} (hθ : 2 ≤ θ) (u v : I) :
    n18Inv θ u+n18Inv θ v < 1 := by
  have hp : 0 < θ := by linarith
  have he : 2 < Real.exp θ := by linarith [Real.add_one_le_exp θ]
  have hb : 2*Real.exp (-θ) < 1 := by
    rw [Real.exp_neg,← div_eq_mul_inv]
    exact (div_lt_one (Real.exp_pos _)).mpr he
  linarith [n18Inv_le_cutoff hp u,n18Inv_le_cutoff hp v]

theorem n18Inv_zero (θ : ℝ) : n18Inv θ 0 = Real.exp (-θ) := by
  simp [n18Inv]
  ring

theorem nelsen18_cdf_full (θ : ℝ) (hθ : 2 ≤ θ) (u v : I) :
    (nelsen18 θ hθ).cdf ![u,v] = max 0 (1+θ/Real.log (n18Inv θ u+n18Inv θ v)) := by
  have hp : 0 < θ := by linarith
  have he := n18Psi_eq_max hp (add_nonneg (n18Inv_nonneg θ u) (n18Inv_nonneg θ v)) (n18_sum_lt_one hθ u v)
  rw [nelsen18_cdf,← he]
  split_ifs with hz
  · have hs : Real.exp (-θ) ≤ n18Inv θ u+n18Inv θ v := by
      rcases hz with hu | hv
      · rw [hu,n18Inv_zero]; linarith [n18Inv_nonneg θ v]
      · rw [hv,n18Inv_zero]; linarith [n18Inv_nonneg θ u]
    rw [n18Psi,min_eq_right hs,n18Core_cutoff hp.ne']
  · rfl

theorem nelsen18_cdf_of_lt_one (θ : ℝ) (hθ : 2 ≤ θ) (u v : I) (hu : u < 1) (hv : v < 1) :
    (nelsen18 θ hθ).cdf ![u,v] =
      max 0 (1+θ/Real.log (Real.exp (θ/((u:ℝ)-1))+Real.exp (θ/((v:ℝ)-1)))) := by
  rw [nelsen18_cdf_full]
  simp only [n18Inv,hu.ne,hv.ne,ite_false]

end Verification
