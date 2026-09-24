import Verification.Nelsen16Density
import Verification.StochasticRigidity

open ProbabilityTheory Set Copula Filter
open scoped unitInterval Topology

namespace Verification

theorem n16Inv_deriv_pos {θ u : ℝ} (hu : 0 < u) :
    HasDerivAt (n16Inv θ) (-n16Weight θ u) u := by
  have hd := ((hasDerivAt_id u).const_sub 1).mul
    (((hasDerivAt_const u θ).div (hasDerivAt_id u) hu.ne').const_add 1)
  convert hd using 1
  · rfl
  · dsimp [n16Weight]; field_simp [hu.ne']; ring

theorem n16RealCDF_deriv_pos {θ u v : ℝ} (hθ : 0 < θ) (hu : 0 < u) :
    HasDerivAt (fun x => n16RealCDF θ x v) (n16Partial θ u v) u := by
  have hh := (n16Psi_deriv (t := n16Inv θ u+n16Inv θ v) hθ).comp u
    ((n16Inv_deriv_pos (θ := θ) hu).add_const (n16Inv θ v))
  convert hh using 1
  · rfl
  · dsimp [n16Partial]; ring

theorem n16Weight_deriv {θ u : ℝ} (hu : 0 < u) :
    HasDerivAt (n16Weight θ) (-2*θ/u^3) u := by
  have hh := (((hasDerivAt_const u θ).div ((hasDerivAt_id u).pow 2) (pow_ne_zero _ hu.ne')).const_add 1)
  convert hh using 1
  · rfl
  · dsimp; field_simp; ring

theorem n16Partial_deriv_left {θ u v : ℝ} (hθ : 0 < θ) (hu : 0 < u) :
    HasDerivAt (fun x => n16Partial θ x v)
      (n16Second θ (n16Inv θ u+n16Inv θ v)*(n16Weight θ u)^2+
        n16PsiDeriv θ (n16Inv θ u+n16Inv θ v)*(2*θ/u^3)) u := by
  have hh := (((n16Psi_deriv2 (t := n16Inv θ u+n16Inv θ v) hθ).comp u
    ((n16Inv_deriv_pos (θ := θ) hu).add_const (n16Inv θ v))).neg).mul (n16Weight_deriv (θ := θ) hu)
  convert hh using 1
  · rfl
  · dsimp [n16Second]; ring

theorem n16RealCDF_eq {θ : ℝ} (hθ : 0 < θ) (u v : I) (hu : u ≠ 0) (hv : v ≠ 0) :
    n16RealCDF θ u v = (nelsen16 θ hθ.le).cdf ![u,v] := by
  rw [nelsen16, dite_eq_right hθ.ne', BivariateGenerator.cdf_copula, BivariateGenerator.cdf]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hu, hv, or_self, ite_false]
  rfl

theorem n16_curvature_nonpos_of_isSI {θ : ℝ} (hθ : 0 < θ)
    (hC : (nelsen16 θ hθ.le).IsSI) (v : I) (hv : 0 < (v:ℝ)) :
    n16Second θ (n16Inv θ v)*(1+θ)^2+n16PsiDeriv θ (n16Inv θ v)*(2*θ) ≤ 0 := by
  have hc : ConcaveOn ℝ (Icc (1/2:ℝ) 1) (fun u => n16RealCDF θ u v) := by
    apply ((cdfSection_concave_of_isSI hC v).subset (by intro u hu; constructor <;> linarith [hu.1,hu.2])
      (convex_Icc _ _)).congr
    intro u hu
    have huI : u ∈ Icc (0:ℝ) 1 := ⟨by linarith [hu.1],hu.2⟩
    unfold cdfSection
    rw [projIcc_of_mem zero_le_one huI]
    exact (n16RealCDF_eq hθ ⟨u,huI⟩ v
      (ne_of_gt (show (0:I) < ⟨u,huI⟩ by change 0 < u; linarith [hu.1]))
      (ne_of_gt (show (0:I) < v from hv))).symm
  have hm : AntitoneOn (fun u => n16Partial θ u v) (Icc (1/2:ℝ) 1) := by
    intro a ha b hb hab
    have hh := hc.antitoneOn_deriv (fun u hu =>
      (n16RealCDF_deriv_pos hθ (by linarith [hu.1] : 0 < u)).differentiableAt) ha hb hab
    rw [(n16RealCDF_deriv_pos hθ (by linarith [ha.1] : 0 < a)).deriv,
      (n16RealCDF_deriv_pos hθ (by linarith [hb.1] : 0 < b)).deriv] at hh
    exact hh
  have hd := (n16Partial_deriv_left (v := (v:ℝ)) hθ (by norm_num : (0:ℝ) < 1)).hasDerivWithinAt
    (s := Icc (1/2:ℝ) 1)
  have he := hd.nonpos_of_antitoneOn ((uniqueDiffOn_Icc (by norm_num : (1/2:ℝ) < 1))
    1 (by norm_num)).accPt hm
  simpa [n16Inv, n16Weight] using he

theorem n16Rad_inv {θ : ℝ} (hθ : 0 < θ) (v : I) (hv : 0 < (v:ℝ)) :
    n16Rad θ (n16Inv θ v) = (v:ℝ)+θ/(v:ℝ) := by
  have he : 1-n16Inv θ v-θ = (v:ℝ)-θ/(v:ℝ) := by unfold n16Inv; field_simp; ring
  have hs : ((v:ℝ)-θ/(v:ℝ))^2+4*θ = ((v:ℝ)+θ/(v:ℝ))^2 := by field_simp; ring
  unfold n16Rad
  rw [he, hs, Real.sqrt_sq (by positivity)]

theorem n16_boundary_polynomial_nonpos {θ : ℝ} (hθ : 0 < θ)
    (hC : (nelsen16 θ hθ.le).IsSI) (v : I) (hv : 0 < (v:ℝ)) :
    (v:ℝ)*(1+θ)^2-((v:ℝ)^2+θ)^2 ≤ 0 := by
  have hh := n16_curvature_nonpos_of_isSI hθ hC v hv
  have hv0 : v ≠ 0 := ne_of_gt (show (0:I) < v from hv)
  have he : n16Psi θ (n16Inv θ v) = (v:ℝ) := (nelsen16Generator θ hθ).right_inv v hv0
  rw [n16PsiDeriv_eq hθ, he] at hh
  unfold n16Second at hh
  rw [n16Rad_inv hθ v hv] at hh
  have hb : 0 < (v:ℝ)^2+θ := by positivity
  have hid : 2*θ/((v:ℝ)+θ/(v:ℝ))^3*(1+θ)^2+
      (-(v:ℝ)/((v:ℝ)+θ/(v:ℝ)))*(2*θ) =
      (2*θ*(v:ℝ)^2/((v:ℝ)^2+θ)^3)*((v:ℝ)*(1+θ)^2-((v:ℝ)^2+θ)^2) := by
    have hd : (v:ℝ)+θ/(v:ℝ) ≠ 0 := ne_of_gt (by positivity)
    field_simp [hv.ne',hb.ne',hd]
    ring
  rw [hid] at hh
  have hp : 0 < 2*θ*(v:ℝ)^2/((v:ℝ)^2+θ)^3 := by positivity
  nlinarith

theorem nelsen16_ci_requires_three_pos {θ : ℝ} (hθ : 0 < θ)
    (hC : (nelsen16 θ hθ.le).IsCI) : 3 ≤ θ := by
  let B : ℝ → ℝ := fun v => v*(1+θ)^2-(v^2+θ)^2
  have hB1 : B 1 = 0 := by dsimp [B]; ring
  have hd : HasDerivAt B ((θ+1)*(θ-3)) 1 := by
    have hh := ((hasDerivAt_id (1:ℝ)).mul_const ((1+θ)^2)).sub
      ((((hasDerivAt_id (1:ℝ)).pow 2).add_const θ).pow 2)
    convert hh using 1
    · rfl
    · norm_num; ring
  have ht : Tendsto (slope B 1) (𝓝[<] (1:ℝ)) (𝓝 ((θ+1)*(θ-3))) :=
    hd.tendsto_slope.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_lt hx))
  have hn : 0 ≤ (θ+1)*(θ-3) := by
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,
      (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1)))] with v hv hv0
    have hh := n16_boundary_polynomial_nonpos hθ hC.1 ⟨v,⟨le_of_lt hv0,le_of_lt hv⟩⟩ hv0
    rw [slope_def_field, hB1, sub_zero]
    exact div_nonneg_of_nonpos hh (sub_nonpos.mpr (le_of_lt hv))
  nlinarith

theorem nelsen16_ci_iff (θ : ℝ) (hθ : 0 ≤ θ) : (nelsen16 θ hθ).IsCI ↔ 3 ≤ θ := by
  constructor
  · intro hC
    by_cases hz : θ = 0
    · subst θ
      rw [nelsen16_zero] at hC
      exact (not_isSI_countermonotonic hC.1).elim
    · exact nelsen16_ci_requires_three_pos (lt_of_le_of_ne hθ (Ne.symm hz)) hC
  · exact nelsen16_isCI

end Verification
