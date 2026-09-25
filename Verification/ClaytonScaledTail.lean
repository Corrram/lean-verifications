import Verification.NormalizedMaxima
import Copula.Families.Clayton.CDF

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def galambosTailKernel (δ x y : ℝ) : ℝ :=
  (x^(-δ)+y^(-δ))^(-1/δ)

theorem clayton_scaled_cdf (δ : ℝ) (hδ : 0<δ) (c : ℝ) (hc : 0<c)
    (u v : I) (hu : 0<(u:ℝ)) (hv : 0<(v:ℝ)) :
    c*(clayton 2 δ hδ).cdf ![u,v]=
      ((c*(u:ℝ))^(-δ)+(c*(v:ℝ))^(-δ)-c^(-δ))^(-1/δ) := by
  rw [cdf_clayton δ hδ _ (by intro i; fin_cases i <;> assumption)]
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Nat.cast_ofNat]
  have hb : 0≤(u:ℝ)^(-δ)+(v:ℝ)^(-δ)-1 := by
    have h1 := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu u.property.2 (by linarith : -δ≤0)
    have h2 := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv v.property.2 (by linarith : -δ≤0)
    linarith
  have he : (c*(u:ℝ))^(-δ)+(c*(v:ℝ))^(-δ)-c^(-δ)=
      c^(-δ)*((u:ℝ)^(-δ)+(v:ℝ)^(-δ)-1) := by
    rw [Real.mul_rpow hc.le hu.le,Real.mul_rpow hc.le hv.le]
    ring
  rw [he,Real.mul_rpow (Real.rpow_nonneg hc.le _) hb,← Real.rpow_mul hc.le,
    show (-δ)*(-1/δ)=1 by field_simp,Real.rpow_one]
  congr 2
  ring

theorem clayton_scaled_cdf_limit {ι : Type*} {l : Filter ι}
    (δ : ℝ) (hδ : 0<δ) (c : ι→ℝ) (hc : ∀ i,0<c i) (hctop : Tendsto c l atTop)
    (u v : ι→I) (hu : ∀ i,0<(u i:ℝ)) (hv : ∀ i,0<(v i:ℝ))
    {x y : ℝ} (hx : 0<x) (hy : 0<y)
    (hux : Tendsto (fun i => c i*(u i:ℝ)) l (nhds x))
    (hvy : Tendsto (fun i => c i*(v i:ℝ)) l (nhds y)) :
    Tendsto (fun i => c i*(clayton 2 δ hδ).cdf ![u i,v i]) l (nhds (galambosTailKernel δ x y)) := by
  have h1 := hux.rpow_const (p := -δ) (Or.inl hx.ne')
  have h2 := hvy.rpow_const (p := -δ) (Or.inl hy.ne')
  have h0 := (tendsto_rpow_neg_atTop hδ).comp hctop
  have hsum := (h1.add h2).sub h0
  simp only [sub_zero,Function.comp_apply] at hsum
  have hpos : 0<x^(-δ)+y^(-δ) := add_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)
  have h := hsum.rpow_const (p := -1/δ) (Or.inl hpos.ne')
  have he : (fun i => c i*(clayton 2 δ hδ).cdf ![u i,v i])=
      fun i => ((c i*(u i:ℝ))^(-δ)+(c i*(v i:ℝ))^(-δ)-(c i)^(-δ))^(-1/δ) :=
    funext fun i => clayton_scaled_cdf δ hδ (c i) (hc i) (u i) (v i) (hu i) (hv i)
  rw [he]
  exact h

end Verification
