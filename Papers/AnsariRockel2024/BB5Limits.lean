import Papers.AnsariRockel2024.BB5Tails
import Verification.GalambosLimits
import Verification.GalambosZeroLimit
import Verification.CopulaUniformLimit
import Copula.Families.Gumbel

open ProbabilityTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem bb5_limit_comonotonic {ι : Type*} {l : Filter ι}
    (θ : ℝ) (hθ : 1≤θ) (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l atTop)
    (u : Fin 2→I) :
    Tendsto (fun i => (Verification.bb5 θ (δ i) hθ (hδ i)).cdf u) l
      (nhds ((comonotonic 2).cdf u)) := by
  apply Verification.copula_limit_comonotonic_of_powerDiagonal
    (fun i => Verification.bb5 θ (δ i) hθ (hδ i))
    (fun i => (2-(2:ℝ)^(-1/δ i))^(1/θ))
    (fun i => by simpa only [bb5_extremalCoefficient] using
      (bb5_isExtremeValue θ (δ i) hθ (hδ i)).hasPowerDiagonal) _ u
  have hn := (tendsto_inv_atTop_zero.comp hd).neg
  simp only [neg_zero] at hn
  have hp := (Real.continuousAt_const_rpow (a := (2:ℝ)) (b := (0:ℝ)) (by norm_num)).tendsto.comp hn
  have hh : Tendsto (fun i => 2-(2:ℝ)^(-1/δ i)) l (nhds 1) := by
    simpa only [Function.comp_def,Real.rpow_zero,neg_div,one_div,
      show (2:ℝ)-1=1 by norm_num] using (tendsto_const_nhds (x := (2:ℝ))).sub hp
  simpa only [Function.comp_def,Real.one_rpow] using
    (Real.continuousAt_rpow_const 1 (1/θ) (Or.inl one_ne_zero)).tendsto.comp hh

theorem bb5_limit_gumbel_interior {ι : Type*} {l : Filter ι}
    (θ : ℝ) (hθ : 1≤θ) (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l (nhds 0))
    (u v : I) (hu : (u:ℝ)∈Ioo (0:ℝ) 1) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    Tendsto (fun i => (Verification.bb5 θ (δ i) hθ (hδ i)).cdf ![u,v]) l
      (nhds ((gumbel θ hθ).cdf ![u,v])) := by
  have hx := Real.rpow_pos_of_pos (neg_pos.mpr (Real.log_neg hu.1 hu.2)) θ
  have hy := Real.rpow_pos_of_pos (neg_pos.mpr (Real.log_neg hv.1 hv.2)) θ
  have hk := Verification.galambos_kernel_limit_zero δ hδ hd _ _ hx hy
  have hh := (tendsto_const_nhds (x := (-Real.log (u:ℝ))^θ+(-Real.log (v:ℝ))^θ)).sub hk
  simp only [sub_zero] at hh
  have hr := (Real.continuousAt_rpow_const _ (1/θ) (Or.inr (by positivity))).tendsto.comp hh
  have he := Real.continuous_exp.continuousAt.tendsto.comp hr.neg
  simp only [bb5_cdf_interior θ _ hθ _ u v hu hv]
  rw [cdf_gumbel θ hθ _ (by
    intro i; fin_cases i
    · exact fun h => hu.1.ne' (congrArg Subtype.val h)
    · exact fun h => hv.1.ne' (congrArg Subtype.val h))]
  simpa only [Function.comp_def,Verification.bb5TailKernel,one_div,
    Matrix.cons_val_zero,Matrix.cons_val_one] using he

theorem bb5_limit_gumbel {ι : Type*} {l : Filter ι}
    (θ : ℝ) (hθ : 1≤θ) (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l (nhds 0)) (u : Fin 2→I) :
    Tendsto (fun i => (Verification.bb5 θ (δ i) hθ (hδ i)).cdf u) l
      (nhds ((gumbel θ hθ).cdf u)) := by
  have hu : u=![u 0,u 1] := by ext i; fin_cases i <;> rfl
  by_cases hz : ∃ j,u j=0
  · obtain ⟨j,hj⟩ := hz
    simp only [cdf_eq_zero_of_coord_eq_zero _ u j hj]
    exact tendsto_const_nhds
  by_cases h0 : u 0=1
  · have he (C : Copula 2) : C.cdf u=(u 1:ℝ) := by
      conv_lhs => rw [hu,h0]
      exact cdf_two_one_left _ _
    simp only [he]
    exact tendsto_const_nhds
  by_cases h1 : u 1=1
  · have he (C : Copula 2) : C.cdf u=(u 0:ℝ) := by
      conv_lhs => rw [hu,h1]
      exact cdf_two_one_right _ _
    simp only [he]
    exact tendsto_const_nhds
  have hp (j) : 0<(u j:ℝ) := lt_of_le_of_ne (u j).property.1
    (fun h => hz ⟨j,Subtype.ext h.symm⟩)
  have hi0 : (u 0:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨hp 0,lt_of_le_of_ne (u 0).property.2 (fun h => h0 (Subtype.ext h))⟩
  have hi1 : (u 1:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨hp 1,lt_of_le_of_ne (u 1).property.2 (fun h => h1 (Subtype.ext h))⟩
  have h := bb5_limit_gumbel_interior θ hθ δ hδ hd (u 0) (u 1) hi0 hi1
  rw [← hu] at h
  exact h


theorem bb5_limit_comonotonic_uniform {ι : Type*} {l : Filter ι}
    (θ : ℝ) (hθ : 1≤θ) (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l atTop) :
    TendstoUniformly (fun i => (Verification.bb5 θ (δ i) hθ (hδ i)).cdf) (comonotonic 2).cdf l :=
  Verification.copula_cdf_uniform_limit_of_pointwise _ _ (bb5_limit_comonotonic θ hθ δ hδ hd)

theorem bb5_limit_gumbel_uniform {ι : Type*} {l : Filter ι}
    (θ : ℝ) (hθ : 1≤θ) (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l (nhds 0)) :
    TendstoUniformly (fun i => (Verification.bb5 θ (δ i) hθ (hδ i)).cdf) (gumbel θ hθ).cdf l :=
  Verification.copula_cdf_uniform_limit_of_pointwise _ _ (bb5_limit_gumbel θ hθ δ hδ hd)

end Papers.AnsariRockel2024
