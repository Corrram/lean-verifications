import Verification.GalambosZeroLimit
import Papers.AnsariRockel2024.GalambosTails
import Verification.GalambosLimits

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem galambos_limit_comonotonic {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l atTop) (u : Fin 2→I) :
    Tendsto (fun i => (Verification.galambos (δ i) (hδ i)).cdf u) l
      (nhds ((comonotonic 2).cdf u)) := by
  apply Verification.copula_limit_comonotonic_of_powerDiagonal
    (fun i => Verification.galambos (δ i) (hδ i)) (fun i => 2-(2:ℝ)^(-1/δ i))
    (fun i => galambos_power_diagonal (δ i) (hδ i)) _ u
  have hi := tendsto_inv_atTop_zero.comp hd
  have hn := hi.neg
  simp only [neg_zero] at hn
  have hp := (Real.continuousAt_const_rpow (a := (2:ℝ)) (b := (0:ℝ)) (by norm_num)).tendsto.comp hn
  have hh := (tendsto_const_nhds (x := (2:ℝ))).sub hp
  simpa only [Function.comp_def,Real.rpow_zero,neg_div,one_div,
    show (2:ℝ)-1=1 by norm_num] using hh

theorem galambos_limit_independence_interior {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l (nhds 0))
    (u v : I) (hu : (u:ℝ)∈Ioo (0:ℝ) 1) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    Tendsto (fun i => (Verification.galambos (δ i) (hδ i)).cdf ![u,v]) l
      (nhds ((u:ℝ)*(v:ℝ))) := by
  have hk := Verification.galambos_kernel_limit_zero δ hδ hd
    (-Real.log (u:ℝ)) (-Real.log (v:ℝ))
    (neg_pos.mpr (Real.log_neg hu.1 hu.2)) (neg_pos.mpr (Real.log_neg hv.1 hv.2))
  have h := (Real.continuous_exp.continuousAt.tendsto.comp hk).const_mul ((u:ℝ)*(v:ℝ))
  have he : (fun i => (Verification.galambos (δ i) (hδ i)).cdf ![u,v])=
      fun i => (u:ℝ)*(v:ℝ)*Real.exp (Verification.galambosTailKernel (δ i) (-Real.log (u:ℝ)) (-Real.log (v:ℝ))) :=
    funext fun i => galambos_cdf_interior (δ i) (hδ i) u v hu hv
  rw [he]
  simpa only [Function.comp_def,Real.exp_zero,mul_one] using h

theorem galambos_limit_independence {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l (nhds 0)) (u : Fin 2→I) :
    Tendsto (fun i => (Verification.galambos (δ i) (hδ i)).cdf u) l
      (nhds ((independence 2).cdf u)) := by
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
  have h := galambos_limit_independence_interior δ hδ hd (u 0) (u 1) hi0 hi1
  rw [← hu] at h
  simpa only [cdf_independence,Fin.prod_univ_two] using h

end Papers.AnsariRockel2024
