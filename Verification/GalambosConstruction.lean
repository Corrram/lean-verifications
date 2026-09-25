import Verification.SurvivalClaytonLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem tendsto_succ_pow_exp {f : ℕ→ℝ} {L : ℝ}
    (hf : Tendsto (fun n : ℕ => ((n:ℝ)+1)*(f n-1)) atTop (nhds L)) :
    Tendsto (fun n => (f n)^(n+1)) atTop (nhds (Real.exp L)) := by
  let g : ℕ→ℝ := fun n => f (n-1)-1
  have hg : Tendsto (fun n : ℕ => (n:ℝ)*g n) atTop (nhds L) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    simpa only [g,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using hf
  have h := (tendsto_add_atTop_iff_nat 1).mpr (Real.tendsto_one_add_pow_exp_of_tendsto hg)
  simpa only [g,Nat.add_sub_cancel,show ∀ x : ℝ,1+(x-1)=x by intro x; ring] using h

theorem galambos_maxima_limit_interior (δ : ℝ) (hδ : 0<δ)
    (u v : I) (hu : (u:ℝ)∈Ioo (0:ℝ) 1) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    Tendsto (fun n => (normalizedMaxima (clayton 2 δ hδ).survivalCopula n).cdf ![u,v])
      atTop (nhds ((u:ℝ)*(v:ℝ)*Real.exp (galambosTailKernel δ (-Real.log (u:ℝ)) (-Real.log (v:ℝ))))) := by
  have h := survivalClayton_linear_limit δ hδ (fun n : ℕ => (n:ℝ)+1)
    (fun _ => by positivity) (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    u v hu hv
  have hh := tendsto_succ_pow_exp h
  have he : (fun n => (normalizedMaxima (clayton 2 δ hδ).survivalCopula n).cdf ![u,v])=
      fun n : ℕ => ((clayton 2 δ hδ).survivalCopula.cdf
        ![unitPower u (((n:ℝ)+1)⁻¹) (by positivity),unitPower v (((n:ℝ)+1)⁻¹) (by positivity)])^(n+1) := by
    funext n
    rw [normalizedMaxima_cdf]
    congr 2
    ext i
    fin_cases i <;> rfl
  rw [he]
  simpa only [Real.exp_add,Real.exp_log hu.1,Real.exp_log hv.1] using hh

noncomputable def galambosCDF (δ : ℝ) (u : Fin 2→I) : ℝ :=
  if u 0=0 ∨ u 1=0 then 0
  else if u 0=1 then (u 1:ℝ)
  else if u 1=1 then (u 0:ℝ)
  else (u 0:ℝ)*(u 1:ℝ)*Real.exp (galambosTailKernel δ (-Real.log (u 0:ℝ)) (-Real.log (u 1:ℝ)))

theorem galambos_maxima_limit (δ : ℝ) (hδ : 0<δ) (u : Fin 2→I) :
    Tendsto (fun n => (normalizedMaxima (clayton 2 δ hδ).survivalCopula n).cdf u)
      atTop (nhds (galambosCDF δ u)) := by
  have hu : u=![u 0,u 1] := by ext i; fin_cases i <;> rfl
  by_cases h0 : u 0=0 ∨ u 1=0
  · rw [galambosCDF,ite_eq_left h0]
    rcases h0 with h|h
    · simp only [cdf_eq_zero_of_coord_eq_zero _ u 0 h]
      exact tendsto_const_nhds
    · simp only [cdf_eq_zero_of_coord_eq_zero _ u 1 h]
      exact tendsto_const_nhds
  rw [galambosCDF,ite_eq_right h0]
  by_cases h1 : u 0=1
  · rw [ite_eq_left h1]
    have he (C : Copula 2) : C.cdf u=(u 1:ℝ) := by
      conv_lhs => rw [hu,h1]
      exact cdf_two_one_left _ _
    simp only [he]
    exact tendsto_const_nhds
  rw [ite_eq_right h1]
  by_cases h2 : u 1=1
  · rw [ite_eq_left h2]
    have he (C : Copula 2) : C.cdf u=(u 0:ℝ) := by
      conv_lhs => rw [hu,h2]
      exact cdf_two_one_right _ _
    simp only [he]
    exact tendsto_const_nhds
  rw [ite_eq_right h2]
  have hi0 : (u 0:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne (u 0).property.1 (fun h => h0 (Or.inl (Subtype.ext h.symm))),
      lt_of_le_of_ne (u 0).property.2 (fun h => h1 (Subtype.ext h))⟩
  have hi1 : (u 1:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne (u 1).property.1 (fun h => h0 (Or.inr (Subtype.ext h.symm))),
      lt_of_le_of_ne (u 1).property.2 (fun h => h2 (Subtype.ext h))⟩
  have h := galambos_maxima_limit_interior δ hδ (u 0) (u 1) hi0 hi1
  rwa [← hu] at h

noncomputable def galambos (δ : ℝ) (hδ : 0<δ) : Copula 2 :=
  (exists_copula_of_pointwise_cdf_limit _ (galambosCDF δ) (galambos_maxima_limit δ hδ)).choose

theorem galambos_cdf (δ : ℝ) (hδ : 0<δ) : (galambos δ hδ).cdf=galambosCDF δ :=
  (exists_copula_of_pointwise_cdf_limit _ (galambosCDF δ) (galambos_maxima_limit δ hδ)).choose_spec

end Verification
