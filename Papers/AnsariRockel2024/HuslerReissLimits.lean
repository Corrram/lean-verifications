import Papers.AnsariRockel2024.HuslerReissTails
import Verification.GalambosLimits
import Verification.CopulaUniformLimit

open ProbabilityTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem huslerReiss_limit_comonotonic {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l atTop) (u : Fin 2→I) :
    Tendsto (fun i => (Verification.huslerReissPositive (δ i) (hδ i)).cdf u) l
      (nhds ((comonotonic 2).cdf u)) := by
  apply Verification.copula_limit_comonotonic_of_powerDiagonal
    (fun i => Verification.huslerReissPositive (δ i) (hδ i))
    (fun i => 2*ProbabilityTheory.cdf (gaussianReal 0 1) (1/δ i))
    (fun i => by simpa only [huslerReiss_extremalCoefficient] using
      (Verification.huslerReissPositive_isExtremeValue (δ i) (hδ i)).hasPowerDiagonal) _ u
  have h := (continuous_standardNormalCDF.continuousAt.tendsto.comp
    (tendsto_inv_atTop_zero.comp hd)).const_mul 2
  simpa [Function.comp_def,one_div,Verification.standardGaussian_cdf_zero] using h

private theorem hr_argument_limit {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l (nhds 0)) (a : ℝ) :
    Tendsto (fun i => 1/δ i+δ i/2*a) l atTop := by
  have hd' : Tendsto δ l (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hd,Eventually.of_forall hδ⟩
  have hi := tendsto_inv_nhdsGT_zero.comp hd'
  have hz := (hd.div_const 2).mul_const a
  simpa only [one_div,Function.comp_def] using hi.atTop_add hz

theorem huslerReiss_limit_independence_interior {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l (nhds 0))
    (u v : I) (hu : (u:ℝ)∈Ioo (0:ℝ) 1) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    Tendsto (fun i => (Verification.huslerReissPositive (δ i) (hδ i)).cdf ![u,v]) l
      (nhds ((u:ℝ)*(v:ℝ))) := by
  have h₁ := (ProbabilityTheory.tendsto_cdf_atTop (gaussianReal 0 1)).comp
    (hr_argument_limit δ hδ hd (Real.log ((-Real.log (u:ℝ))/(-Real.log (v:ℝ)))))
  have h₂ := (ProbabilityTheory.tendsto_cdf_atTop (gaussianReal 0 1)).comp
    (hr_argument_limit δ hδ hd (Real.log ((-Real.log (v:ℝ))/(-Real.log (u:ℝ)))))
  have h := Real.continuous_exp.continuousAt.tendsto.comp
    (((h₁.const_mul (-Real.log (u:ℝ))).add (h₂.const_mul (-Real.log (v:ℝ)))).neg)
  simp only [huslerReiss_cdf_interior _ _ u v hu hv]
  simpa only [Function.comp_def,mul_one,one_mul,neg_add_rev,neg_neg,Real.exp_add,
    Real.exp_log hu.1,Real.exp_log hv.1,mul_comm] using h

theorem huslerReiss_limit_independence {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l (nhds 0)) (u : Fin 2→I) :
    Tendsto (fun i => (Verification.huslerReissPositive (δ i) (hδ i)).cdf u) l
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
  have h := huslerReiss_limit_independence_interior δ hδ hd (u 0) (u 1) hi0 hi1
  rw [← hu] at h
  simpa only [cdf_independence,Fin.prod_univ_two] using h

theorem huslerReiss_limit_comonotonic_uniform {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l atTop) :
    TendstoUniformly (fun i => (Verification.huslerReissPositive (δ i) (hδ i)).cdf) (comonotonic 2).cdf l :=
  Verification.copula_cdf_uniform_limit_of_pointwise _ _ (huslerReiss_limit_comonotonic δ hδ hd)

theorem huslerReiss_limit_independence_uniform {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l (nhds 0)) :
    TendstoUniformly (fun i => (Verification.huslerReissPositive (δ i) (hδ i)).cdf) (independence 2).cdf l :=
  Verification.copula_cdf_uniform_limit_of_pointwise _ _ (huslerReiss_limit_independence δ hδ hd)

end Papers.AnsariRockel2024
