import Papers.AnsariRockel2024.JoeExtremeValue
import Papers.AnsariRockel2024.GalambosOrders
import Papers.AnsariRockel2024.GalambosLimits
import Copula.Families.MarshallOlkin

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem joeExtremeValue_lowerOrthant_mono (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε)
    (hδε : δ≤ε) (α β : I) :
    (Verification.joeExtremeValue δ hδ α β).LowerOrthantLE
      (Verification.joeExtremeValue ε hε α β) := by
  intro u
  unfold Verification.joeExtremeValue
  rw [cdf_maxProduct,cdf_maxProduct]
  exact mul_le_mul_of_nonneg_right (galambos_lowerOrthant_mono δ ε hδ hε hδε _)
    ((independence 2).cdf_nonneg _)

theorem joeExtremeValue_schurBoth_mono (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε)
    (hδε : δ≤ε) (α β : I) :
    (Verification.joeExtremeValue δ hδ α β).SchurBothLE
      (Verification.joeExtremeValue ε hε α β) := by
  apply (extremeValue_schur_iff_pickands_of_ci _ _ (joeExtremeValue_isExtremeValue δ hδ α β)
    (joeExtremeValue_isExtremeValue ε hε α β) (joeExtremeValue_isCI δ hδ α β)
    (joeExtremeValue_isCI ε hε α β)).mpr
  exact (extremeValue_pickands_order _ _ (joeExtremeValue_isExtremeValue δ hδ α β)
    (joeExtremeValue_isExtremeValue ε hε α β)).mp
    (joeExtremeValue_lowerOrthant_mono δ ε hδ hε hδε α β)

theorem joeExtremeValue_limit_marshallOlkin {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l atTop) (α β : I) (u : Fin 2→I) :
    Tendsto (fun i => (Verification.joeExtremeValue (δ i) (hδ i) α β).cdf u) l
      (nhds ((marshallOlkin α β).cdf u)) := by
  let a : Fin 2→I := ![α,β]
  have h := (galambos_limit_comonotonic δ hδ hd
    (fun j => unitPower (u j) (a j) (a j).property.1)).mul_const
    ((independence 2).cdf (fun j => unitPower (u j) (unitInterval.symm (a j)) (unitInterval.symm (a j)).property.1))
  simpa only [Verification.joeExtremeValue,marshallOlkin,commonShock,cdf_maxProduct,a] using h

private theorem maxProduct_independence (d : ℕ) (a : Fin d→I) :
    maxProduct (independence d) (independence d) a=independence d := by
  apply ext_cdf
  intro u
  rw [cdf_maxProduct,cdf_independence,cdf_independence,cdf_independence,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [coe_unitPower,unitInterval.coe_symm_eq]
  by_cases hu : (u j:ℝ)=0
  · by_cases ha : (a j:ℝ)=0
    · simp [hu,ha]
    · simp [hu,Real.zero_rpow ha]
  · rw [← Real.rpow_add (lt_of_le_of_ne (u j).property.1 (Ne.symm hu)),add_sub_cancel,Real.rpow_one]

theorem joeExtremeValue_limit_independence {ι : Type*} {l : Filter ι}
    (δ : ι→ℝ) (hδ : ∀ i,0<δ i) (hd : Tendsto δ l (nhds 0)) (α β : I) (u : Fin 2→I) :
    Tendsto (fun i => (Verification.joeExtremeValue (δ i) (hδ i) α β).cdf u) l
      (nhds ((independence 2).cdf u)) := by
  let a : Fin 2→I := ![α,β]
  have h := (galambos_limit_independence δ hδ hd
    (fun j => unitPower (u j) (a j) (a j).property.1)).mul_const
    ((independence 2).cdf (fun j => unitPower (u j) (unitInterval.symm (a j)) (unitInterval.symm (a j)).property.1))
  have he := congrArg (fun C : Copula 2 => C.cdf u) (maxProduct_independence 2 a)
  rw [cdf_maxProduct] at he
  rw [he] at h
  simpa only [Verification.joeExtremeValue,cdf_maxProduct,a] using h

end Papers.AnsariRockel2024
