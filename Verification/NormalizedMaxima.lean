import Copula.Transform.MaxProduct
import Verification.CopulaWeakCompactness

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def maximaWeight (n : ℕ) : I :=
  ⟨((n:ℝ)+1)/((n:ℝ)+2),by positivity,
    (div_le_one (by positivity)).mpr (by linarith)⟩

/-- The normalized maximum of `n+1` independent copies of a copula. -/
noncomputable def normalizedMaxima {d : ℕ} (C : Copula d) : ℕ→Copula d
  | 0 => C
  | n+1 => maxProduct (normalizedMaxima C n) C (fun _ => maximaWeight n)

theorem normalizedMaxima_cdf {d : ℕ} (C : Copula d) (n : ℕ) (u : Fin d→I) :
    (normalizedMaxima C n).cdf u=
      (C.cdf (fun i => unitPower (u i) (((n:ℝ)+1)⁻¹) (by positivity)))^(n+1) := by
  induction n generalizing u with
  | zero => simp [normalizedMaxima]
  | succ n ih =>
    rw [normalizedMaxima,cdf_maxProduct,ih]
    have h₁ : (fun i => unitPower (unitPower (u i) (maximaWeight n) (maximaWeight n).property.1)
        (((n:ℝ)+1)⁻¹) (by positivity))=
        fun i => unitPower (u i) (((n:ℝ)+2)⁻¹) (by positivity) := by
      funext i
      rw [unitPower_mul]
      congr 1
      change (((n:ℝ)+1)/((n:ℝ)+2))*((n:ℝ)+1)⁻¹=((n:ℝ)+2)⁻¹
      field_simp
    have h₂ : (fun i => unitPower (u i) (unitInterval.symm (maximaWeight n))
        (unitInterval.symm (maximaWeight n)).property.1)=
        fun i => unitPower (u i) (((n:ℝ)+2)⁻¹) (by positivity) := by
      funext i
      congr 1
      change 1-(((n:ℝ)+1)/((n:ℝ)+2))=((n:ℝ)+2)⁻¹
      field_simp
      ring
    rw [h₁,h₂,← pow_succ]
    simp only [Nat.cast_add,Nat.cast_one,show (n:ℝ)+1+1=(n:ℝ)+2 by ring]

theorem exists_copula_of_pointwise_cdf_limit (C : ℕ→Copula 2)
    (F : (Fin 2→I)→ℝ)
    (hF : ∀ u,Tendsto (fun n => (C n).cdf u) atTop (nhds (F u))) :
    ∃ D : Copula 2, D.cdf=F := by
  obtain ⟨D,φ,hφ,_,hlim⟩ := exists_copula_subsequence C
  refine ⟨D,funext fun u => ?_⟩
  have he : u=![u 0,u 1] := by ext i; fin_cases i <;> rfl
  have h := hlim (u 0) (u 1)
  rw [← he] at h
  exact tendsto_nhds_unique h ((hF u).comp hφ.tendsto_atTop)

end Verification
