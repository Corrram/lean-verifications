import Papers.AnsariRockel2024.FrankDensity
import Verification.FrankContinuity

/-! # Table 1: the two-sided Frank independence limit -/

open ProbabilityTheory Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem frankSigned_cdf_regular (θ : ℝ) (u v : I) :
    (frankSigned θ).cdf ![u,v] = Verification.frankRegularCDF u v θ := by
  unfold frankSigned
  split_ifs with hp hn
  · exact (Verification.frankRegularCDF_positive θ hp u v).symm
  · exact (Verification.frankRegularCDF_negative θ hn u v).symm
  · have hz : θ = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
    subst θ
    simp [Verification.frankRegularCDF_zero, Copula.cdf_independence, Fin.prod_univ_two]

theorem frank_continuousAt_zero (u : Fin 2 → I) :
    ContinuousAt (fun θ : ℝ => (frankSigned θ).cdf u) 0 := by
  have hx : u = ![u 0,u 1] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [hx]
  simp_rw [frankSigned_cdf_regular]
  exact Verification.continuousAt_frankRegularCDF _ _

theorem frank_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hlim : Tendsto θ l (𝓝 0)) (u : Fin 2 → I) :
    Tendsto (fun z => (frankSigned (θ z)).cdf u) l (𝓝 ((Copula.independence 2).cdf u)) := by
  have hh := (frank_continuousAt_zero u).tendsto.comp hlim
  simpa [frankSigned, Function.comp_def] using hh

end Papers.AnsariRockel2024
