import Copula.ExtremeValue.Diagonal

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem copula_limit_comonotonic_of_diagonal {ι : Type*} {l : Filter ι}
    (C : ι→Copula 2)
    (h : ∀ t : I,Tendsto (fun i => (C i).diagonal t) l (nhds (t:ℝ)))
    (u : Fin 2→I) :
    Tendsto (fun i => (C i).cdf u) l (nhds ((comonotonic 2).cdf u)) := by
  have hu : u=![u 0,u 1] := by ext i; fin_cases i <;> rfl
  have he : (comonotonic 2).cdf u=(min (u 0) (u 1):ℝ) := by
    conv_lhs => rw [hu,cdf_comonotonic_two]
    rfl
  rw [he]
  apply (h (min (u 0) (u 1))).squeeze tendsto_const_nhds
  · intro i
    apply (C i).monotone_cdf
    intro j
    fin_cases j
    · exact min_le_left _ _
    · exact min_le_right _ _
  · intro i
    exact le_min ((C i).cdf_le_coord u 0) ((C i).cdf_le_coord u 1)

theorem copula_limit_comonotonic_of_powerDiagonal {ι : Type*} {l : Filter ι}
    (C : ι→Copula 2) (κ : ι→ℝ) (hκ : ∀ i,(C i).HasPowerDiagonal (κ i))
    (hk : Tendsto κ l (nhds 1)) (u : Fin 2→I) :
    Tendsto (fun i => (C i).cdf u) l (nhds ((comonotonic 2).cdf u)) := by
  apply copula_limit_comonotonic_of_diagonal C _ u
  intro t
  have h := (Real.continuousAt_const_rpow' (a := (t:ℝ)) (by norm_num : (1:ℝ)≠0)).tendsto.comp hk
  have he : (fun i => (C i).diagonal t)=fun i => (t:ℝ)^(κ i) := funext fun i => hκ i t
  rw [he]
  simpa only [Function.comp_def,Real.rpow_one] using h

end Verification
