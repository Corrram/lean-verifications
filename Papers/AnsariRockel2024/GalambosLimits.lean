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

end Papers.AnsariRockel2024
