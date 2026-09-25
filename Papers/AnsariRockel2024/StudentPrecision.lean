import Verification.GammaPrecisionConcentration

open ProbabilityTheory MeasureTheory Real Set Filter Verification
open scoped Topology

namespace Papers.AnsariRockel2024

theorem student_precision_centered_second_moment (ν : ℝ) (hν : 0<ν) :
    Integrable (fun t : ℝ => (t-1)^2) (gammaMeasure (ν/2) (ν/2)) ∧
      (∫ t : ℝ, (t-1)^2 ∂gammaMeasure (ν/2) (ν/2))=2/ν := by
  simpa only [inv_div,one_div] using gammaPrecision_centered_second_moment (show 0<ν/2 by positivity)

theorem student_precision_concentration_bound (ν : ℝ) (hν : 0<ν) {ε : ℝ} (hε : 0<ε) :
    (gammaMeasure (ν/2) (ν/2)).real {t | ε≤|t-1|}≤2/(ν*ε^2) := by
  have h := gammaPrecision_concentration_bound (show 0<ν/2 by positivity) hε
  simpa only [inv_div,one_div,div_div] using h

/-- Concentration of the actual Student gamma precision; the copula limit requires
additional marginal and joint CDF arguments. -/
theorem student_precision_concentrates {ι : Type*} {l : Filter ι}
    (ν : ι→ℝ) (hν : ∀ i,0<ν i) (ht : Tendsto ν l atTop) {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun i => (gammaMeasure (ν i/2) (ν i/2)).real {t | ε≤|t-1|}) l (nhds 0) :=
  gammaPrecision_concentrates (fun i => ν i/2) (fun i => div_pos (hν i) (by norm_num))
    (ht.atTop_div_const (by norm_num)) hε

end Papers.AnsariRockel2024
