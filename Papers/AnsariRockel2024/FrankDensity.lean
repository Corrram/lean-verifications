import Verification.FrankDensity

/-! # Table 3: Frank density TP2 on the full real parameter range -/

open ProbabilityTheory MeasureTheory

namespace Papers.AnsariRockel2024

noncomputable def frankSigned (θ : ℝ) : Copula 2 :=
  if hp : 0 < θ then Copula.frank θ hp
  else if hn : θ < 0 then Copula.frankNegative θ hn
  else Copula.independence 2

theorem frank_positive_density (θ : ℝ) (hθ : 0 < θ) :
    (Copula.frank θ hθ).toMeasure =
      (volume : Measure (Fin 2 → unitInterval)).withDensity
        (fun x => ENNReal.ofReal (Verification.frankDensity θ x)) :=
  Verification.frank_toMeasure_density hθ

theorem frank_positive_density_tp2 (θ : ℝ) (hθ : 0 < θ) :
    (Copula.frank θ hθ).HasMTP2Density :=
  Verification.frank_hasMTP2Density hθ

theorem frank_density_tp2_iff (θ : ℝ) : (frankSigned θ).HasMTP2Density ↔ 0 ≤ θ := by
  unfold frankSigned
  split_ifs with hp hn
  · exact iff_of_true (frank_positive_density_tp2 θ hp) hp.le
  · exact iff_of_false (Verification.frank_negative_not_density_tp2 θ hn) (not_le.mpr hn)
  · exact iff_of_true (Copula.hasMTP2Density_independence 2) (le_of_not_gt hn)

theorem frank_ci_iff (θ : ℝ) : (frankSigned θ).IsCI ↔ 0 ≤ θ := by
  unfold frankSigned
  split_ifs with hp hn
  · exact iff_of_true (Verification.frank_positive_isCI θ hp) hp.le
  · exact iff_of_false (Verification.frank_negative_not_ci θ hn) (not_le.mpr hn)
  · exact iff_of_true Copula.isCI_independence (le_of_not_gt hn)

theorem frank_cd_iff (θ : ℝ) : (frankSigned θ).IsCD ↔ θ ≤ 0 := by
  unfold frankSigned
  split_ifs with hp hn
  · exact iff_of_false (Verification.frank_positive_not_cd θ hp) (not_le.mpr hp)
  · exact iff_of_true (Verification.frank_negative_isCD θ hn) hn.le
  · exact iff_of_true Copula.isCD_independence (le_of_not_gt hp)

end Papers.AnsariRockel2024
