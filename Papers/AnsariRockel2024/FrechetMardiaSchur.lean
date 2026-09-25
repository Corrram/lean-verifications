import Verification.FrechetSchur

/-! # Table 5 / Appendix A.4.2: Schur order of the Fréchet and Mardia families -/

open ProbabilityTheory Copula

namespace Papers.AnsariRockel2024

/-- Table 5 (`*` cell): Mardia increases in both-direction Schur order on `0≤θ≤1`. -/
theorem mardia_schur_nonnegative {θ η : ℝ} (hθ : 0 ≤ θ) (hθη : θ ≤ η) (hη : η ≤ 1) :
    (mardia θ (abs_le.mpr ⟨by linarith, by linarith⟩)).SchurBothLE
      (mardia η (abs_le.mpr ⟨by linarith, hη⟩)) :=
  Verification.FrechetSchur.mardia_schur_nonnegative hθ hθη hη

/-- Table 5 (`*` cell): Mardia decreases in both-direction Schur order on `-1≤θ≤0`. -/
theorem mardia_schur_nonpositive {θ η : ℝ} (hθ : -1 ≤ θ) (hθη : θ ≤ η) (hη : η ≤ 0) :
    (mardia η (abs_le.mpr ⟨by linarith, by linarith⟩)).SchurBothLE
      (mardia θ (abs_le.mpr ⟨hθ, by linarith⟩)) :=
  Verification.FrechetSchur.mardia_schur_nonpositive hθ hθη hη

/-- Table 5: on the unmixed axis `β=0`, Fréchet Schur order increases with the `M` weight. -/
theorem frechet_schur_mono_M {a a' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (ha' : a' ≤ 1) :
    (frechet a 0 ha le_rfl (by linarith)).SchurBothLE
      (frechet a' 0 (ha.trans haa) le_rfl (by linarith)) :=
  Verification.FrechetSchur.frechet_schur_mono_first ha haa ha'

/-- Table 5: on the unmixed axis `α=0`, Fréchet Schur order increases with the `W` weight. -/
theorem frechet_schur_mono_W {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') (hb' : b' ≤ 1) :
    (frechet 0 b le_rfl hb (by linarith)).SchurBothLE
      (frechet 0 b' le_rfl (hb.trans hbb) (by linarith)) :=
  Verification.FrechetSchur.frechet_schur_mono_second hb hbb hb'

end Papers.AnsariRockel2024
