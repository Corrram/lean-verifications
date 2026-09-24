import Verification.Plackett
import Copula.TailDependence.Derivative
import Copula.TailDependence.Examples

open ProbabilityTheory Copula
open scoped unitInterval

namespace Verification

noncomputable def plackettDiag (θ t : ℝ) : ℝ :=
  (1+2*(θ-1)*t-Real.sqrt (1+4*(θ-1)*t*(1-t)))/(2*(θ-1))

theorem plackettDiag_eq {θ : ℝ} (hθ : 0 < θ) (hne : θ ≠ 1) (t : I) :
    plackettDiag θ t = (plackett θ hθ).diagonal t := by
  rw [diagonal,plackett_cdf hθ hne]
  have hd : (1+(θ-1)*((t:ℝ)+(t:ℝ)))^2-4*θ*(θ-1)*(t:ℝ)*(t:ℝ) =
      1+4*(θ-1)*(t:ℝ)*(1-(t:ℝ)) := by ring
  rw [hd]
  unfold plackettDiag
  congr 2
  ring

theorem plackettDiag_deriv {θ t : ℝ} (hne : θ ≠ 1)
    (hD : 0 < 1+4*(θ-1)*t*(1-t)) :
    HasDerivAt (plackettDiag θ)
      (1-(1-2*t)/Real.sqrt (1+4*(θ-1)*t*(1-t))) t := by
  have hd : HasDerivAt (fun x : ℝ => 1+4*(θ-1)*x*(1-x))
      (4*(θ-1)*(1-2*t)) t := by
    convert ((((hasDerivAt_id t).const_mul (4*(θ-1))).mul
      ((hasDerivAt_id t).const_sub 1)).const_add 1) using 1
    · rfl
    · dsimp; ring
  have hh := ((((hasDerivAt_id t).const_mul (2*(θ-1))).const_add 1).sub
    (hd.sqrt hD.ne')).div_const (2*(θ-1))
  convert hh using 1
  · rfl
  · field_simp [sub_ne_zero.mpr hne,(Real.sqrt_pos.mpr hD).ne']
    ring

theorem plackett_tails {θ : ℝ} (hθ : 0 < θ) :
    (plackett θ hθ).HasLowerTailDependence 0 ∧ (plackett θ hθ).HasUpperTailDependence 0 := by
  by_cases he : θ=1
  · subst θ; rw [plackett_one]
    exact ⟨hasLowerTailDependence_independence,hasUpperTailDependence_independence⟩
  have h0 : HasDerivAt (plackettDiag θ) 0 0 := by
    simpa using plackettDiag_deriv (t := 0) he (by norm_num)
  have h1 : HasDerivAt (plackettDiag θ) 2 1 := by
    simpa using plackettDiag_deriv (t := 1) he (by norm_num)
  exact ⟨hasLowerTailDependence_of_hasDerivWithinAt (plackettDiag_eq hθ he) h0.hasDerivWithinAt,
    by simpa using hasUpperTailDependence_of_hasDerivWithinAt (plackettDiag_eq hθ he) h1.hasDerivWithinAt⟩

end Verification
