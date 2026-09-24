import Verification.Plackett
import Verification.InteriorDensity

open ProbabilityTheory MeasureTheory Set
open scoped unitInterval

namespace Verification

theorem plackett_toMeasure_density {θ : ℝ} (hθ : 0 < θ) (hne : θ ≠ 1) :
    (plackett θ hθ).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (plackettDensity θ (x 0) (x 1))) := by
  apply copula_density_of_interior_derivatives (plackett θ hθ)
    (plackettDensity θ) (plackettF θ) (plackettP θ)
  · intro u v; exact plackettDensity_nonneg hθ u.property v.property
  · intro u v hu hv
    have hn := (Real.sqrt_pos.mpr (plackettD_pos hθ ⟨hu.1.le,hu.2.le⟩ ⟨hv.1.le,hv.2.le⟩)).ne'
    unfold plackettDensity
    apply ContinuousAt.div
    · fun_prop
    · unfold plackettD plackettA; fun_prop
    · exact pow_ne_zero 3 hn
  · intro u v hu hv
    have hn := (Real.sqrt_pos.mpr (plackettD_pos hθ ⟨hu.1.le,hu.2.le⟩ ⟨hv.1.le,hv.2.le⟩)).ne'
    unfold plackettP
    apply ContinuousAt.div_const
    apply ContinuousAt.sub continuousAt_const
    apply ContinuousAt.div
    · unfold plackettA; fun_prop
    · unfold plackettD plackettA; fun_prop
    · exact hn
  · intro u v hu hv
    exact plackettF_deriv hne (plackettD_pos hθ ⟨hu.1.le,hu.2.le⟩ ⟨hv.1.le,hv.2.le⟩)
  · intro u v hu hv
    exact plackettP_deriv (plackettD_pos hθ ⟨hu.1.le,hu.2.le⟩ ⟨hv.1.le,hv.2.le⟩)
  · intro u v _ _ _ _
    exact (plackett_cdf hθ hne u v).symm

end Verification
