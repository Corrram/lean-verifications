import Verification.GaussianWedge
import Mathlib.Probability.Distributions.Gaussian.Real

open ProbabilityTheory MeasureTheory Real Set

namespace Verification

noncomputable def positivePower (ν z : ℝ) : ℝ := (max z 0)^ν

theorem positivePower_nonneg (ν z : ℝ) : 0≤positivePower ν z :=
  Real.rpow_nonneg (le_max_right _ _) _

theorem positivePower_continuous (ν : ℝ) (hν : 0<ν) : Continuous (positivePower ν) := by
  unfold positivePower
  exact (continuous_id.max continuous_const).rpow_const (fun _ => Or.inr hν.le)

theorem positivePower_integrable (ν : ℝ) (hν : 0<ν) :
    Integrable (positivePower ν) (gaussianReal 0 1) := by
  have hi : Integrable (fun z : ℝ => |z|^ν) (gaussianReal 0 1) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := 1) ⟨ν,hν.le⟩).integrable_norm_rpow'
    convert h using 1
    simp only [id_eq,Real.norm_eq_abs]
    rfl
  apply hi.mono' (positivePower_continuous ν hν).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (positivePower_nonneg ν z)]
  exact Real.rpow_le_rpow (le_max_right _ _) (max_le (le_abs_self _) (abs_nonneg _)) hν.le

noncomputable def gaussianPositiveMoment (ν : ℝ) : ℝ :=
  ∫ z,positivePower ν z ∂gaussianReal 0 1

theorem gaussianPositiveMoment_pos (ν : ℝ) (hν : 0<ν) : 0<gaussianPositiveMoment ν := by
  apply (integral_pos_iff_support_of_nonneg (positivePower_nonneg ν) (positivePower_integrable ν hν)).mpr
  have hs : Ioi (0:ℝ)⊆Function.support (positivePower ν) := by
    intro z hz
    exact (Real.rpow_pos_of_pos (lt_of_lt_of_le hz (le_max_left _ _)) ν).ne'
  have hm : 0<(gaussianReal 0 1) (Ioi (0:ℝ)) := by
    have he : (gaussianReal 0 1).real (Ioi (0:ℝ))=1/2 := by
      rw [← compl_Iic,measureReal_compl measurableSet_Iic,probReal_univ,
        ← ProbabilityTheory.cdf_eq_real,standardGaussian_cdf_zero]
      norm_num
    by_contra h
    have hz : (gaussianReal 0 1) (Ioi (0:ℝ))=0 := le_antisymm (le_of_not_gt h) zero_le
    simp only [Measure.real,hz,ENNReal.toReal_zero] at he
    norm_num at he
  exact hm.trans_le (measure_mono hs)

noncomputable def gaussianPositiveWeight (ν z : ℝ) : ℝ := positivePower ν z/gaussianPositiveMoment ν

theorem gaussianPositiveWeight_integrable (ν : ℝ) (hν : 0<ν) :
    Integrable (gaussianPositiveWeight ν) (gaussianReal 0 1) :=
  (positivePower_integrable ν hν).div_const _

theorem gaussianPositiveWeight_nonneg (ν : ℝ) (hν : 0<ν) (z : ℝ) :
    0≤gaussianPositiveWeight ν z :=
  div_nonneg (positivePower_nonneg ν z) (gaussianPositiveMoment_pos ν hν).le

theorem gaussianPositiveWeight_mean (ν : ℝ) (hν : 0<ν) :
    ∫ z,gaussianPositiveWeight ν z ∂gaussianReal 0 1=1 := by
  unfold gaussianPositiveWeight
  rw [integral_div]
  exact div_self (gaussianPositiveMoment_pos ν hν).ne'

end Verification
