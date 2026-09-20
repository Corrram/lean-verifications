import Papers.OrendayLaresRockel2026XiBeta.LeftBoundary
import Copula.Dependence.ConditionalMonotonicity
import Copula.Dependence.Rank
import Copula.Symmetry
import Copula.Rectangle

/-! # Reflection, radial symmetry, and dependence of the tent family -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

theorem tentDisplacement_symm (b : ℝ) (hb : b ∈ Icc (-1) 1) (v : I) :
    tentDisplacement b hb (unitInterval.symm v) = tentDisplacement b hb v := by
  have he : 1 - (v : ℝ) - 1 / 2 = -((v : ℝ) - 1 / 2) := by ring
  simp only [tentDisplacement, medianTent, unitInterval.coe_symm_eq, he, abs_neg]

theorem tentDisplacement_neg (b : ℝ) (hb : b ∈ Icc (-1) 1)
    (hnb : -b ∈ Icc (-1) 1) (v : I) :
    tentDisplacement (-b) hnb v = -tentDisplacement b hb v := by
  rcases lt_trichotomy b 0 with h | h | h
  · simp [tentDisplacement, not_le.mpr h, neg_nonneg.mpr h.le]
  · subst b
    simp [tentDisplacement, medianTent]
  · simp [tentDisplacement, h.le, not_le.mpr (neg_neg_of_pos h)]

theorem medianWedge_symm (u : I) : medianWedge (unitInterval.symm u) = medianWedge u := by
  simp [medianWedge, unitInterval.coe_symm_eq, min_comm]

theorem leftBoundary_reflect_second (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).reflect {1} =
      leftBoundary (-b) (by constructor <;> linarith [hb.1, hb.2]) := by
  apply Copula.ext_cdf_two
  intro u v
  rw [Copula.cdf_reflect_second]
  simp only [leftBoundary, cdf_twoStrip, tentDisplacement_symm,
    unitInterval.coe_symm_eq]
  erw [tentDisplacement_neg b hb (by constructor <;> linarith [hb.1, hb.2]) v]
  ring

theorem leftBoundary_reflect_first (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).reflect {0} =
      leftBoundary (-b) (by constructor <;> linarith [hb.1, hb.2]) := by
  apply Copula.ext_cdf_two
  intro u v
  rw [Copula.cdf_reflect_first]
  simp only [leftBoundary, cdf_twoStrip, medianWedge_symm,
    unitInterval.coe_symm_eq]
  erw [tentDisplacement_neg b hb (by constructor <;> linarith [hb.1, hb.2]) v]
  ring

theorem leftBoundary_radiallySymmetric (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).IsRadiallySymmetric := by
  apply (Copula.isRadiallySymmetric_iff _).mpr
  intro u v
  simp only [leftBoundary, cdf_twoStrip, medianWedge_symm, tentDisplacement_symm,
    unitInterval.coe_symm_eq]
  ring

theorem leftBoundary_zero (h0 : (0 : ℝ) ∈ Icc (-1) 1) :
    leftBoundary 0 h0 = Copula.independence 2 := by
  apply ((leftBoundary 0 h0).chatterjeeXi_eq_zero_iff).mp
  rw [leftBoundary_xi]
  norm_num

theorem leftBoundary_isSI (b : ℝ) (hb : b ∈ Icc (-1) 1) (hpos : 0 ≤ b) :
    (leftBoundary b hb).IsSI := by
  intro a c d v hac hcd
  have hn : 0 ≤ tentDisplacement b hb v := by
    change 0 ≤ if 0 ≤ b then medianTent b v else -medianTent (-b) v
    rw [ite_eq_left hpos]
    exact le_max_left _ _
  have hanti : Antitone (stripKernel (tentDisplacement b hb) v) := by
    intro u w huw
    by_cases hu : u ≤ Copula.unitHalf
    · by_cases hw : w ≤ Copula.unitHalf
      · simp [stripKernel, hu, hw]
      · simp only [stripKernel, ite_eq_left hu, ite_eq_right hw]
        linarith
    · have hw : ¬w ≤ Copula.unitHalf := fun hw => hu (huw.trans hw)
      simp [stripKernel, hu, hw]
  simpa only [integral_stripKernel_Iic, leftBoundary] using
    Copula.integral_Iic_concave_of_antitone (stripKernel_integrable _ v) hanti a c d hac hcd

theorem leftBoundary_isSD (b : ℝ) (hb : b ∈ Icc (-1) 1) (hneg : b ≤ 0) :
    (leftBoundary b hb).IsSD := by
  apply (Copula.isSI_reflect_second_iff _).mp
  rw [leftBoundary_reflect_second]
  exact leftBoundary_isSI _ _ (neg_nonneg.mpr hneg)

theorem leftBoundary_pqd_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).IsPQD ↔ 0 ≤ b := by
  constructor
  · intro h
    simpa only [leftBoundary_beta] using h.blomqvistBeta_nonneg
  · exact fun h => (leftBoundary_isSI b hb h).isPQD

theorem leftBoundary_nqd_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).IsNQD ↔ b ≤ 0 := by
  constructor
  · intro h
    have hm := h Copula.unitHalf Copula.unitHalf
    have hβ := leftBoundary_beta b hb
    unfold Copula.blomqvistBeta at hβ
    change (leftBoundary b hb).cdf ![Copula.unitHalf, Copula.unitHalf] ≤
      (1 / 2 : ℝ) * (1 / 2) at hm
    linarith
  · exact fun h => (leftBoundary_isSD b hb h).isNQD

theorem leftBoundary_si_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).IsSI ↔ 0 ≤ b :=
  ⟨fun h => (leftBoundary_pqd_iff b hb).mp h.isPQD, leftBoundary_isSI b hb⟩

theorem leftBoundary_sd_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).IsSD ↔ b ≤ 0 :=
  ⟨fun h => (leftBoundary_nqd_iff b hb).mp h.isNQD, leftBoundary_isSD b hb⟩

/-- Proposition 2, equation (8), as an almost-everywhere conditional-CDF identity. -/
theorem leftBoundary_conditionalCDF (b : ℝ) (hb : b ∈ Icc (-1) 1) (v : I) :
    (fun u => (leftBoundary b hb).conditionalCDF u v) =ᵐ[volume]
      (fun u => if u ≤ Copula.unitHalf then (v : ℝ) + tentDisplacement b hb v
        else (v : ℝ) - tentDisplacement b hb v) :=
  conditionalCDF_twoStrip (tentDisplacement b hb) v

/-- A median quadrant, with `true` selecting the upper half in that coordinate.
The half-open convention has no effect on mass because the marginals are uniform. -/
def medianQuadrant (p q : Bool) : Set (Fin 2 → I) :=
  Set.pi univ (fun i => Ioc
    (![if p then Copula.unitHalf else 0, if q then Copula.unitHalf else 0] i)
    (![if p then 1 else Copula.unitHalf, if q then 1 else Copula.unitHalf] i))

/-- Proposition 3(ii): all four median quadrant masses. -/
theorem leftBoundary_quadrant_masses (b : ℝ) (hb : b ∈ Icc (-1) 1) (p q : Bool) :
    (leftBoundary b hb).toMeasure.real (medianQuadrant p q) =
      if p = q then (1 + b) / 4 else (1 - b) / 4 := by
  have hm : (leftBoundary b hb).cdf ![Copula.unitHalf, Copula.unitHalf] = (1 + b) / 4 := by
    have h := leftBoundary_beta b hb
    unfold Copula.blomqvistBeta at h
    linarith
  have hz (v : I) : (leftBoundary b hb).cdf ![v, 0] = 0 :=
    Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 rfl
  unfold medianQuadrant
  rw [Copula.measureReal_rectangle_two _ _ _ (by
    intro i
    fin_cases i <;> cases p <;> cases q <;> norm_num [Copula.unitHalf] <;> exact unitInterval.le_one _)]
  cases p <;> cases q <;> simp [hm, hz] <;> norm_num [Copula.unitHalf] <;> ring

end Papers.OrendayLaresRockel2026XiBeta
