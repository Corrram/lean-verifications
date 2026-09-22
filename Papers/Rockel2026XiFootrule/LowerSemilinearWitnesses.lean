import Verification.LowerSemilinear
import Papers.Rockel2026XiFootrule.SIRegion

/-! # Convexity and boundary witnesses for the lower semilinear class -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

/-- The standard lower semilinear class is closed under copula mixtures. -/
theorem IsLowerSemilinear.mix {C E : Copula 2}
    (hC : IsLowerSemilinear C) (hE : IsLowerSemilinear E) (a : I) :
    IsLowerSemilinear (C.mix E a) := by
  obtain ⟨D⟩ := hC
  obtain ⟨F⟩ := hE
  refine ⟨⟨fun t => (a : ℝ)*D.q t+(1-(a : ℝ))*F.q t, ?_, ?_, ?_⟩⟩
  · intro t
    exact add_nonneg (mul_nonneg a.property.1 (D.nonneg t))
      (mul_nonneg (sub_nonneg.mpr a.property.2) (F.nonneg t))
  · intro s hs t ht hst
    dsimp only
    simp only [add_div, mul_div_assoc]
    exact add_le_add (mul_le_mul_of_nonneg_left (D.ratio_antitone hs ht hst) a.property.1)
      (mul_le_mul_of_nonneg_left (F.ratio_antitone hs ht hst) (sub_nonneg.mpr a.property.2))
  · intro u v
    rw [Copula.cdf_mix, D.cdf_eq, F.cdf_eq]
    ring

end Verification

namespace Papers.Rockel2026XiFootrule

open Verification

/-- Every Frechet upper-boundary witness is lower semilinear. -/
theorem upperBoundary_isLowerSemilinear (a : I) : IsLowerSemilinear (upperBoundary a) := by
  refine ⟨⟨fun t => (a : ℝ)+(1-(a : ℝ))*(t : ℝ), ?_, ?_, ?_⟩⟩
  · intro t
    exact add_nonneg a.property.1 (mul_nonneg (sub_nonneg.mpr a.property.2) t.property.1)
  · intro s hs t ht hst
    apply (div_le_div_iff₀ (show (0 : ℝ) < t from ht) (show (0 : ℝ) < s from hs)).mpr
    have h := mul_nonneg a.property.1 (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst))
    nlinarith only [h]
  · intro u v
    rw [cdf_upperBoundary]
    rcases le_total u v with h | h
    · rw [min_eq_left h, max_eq_right h, min_eq_left (show (u : ℝ) ≤ v from h)]
      ring
    · rw [min_eq_right h, max_eq_left h, min_eq_right (show (v : ℝ) ≤ u from h)]
      ring

/-- Every diagonal lower-boundary witness is lower semilinear. -/
theorem diagonalBoundary_isLowerSemilinear (a : I) : IsLowerSemilinear (diagonalBoundary a) := by
  by_cases ha : a = 0
  · subst a
    have he : diagonalBoundary 0 = upperBoundary 1 := by
      simp [diagonalBoundary, upperBoundary]
    rw [he]
    exact upperBoundary_isLowerSemilinear 1
  have ha0 : (0 : ℝ) < a := lt_of_le_of_ne a.property.1 (by
    intro h
    exact ha (Subtype.ext h.symm))
  have han : (a : ℝ) ≠ 0 := ne_of_gt ha0
  refine ⟨⟨fun t => if t ≤ a then (t : ℝ)/a else 1, ?_, ?_, ?_⟩⟩
  · intro t
    split_ifs
    · exact div_nonneg t.property.1 a.property.1
    · exact zero_le_one
  · intro s hs t ht hst
    dsimp only
    have hs0 : (0 : ℝ) < s := hs
    have ht0 : (0 : ℝ) < t := ht
    by_cases hta : t ≤ a
    · rw [ite_eq_left hta, ite_eq_left (hst.trans hta)]
      apply le_of_eq
      field_simp
    · rw [ite_eq_right hta]
      by_cases hsa : s ≤ a
      · rw [ite_eq_left hsa]
        apply (div_le_div_iff₀ ht0 hs0).mpr
        rw [div_mul_eq_mul_div, le_div_iff₀ ha0]
        have h : (s : ℝ)*a ≤ (s : ℝ)*t :=
          mul_le_mul_of_nonneg_left (show (a : ℝ) ≤ t from le_of_not_ge hta) s.property.1
        simpa only [one_mul] using h
      · rw [ite_eq_right hsa]
        exact one_div_le_one_div_of_le hs0 hst
  · intro u v
    rw [diagonalBoundary_cdf]
    by_cases hv : v ≤ a
    · rw [ite_eq_left hv]
      by_cases hu : u ≤ a
      · rw [min_eq_left (show (u : ℝ) ≤ a from hu), ite_eq_left (max_le hu hv)]
        rcases le_total u v with h | h
        · rw [min_eq_left h, max_eq_right h]
          ring
        · rw [min_eq_right h, max_eq_left h]
          ring
      · have hau : a ≤ u := le_of_not_ge hu
        have hvu : v ≤ u := hv.trans hau
        rw [min_eq_right (show (a : ℝ) ≤ u from hau), min_eq_right hvu, max_eq_left hvu,
          ite_eq_right hu, mul_one]
        field_simp
    · rw [ite_eq_right hv, ite_eq_right (fun h => hv ((le_max_right u v).trans h)), mul_one]
      rfl

end Papers.Rockel2026XiFootrule
