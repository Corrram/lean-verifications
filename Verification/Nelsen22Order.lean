import Verification.Nelsen22Comparison
import Verification.Nelsen22Conditional
import Verification.SchurOrthantEquivalence
import Copula.Order.SymmetricSchur

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

theorem n22Inv_mem {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (u : I) :
    (n22Generator θ hθ hθ1).invFun u ∈ Icc 0 (Real.pi/2) := by
  change Real.arcsin (1-(u:ℝ)^(θ⁻¹)⁻¹) ∈ _
  rw [inv_inv]
  exact ⟨Real.arcsin_nonneg.mpr (sub_nonneg.mpr (Real.rpow_le_one u.property.1 u.property.2 hθ.le)),Real.arcsin_le_pi_div_two _⟩

theorem n22Comparison_inv {θ η : ℝ} (hθ : 0 < θ) (hθη : θ ≤ η) (hη1 : η ≤ 1) (u : I) :
    n22Comparison (η/θ) ((n22Generator θ hθ (hθη.trans hη1)).invFun u) =
      (n22Generator η (hθ.trans_le hθη) hη1).invFun u := by
  change n22Comparison (η/θ) (Real.arcsin (1-(u:ℝ)^(θ⁻¹)⁻¹)) = Real.arcsin (1-(u:ℝ)^(η⁻¹)⁻¹)
  simp only [inv_inv,n22Comparison]
  rw [Real.sin_arcsin (by linarith [Real.rpow_le_one u.property.1 u.property.2 hθ.le])
    (by linarith [Real.rpow_nonneg u.property.1 θ]),sub_sub_cancel,← Real.rpow_mul u.property.1]
  congr 2
  field_simp

theorem n22Comparison_psi {θ η t : ℝ} (hθ : 0 < θ) (hθη : θ ≤ η) (hη1 : η ≤ 1)
    (ht : t ∈ Icc 0 (Real.pi/2)) :
    (n22Generator η (hθ.trans_le hθη) hη1).toFun (n22Comparison (η/θ) t) =
      (n22Generator θ hθ (hθη.trans hη1)).toFun t := by
  have hη := hθ.trans_le hθη
  have hr : 0 < η/θ := div_pos hη hθ
  have hb : 1-Real.sin t ∈ Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr (Real.sin_le_one _),by
    linarith [Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2,Real.pi_pos])]⟩
  have hpow := Real.rpow_le_one hb.1 hb.2 hr.le
  have hn := Real.rpow_nonneg hb.1 (η/θ)
  change (n22Base (n22Comparison (η/θ) t))^η⁻¹ = (n22Base t)^θ⁻¹
  rw [n22Base,n22Base,n22Comparison,min_eq_left (Real.arcsin_le_pi_div_two _),min_eq_left ht.2,
    Real.sin_arcsin (by linarith) (by linarith),sub_sub_cancel,← Real.rpow_mul hb.1]
  congr 1
  field_simp

theorem n22Psi_zero {θ t : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ht : Real.pi/2 ≤ t) :
    (n22Generator θ hθ hθ1).toFun t = 0 := by
  change (n22Base t)^θ⁻¹ = 0
  simp [n22Base,min_eq_right ht,Real.zero_rpow (inv_ne_zero hθ.ne')]

theorem nelsen22_lowerOrthant_positive {θ η : ℝ} (hθ : 0 < θ) (hθη : θ ≤ η) (hη1 : η ≤ 1) :
    (nelsen22 η ⟨(hθ.trans_le hθη).le,hη1⟩).LowerOrthantLE (nelsen22 θ ⟨hθ.le,hθη.trans hη1⟩) := by
  have hη := hθ.trans_le hθη
  have hr : 1 ≤ η/θ := (one_le_div hθ).mpr hθη
  intro x
  simp only [nelsen22,hθ.ne',hη.ne',dite_false,BivariateGenerator.cdf_copula,BivariateGenerator.cdf]
  split_ifs with hz
  · exact le_rfl
  have hu : x 0 ≠ 0 := (not_or.mp hz).1
  have hv : x 1 ≠ 0 := (not_or.mp hz).2
  let s := (n22Generator θ hθ (hθη.trans hη1)).invFun (x 0)
  let t := (n22Generator θ hθ (hθη.trans hη1)).invFun (x 1)
  have hs := n22Inv_mem hθ (hθη.trans hη1) (x 0)
  have ht := n22Inv_mem hθ (hθη.trans hη1) (x 1)
  by_cases hsum : s+t ≤ Real.pi/2
  · have hh := n22Comparison_subadd hr hs.1 ht.1 hsum
    change n22Comparison (η/θ) (s+t) ≤ n22Comparison (η/θ) s+n22Comparison (η/θ) t at hh
    rw [n22Comparison_inv hθ hθη hη1,n22Comparison_inv hθ hθη hη1] at hh
    have hn : 0 ≤ n22Comparison (η/θ) (s+t) :=
      (add_nonneg hs.1 ht.1).trans (n22Comparison_ge hr ⟨add_nonneg hs.1 ht.1,hsum⟩)
    have hm := (n22Generator η hη hη1).antitone hn (hn.trans hh) hh
    rw [n22Comparison_psi hθ hθη hη1 ⟨add_nonneg hs.1 ht.1,hsum⟩] at hm
    exact hm
  · have hge := add_le_add (n22Comparison_ge hr hs) (n22Comparison_ge hr ht)
    rw [n22Comparison_inv hθ hθη hη1,n22Comparison_inv hθ hθη hη1] at hge
    have hb : Real.pi/2 ≤ (n22Generator η hη hη1).invFun (x 0)+(n22Generator η hη hη1).invFun (x 1) :=
      (lt_of_not_ge hsum).le.trans hge
    rw [n22Psi_zero hη hη1 hb]
    exact (n22Generator θ hθ (hθη.trans hη1)).nonneg _ (add_nonneg hs.1 ht.1)

theorem nelsen22_lowerOrthant_antitone {θ η : ℝ} (hθ : θ ∈ Icc 0 1) (hη : η ∈ Icc 0 1)
    (hθη : θ ≤ η) : (nelsen22 η hη).LowerOrthantLE (nelsen22 θ hθ) := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen22_zero]
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx,cdf_independence]
    simpa using (nelsen22_isCD η hη).isNQD (x 0) (x 1)
  · exact nelsen22_lowerOrthant_positive (lt_of_le_of_ne hθ.1 (Ne.symm hz)) hθη hη.2

theorem nelsen22_schur_monotone {θ η : ℝ} (hθ : θ ∈ Icc 0 1) (hη : η ∈ Icc 0 1)
    (hθη : θ ≤ η) : (nelsen22 θ hθ).SchurBothLE (nelsen22 η hη) := by
  have ho := nelsen22_lowerOrthant_antitone hθ hη hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSD _ _ (nelsen22_isCD θ hθ).1 (nelsen22_isCD η hη).1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSD _ _ (nelsen22_isCD θ hθ).2 (nelsen22_isCD η hη).2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx,cdf_transpose,cdf_transpose]
    exact ho ![x 1,x 0]

end Verification
