import Verification.Nelsen14Comparison
import Verification.SchurOrthantEquivalence
import Copula.Order.SymmetricSchur

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n14Inv (θ u : ℝ) : ℝ := (u^(-θ⁻¹)-1)^θ
noncomputable def n14Psi (θ t : ℝ) : ℝ := (1+t^θ⁻¹)^(-θ)

theorem n14Inv_base {θ : ℝ} (hθ : 0 < θ) {u : I} (hu : 0 < (u:ℝ)) :
    0 ≤ (u:ℝ)^(-θ⁻¹)-1 := by
  apply sub_nonneg.mpr
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu u.property.2 (neg_nonpos.mpr (inv_nonneg.mpr hθ.le))

theorem n14Comparison_inv {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) {u : I} (hu : 0 < (u:ℝ)) :
    n14Comparison θ η (n14Inv θ u) = n14Inv η u := by
  unfold n14Comparison n14Inv
  rw [Real.rpow_rpow_inv (n14Inv_base hθ hu) hθ.ne', add_sub_cancel,
    ← Real.rpow_mul hu.le]
  have he : -θ⁻¹*(θ/η) = -η⁻¹ := by field_simp
  rw [he]

theorem n14Comparison_psi {θ η t : ℝ} (hθ : 0 < θ) (hη : 0 < η) (ht : 0 ≤ t) :
    n14Psi η (n14Comparison θ η t) = n14Psi θ t := by
  have hx : 0 ≤ t^θ⁻¹ := Real.rpow_nonneg ht _
  have hB : 0 ≤ (1+t^θ⁻¹)^(θ/η)-1 :=
    sub_nonneg.mpr (Real.one_le_rpow (by linarith) (div_nonneg hθ.le hη.le))
  unfold n14Psi n14Comparison
  rw [Real.rpow_rpow_inv hB hη.ne', add_sub_cancel, ← Real.rpow_mul (by linarith : 0 ≤ 1+t^θ⁻¹)]
  have he : θ/η*(-η) = -θ := by field_simp
  rw [he]

theorem nelsen14_lowerOrthant_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (hθη : θ ≤ η) :
    (nelsen14 θ hθ).LowerOrthantLE (nelsen14 η hη) := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  have hq : 0 < η := lt_of_lt_of_le zero_lt_one hη
  intro x
  by_cases hz : ∀ i, x i ≠ 0
  · have hpos (i : Fin 2) : 0 < (x i:ℝ) := lt_of_le_of_ne (x i).property.1
      (Ne.symm (fun h => hz i (Subtype.ext h)))
    have hn (i : Fin 2) : 0 ≤ n14Inv θ (x i) := Real.rpow_nonneg (n14Inv_base hp (hpos i)) _
    have hh := n14Comparison_superadd hp hq hθη (hn 0) (hn 1)
    rw [n14Comparison_inv hp hq (hpos 0), n14Comparison_inv hp hq (hpos 1)] at hh
    have hnη (i : Fin 2) : 0 ≤ n14Inv η (x i) := Real.rpow_nonneg (n14Inv_base hq (hpos i)) _
    have hpow := Real.rpow_le_rpow (add_nonneg (hnη 0) (hnη 1)) hh (inv_nonneg.mpr hq.le)
    have hbase : 0 < 1+(n14Inv η (x 0)+n14Inv η (x 1))^η⁻¹ := by
      have hn' := Real.rpow_nonneg (add_nonneg (hnη 0) (hnη 1)) η⁻¹
      linarith
    have hi := Real.rpow_le_rpow_of_nonpos hbase (add_le_add (le_refl 1) hpow) (neg_nonpos.mpr hq.le)
    change n14Psi η (n14Comparison θ η (n14Inv θ (x 0)+n14Inv θ (x 1))) ≤
      n14Psi η (n14Inv η (x 0)+n14Inv η (x 1)) at hi
    rw [n14Comparison_psi hp hq (add_nonneg (hn 0) (hn 1))] at hi
    simpa only [cdf_nelsen14 θ hθ x hz, cdf_nelsen14 η hη x hz, n14Psi, n14Inv] using hi
  · push Not at hz
    obtain ⟨i, hi⟩ := hz
    rw [(nelsen14 θ hθ).cdf_eq_zero_of_coord_eq_zero x i hi,
      (nelsen14 η hη).cdf_eq_zero_of_coord_eq_zero x i hi]

theorem nelsen14_schur_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (hθη : θ ≤ η) :
    (nelsen14 θ hθ).SchurBothLE (nelsen14 η hη) := by
  have ho := nelsen14_lowerOrthant_monotone hθ hη hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen14_isCI θ hθ).1 (nelsen14_isCI η hη).1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen14_isCI θ hθ).2 (nelsen14_isCI η hη).2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, cdf_transpose, cdf_transpose]
    exact ho ![x 1,x 0]

end Verification
