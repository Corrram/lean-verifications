import Papers.Rockel2026XiBlest.ExtremalFamily
import Papers.Rockel2026XiBlest.Normalization
import Verification.QuadraticBandOrder
import Copula.Dependence.ConditionalMonotonicity

/-! # Concordance ordering in the revised manuscript -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiBlest

/-- The source's signed family, extended by independence at zero. -/
noncomputable def signedExtremalCopula (b : ℝ) : Copula 2 :=
  if hb : 0 ≤ b then extremalCopula b hb else
    (extremalCopula (-b) (by linarith)).reflect {1}

theorem signedExtremal_nonneg (b : ℝ) (hb : 0 ≤ b) :
    signedExtremalCopula b = extremalCopula b hb := by simp [signedExtremalCopula,hb]

theorem signedExtremal_neg (b : ℝ) (hb : b < 0) :
    signedExtremalCopula b = (extremalCopula (-b) (by linarith)).reflect {1} := by
  simp [signedExtremalCopula,not_le.mpr hb]

/-- Revised Proposition basic_properties_cb(iii): response reflection fixes xi and negates Blest nu for the actual signed family. -/
theorem signed_extremal_reflection_coefficients (b : ℝ) (hb : 0 < b) :
    (signedExtremalCopula (-b)).chatterjeeXi =
      (signedExtremalCopula b).chatterjeeXi ∧
    blestNu (signedExtremalCopula (-b)) = -blestNu (signedExtremalCopula b) := by
  rw [signedExtremal_neg (-b) (by linarith), signedExtremal_nonneg b hb.le]
  simpa using xi_blest_reflection (extremalCopula b hb.le)

/-- The reversed concordance direction printed in arXiv v1 Lemma 4.3(iii) fails at the M/W endpoints. -/
theorem not_comonotonic_concordanceLE_countermonotonic :
    ¬(Copula.comonotonic 2).ConcordanceLE Copula.countermonotonic := by
  intro h
  let mid : I := ⟨1 / 2, by constructor <;> norm_num⟩
  have hi : (⨅ i : Fin 2, ![mid, mid] i) = mid := by
    have he : (![mid, mid] : Fin 2 → I) = fun _ => mid := by
      funext i; fin_cases i <;> rfl
    rw [he]
    simp
  have ht := h.1 ![mid, mid]
  norm_num [Copula.cdf_comonotonic_two, Copula.cdf_countermonotonic, hi, mid] at ht

/-- The positive branch is ordered as copulas, not just by its rank coefficients. -/
theorem extremal_cdf_monotone (b d : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hbd : b ≤ d) (u v : I) :
    (extremalCopula b hb).cdf ![u,v] ≤ (extremalCopula d hd).cdf ![u,v] :=
  quadraticBand_cdf_mono b d hb hd hbd u v

/-- The full signed family is increasing in concordance order. -/
theorem signed_extremal_concordance (b d : ℝ) (hbd : b ≤ d) (u v : I) :
    (signedExtremalCopula b).cdf ![u,v] ≤ (signedExtremalCopula d).cdf ![u,v] := by
  by_cases hb : 0 ≤ b
  · rw [signedExtremal_nonneg b hb, signedExtremal_nonneg d (hb.trans hbd)]
    exact extremal_cdf_monotone b d hb (hb.trans hbd) hbd u v
  · have hb' : b < 0 := lt_of_not_ge hb
    rw [signedExtremal_neg b hb', Copula.cdf_reflect_second]
    by_cases hd : 0 ≤ d
    · rw [signedExtremal_nonneg d hd]
      have h₁ := extremal_cdf_monotone 0 (-b) (by norm_num) (by linarith) (by linarith)
        u (unitInterval.symm v)
      have h₂ := extremal_cdf_monotone 0 d (by norm_num) hd hd u v
      rw [extremal_zero] at h₁ h₂
      simp only [Copula.cdf_independence, Fin.prod_univ_two,
        Matrix.cons_val_zero,Matrix.cons_val_one,unitInterval.coe_symm_eq] at h₁ h₂
      nlinarith only [h₁,h₂]
    · rw [signedExtremal_neg d (lt_of_not_ge hd), Copula.cdf_reflect_second]
      exact sub_le_sub_left (extremal_cdf_monotone (-d) (-b) (by linarith) (by linarith)
        (by linarith) u (unitInterval.symm v)) _

/-- The reflected negative branch is stochastically decreasing. -/
theorem signed_extremal_isSD (b : ℝ) (hb : b < 0) : (signedExtremalCopula b).IsSD := by
  rw [signedExtremal_neg b hb,Copula.isSD_reflect_second_iff]
  exact quadraticBand_isSI (-b) (by linarith)

end Papers.Rockel2026XiBlest
