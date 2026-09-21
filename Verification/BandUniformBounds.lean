import Verification.DiagonalBand

/-! # Quantitative uniform bounds for normalized clamped bands -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

private theorem clamp_shift {x y r : ℝ} (hr : 0 ≤ r) (h : x ≤ y + r) :
    unitClamp x ≤ unitClamp y + r := by
  unfold unitClamp
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- Every clamped section is within its slope of its prescribed mean. -/
theorem clamped_deviation {a b : ℝ} (hb : 0 ≤ b) (u : I) :
    |unitClamp (a-b*(u : ℝ)) - clampedMean b a| ≤ b := by
  have hi : Integrable (fun t : I => unitClamp (a-b*(t : ℝ))) :=
    Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop)
  have hpair (s t : I) : unitClamp (a-b*(s : ℝ)) ≤ unitClamp (a-b*(t : ℝ)) + b := by
    apply clamp_shift hb
    nlinarith [s.property.1, t.property.2]
  have h₁ := integral_mono (integrable_const (unitClamp (a-b*(u : ℝ))))
    (hi.add (integrable_const b)) (fun t => hpair u t)
  have h₂ := integral_mono hi (integrable_const (unitClamp (a-b*(u : ℝ))+b)) (fun t => hpair t u)
  simp only [Pi.add_apply] at h₁
  rw [integral_add hi (integrable_const b)] at h₁
  simp only [integral_const, probReal_univ, one_smul] at h₁ h₂
  change |unitClamp (a-b*(u : ℝ)) - ∫ t : I, unitClamp (a-b*(t : ℝ))| ≤ b
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A uniform rate at the independence endpoint. -/
theorem diagonalBand_independence_error (b : ℝ) (hb : 0 ≤ b) (u v : I) :
    |(diagonalBand b hb).cdf ![u,v] - (u : ℝ)*(v : ℝ)| ≤ b := by
  rw [diagonalBand_cdf]
  have hi := bandKernel_integrable b hb v
  change Integrable (fun t : I => unitClamp (bandIntercept b hb v-b*(t : ℝ))) at hi
  have h (t : I) : (v : ℝ)-b ≤ unitClamp (bandIntercept b hb v-b*(t : ℝ)) ∧
      unitClamp (bandIntercept b hb v-b*(t : ℝ)) ≤ v+b := by
    have hh := clamped_deviation (a := bandIntercept b hb v) hb t
    rw [bandIntercept_mean] at hh
    exact ⟨by linarith [(abs_le.mp hh).1], by linarith [(abs_le.mp hh).2]⟩
  have h₁ := setIntegral_mono_on (s := Iic u) (integrable_const ((v : ℝ)-b)).integrableOn
    hi.integrableOn measurableSet_Iic (fun t _ => (h t).1)
  have h₂ := setIntegral_mono_on (s := Iic u) hi.integrableOn
    (integrable_const ((v : ℝ)+b)).integrableOn measurableSet_Iic (fun t _ => (h t).2)
  simp only [setIntegral_const, Measure.real, unitInterval.volume_Iic,
    ENNReal.toReal_ofReal u.property.1, smul_eq_mul] at h₁ h₂
  exact abs_le.mpr ⟨by nlinarith [u.property.2], by nlinarith [u.property.2]⟩

/-- A uniform rate at the comonotonic endpoint. -/
theorem diagonalBand_comonotonic_error (b : ℝ) (hb : 0 < b) (u v : I) :
    |(diagonalBand b hb.le).cdf ![u,v] - min (u : ℝ) (v : ℝ)| ≤ 1/b := by
  let a := bandIntercept b hb.le v
  let g : I → ℝ := fun t => unitClamp (a-b*(t : ℝ))
  have hi : Integrable g := bandKernel_integrable b hb.le v
  have hm : (∫ t, g t) = (v : ℝ) := bandIntercept_mean b hb.le v
  have hc : (diagonalBand b hb.le).cdf ![u,v] = ∫ t in Iic u, g t := diagonalBand_cdf b hb.le u v
  have hup : (diagonalBand b hb.le).cdf ![u,v] ≤ min (u : ℝ) (v : ℝ) := by
    exact le_min ((diagonalBand b hb.le).cdf_le_coord ![u,v] 0)
      ((diagonalBand b hb.le).cdf_le_coord ![u,v] 1)
  rw [abs_of_nonpos (sub_nonpos.mpr hup)]
  have hb0 : 0 ≤ 1/b := by positivity
  by_cases hu : a-b*(u : ℝ) ≤ 0
  · have ht : (∫ t in Ioc u (1 : I), g t) = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      dsimp [g, unitClamp]
      rw [max_eq_left (by nlinarith [show (u : ℝ) < t from ht.1])]
      norm_num
    have he := Copula.integral_Iic_add_Ioc_unit hi (show u ≤ (1 : I) from u.property.2)
    have hs : Iic (1 : I) = univ := by ext t; simp [unitInterval.le_one']
    rw [ht, hs, Measure.restrict_univ, hm, add_zero, ← hc] at he
    rw [he]
    linarith [min_le_right (u : ℝ) (v : ℝ)]
  · by_cases hs : (u : ℝ) ≤ 1/b
    · have hn := (diagonalBand b hb.le).cdf_nonneg ![u,v]
      linarith [min_le_left (u : ℝ) (v : ℝ)]
    · let s : I := ⟨(u : ℝ)-1/b, by constructor <;> linarith [u.property.2]⟩
      have hsu : s ≤ u := by change (u : ℝ)-1/b ≤ u; linarith
      have hg : (∫ t in Iic s, g t) = (s : ℝ) := by
        calc
          _ = ∫ _t in Iic s, (1 : ℝ) := by
            apply setIntegral_congr_fun measurableSet_Iic
            intro t ht
            have hts : (t : ℝ) ≤ (u : ℝ)-1/b := ht
            have hdiv : b*(1/b) = 1 := by field_simp
            have hraw : 1 ≤ a-b*(t : ℝ) := by nlinarith
            dsimp [g, unitClamp]
            rw [max_eq_right (by linarith), min_eq_left hraw]
          _ = _ := by simp [Measure.real, unitInterval.volume_Iic, s.property.1]
      have ht : 0 ≤ ∫ t in Ioc s u, g t :=
        integral_nonneg (fun t => (unitClamp_mem _).1)
      have he := Copula.integral_Iic_add_Ioc_unit hi hsu
      rw [hg, ← hc] at he
      have hsval : (s : ℝ) = (u : ℝ)-1/b := rfl
      linarith [min_le_left (u : ℝ) (v : ℝ)]

end Verification
