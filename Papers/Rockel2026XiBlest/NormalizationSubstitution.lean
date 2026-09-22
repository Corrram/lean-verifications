import Papers.Rockel2026XiBlest.SubstitutionFormulas

/-! # The exact change of variables from response thresholds to section parameters -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiBlest

theorem extremalQ_mem (b : ℝ) (hb : 0 < b) (v : I) : extremalQ b hb v ∈ Icc (-1/b) 1 := by
  have hi := quadraticIntercept_mem b hb.le v
  unfold extremalQ
  constructor
  · apply (div_le_div_iff_of_pos_right hb).mpr
    linarith [hi.2]
  · apply (div_le_one hb).mpr
    linarith [hi.1]

theorem extremalQ_normalizationMean (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1) :
    extremalQ b hb ⟨normalizationMean b q,(normalizationMean_properties b hb).2.2.2.2 q⟩=q := by
  have ha : -b*q ∈ Icc (-b) (1 : ℝ) := by
    constructor
    · nlinarith [hq.2]
    · have h := (div_le_iff₀ hb).mp hq.1
      nlinarith
  have he : (⟨normalizationMean b q,(normalizationMean_properties b hb).2.2.2.2 q⟩ : I)=quadraticMeanUnit b (-b*q) :=
    Subtype.ext (normalizationMean_eq b q)
  rw [he]
  unfold extremalQ
  change -quadraticIntercept b hb.le (quadraticMeanUnit b (-b*q))/b=q
  rw [quadraticIntercept_quadraticMean b hb.le ha]
  field_simp

theorem normalization_substitution (b : ℝ) (hb : 0 < b) (G : ℝ → ℝ) (hG : Continuous G) :
    (∫ v : I,G (extremalQ b hb v))=
      ∫ q in (-1/b)..1,G q*(-deriv (normalizationMean b) q) := by
  let clip : ℝ → I := fun x => ⟨unitClamp x,unitClamp_mem x⟩
  have hc : Continuous clip := (unitClamp_lipschitz.continuous).subtype_mk _
  have hclip (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : (clip x : ℝ)=x := by
    dsimp [clip,unitClamp]
    rw [max_eq_right hx.1,min_eq_right hx.2]
  let g : ℝ → ℝ := fun x => G (extremalQ b hb (clip x))
  have hg : Continuous g := hG.comp ((extremalQ_continuous b hb).comp hc)
  have hab : -1/b ≤ (1 : ℝ) := by
    have h : 0 ≤ 1/b := by positivity
    rw [neg_div]
    linarith
  have hd (q : ℝ) (hq : q ∈ uIcc (-1/b) 1) :
      HasDerivAt (normalizationMean b) (-b*(quadraticUpper b q-quadraticLower q)) q :=
    normalizationMean_hasDerivAt b q hb (by simpa only [uIcc_of_le hab] using hq)
  have hcont : Continuous (fun q => -b*(quadraticUpper b q-quadraticLower q)) := by
    unfold quadraticUpper quadraticLower
    fun_prop
  have hsub := intervalIntegral.integral_comp_mul_deriv hd hcont.continuousOn hg
  have he (q : ℝ) (hq : q ∈ Icc (-1/b) 1) : g (normalizationMean b q)=G q := by
    dsimp only [g]
    have hcl : clip (normalizationMean b q)=⟨normalizationMean b q,(normalizationMean_properties b hb).2.2.2.2 q⟩ :=
      Subtype.ext (hclip _ ((normalizationMean_properties b hb).2.2.2.2 q))
    rw [hcl,extremalQ_normalizationMean b q hb hq]
  have hchange : (∫ q in (-1/b)..1,G q*(-b*(quadraticUpper b q-quadraticLower q)))=∫ x in (1 : ℝ)..0,g x := by
    rw [(normalizationMean_properties b hb).2.2.1,(normalizationMean_properties b hb).2.2.2.1] at hsub
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro q hq
    dsimp only [Function.comp_def]
    rw [he q (by simpa only [uIcc_of_le hab] using hq)]
  have hgint : (∫ v : I,G (extremalQ b hb v))=∫ x in (0 : ℝ)..1,g x := by
    rw [← Copula.integral_unitInterval g]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      change G (extremalQ b hb v)=G (extremalQ b hb (clip v))
      have he : clip v=v := Subtype.ext (hclip v v.property)
      rw [he]
  rw [intervalIntegral.integral_symm (a := 0) (b := 1)] at hchange
  rw [hgint]
  calc
    _ = -(∫ q in (-1/b)..1,G q*(-b*(quadraticUpper b q-quadraticLower q))) := by linarith [hchange]
    _ = _ := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro q hq
      dsimp only
      rw [(hd q hq).deriv]
      ring

end Papers.Rockel2026XiBlest
