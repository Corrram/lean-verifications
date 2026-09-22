import Papers.Rockel2026XiBlest.ExtremalFamily
import Verification.Mixture

/-! # Complete normalization-map properties from Lemma 2.1 -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiBlest

noncomputable def normalizationMean (b q : ℝ) : ℝ :=
  ∫ t : I,unitClamp (b*((1-(t : ℝ))^2-q))

theorem normalizationMean_eq (b q : ℝ) : normalizationMean b q=quadraticMean b (-b*q) := by
  unfold normalizationMean quadraticMean
  congr 1; funext t; congr 1; ring

theorem normalizationMean_properties (b : ℝ) (hb : 0 < b) :
    Continuous (normalizationMean b) ∧ StrictAntiOn (normalizationMean b) (Icc (-1/b) 1) ∧
    normalizationMean b (-1/b)=1 ∧ normalizationMean b 1=0 ∧
    ∀ q : ℝ, normalizationMean b q ∈ Icc (0 : ℝ) 1 := by
  have hmem (q : ℝ) (hq : q ∈ Icc (-1/b) 1) : -b*q ∈ Icc (-b) (1 : ℝ) := by
    constructor
    · nlinarith [hq.2]
    · have hh := (div_le_iff₀ hb).mp hq.1
      nlinarith
  refine ⟨?_,?_,?_,?_,?_⟩
  · have he : normalizationMean b=fun q => quadraticMean b (-b*q) := funext (normalizationMean_eq b)
    rw [he]
    exact (continuous_quadraticMean b).comp (by fun_prop)
  · intro q hq r hr hqr
    rw [normalizationMean_eq,normalizationMean_eq]
    exact quadraticMean_strictMonoOn hb.le (hmem r hr) (hmem q hq) (by nlinarith)
  · rw [normalizationMean_eq]
    have he : -b*(-1/b)=1 := by field_simp
    rw [he,quadraticMean_top b hb.le]
  · rw [normalizationMean_eq,mul_one,quadraticMean_zero b hb.le]
  · intro q
    rw [normalizationMean_eq]
    exact quadraticMean_mem b (-b*q)

theorem quadraticIntercept_continuous (b : ℝ) (hb : 0 ≤ b) : Continuous (quadraticIntercept b hb) := by
  let f : Icc (-b) (1 : ℝ) → I := fun a => quadraticMeanUnit b a
  have hf : Continuous f := (continuous_quadraticMeanUnit b).comp continuous_subtype_val
  have hs : Function.Surjective f := by
    intro v
    refine ⟨⟨quadraticIntercept b hb v,quadraticIntercept_mem b hb v⟩,?_⟩
    apply Subtype.ext
    exact quadraticIntercept_mean b hb v
  apply (hf.isClosedMap.isQuotientMap hf hs).continuous_iff.mpr
  have he : quadraticIntercept b hb ∘ f=fun a : Icc (-b) (1 : ℝ) => (a : ℝ) := by
    funext a
    exact quadraticIntercept_quadraticMean b hb a.property
  rw [he]
  exact continuous_subtype_val

theorem extremalQ_continuous (b : ℝ) (hb : 0 < b) : Continuous (extremalQ b hb) :=
  (quadraticIntercept_continuous b hb.le).neg.div_const b

theorem extremal_kernel_continuous (b : ℝ) (hb : 0 ≤ b) :
    Continuous (fun p : I × I => quadraticKernel b hb p.2 p.1) := by
  have h : Continuous (fun p : I × I => quadraticIntercept b hb p.2) :=
    (quadraticIntercept_continuous b hb).comp continuous_snd
  unfold quadraticKernel unitClamp
  fun_prop

/-- Lemma 4.4, including both endpoints and singular copulas. -/
theorem xi_mixture_continuous (C D : Copula 2) :
    Continuous (fun a : I => (C.mix D a).chatterjeeXi) := continuous_xi_mix C D

end Papers.Rockel2026XiBlest
