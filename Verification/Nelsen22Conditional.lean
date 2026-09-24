import Verification.Nelsen22Analytic

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem convex_increment_Ioo {f : ℝ → ℝ} {r : ℝ} (hf : ConvexOn ℝ (Ioo 0 r) f)
    {a b c e : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hab : a ≤ b) (hce : c ≤ e) (hbr : b+e < r) :
    0 ≤ f (b + e) - f (a + e) - f (b + c) + f (a + c) := by
  by_cases hz : b - a + (e - c) = 0
  · have hb : b = a := by linarith
    have he : e = c := by linarith
    simp [hb, he]
  have ht : 0 < b - a + (e - c) := by positivity
  have hp : 0 ≤ (b - a) / (b - a + (e - c)) := div_nonneg (sub_nonneg.mpr hab) ht.le
  have hq : 0 ≤ (e - c) / (b - a + (e - c)) := div_nonneg (sub_nonneg.mpr hce) ht.le
  have hpq : (b - a) / (b - a + (e - c)) + (e - c) / (b - a + (e - c)) = 1 := by
    rw [← add_div, div_self hz]
  have h₁ := hf.2 (show a + c ∈ Ioo 0 r by constructor <;> linarith)
    (show b + e ∈ Ioo 0 r by constructor <;> linarith) hp hq hpq
  have h₂ := hf.2 (show a + c ∈ Ioo 0 r by constructor <;> linarith)
    (show b + e ∈ Ioo 0 r by constructor <;> linarith) hq hp (by linarith)
  have he₁ : (b - a) / (b - a + (e - c)) * (a + c) +
      (e - c) / (b - a + (e - c)) * (b + e) = a + e := by field_simp; ring
  have he₂ : (e - c) / (b - a + (e - c)) * (a + c) +
      (b - a) / (b - a + (e - c)) * (b + e) = b + c := by field_simp; ring
  simp only [smul_eq_mul, he₁] at h₁
  simp only [smul_eq_mul, he₂] at h₂
  have hs := add_le_add h₁ h₂
  have he : (b - a) / (b - a + (e - c)) * f (a + c) +
      (e - c) / (b - a + (e - c)) * f (b + e) +
      ((e - c) / (b - a + (e - c)) * f (a + c) +
      (b - a) / (b - a + (e - c)) * f (b + e)) = f (a + c) + f (b + e) := by
    calc
      _ = ((b - a) / (b - a + (e - c)) + (e - c) / (b - a + (e - c))) *
        (f (a + c) + f (b + e)) := by ring
      _ = _ := by rw [hpq, one_mul]
  rw [he] at hs
  linarith


theorem n22Prime_ratio_antitone {p : ℝ} (hp : 1 ≤ p) (k : ℝ) (hk : 0 ≤ k) :
    AntitoneOn (fun t => n22Prime p (t+k)/n22Prime p t) (Ioo 0 (Real.pi/2)) := by
  intro a ha b hb hab
  change n22Prime p (b+k)/n22Prime p b ≤ n22Prime p (a+k)/n22Prime p a
  by_cases hcut : b+k < Real.pi/2
  · have hak : a+k ∈ Ioo (0:ℝ) (Real.pi/2) := ⟨by linarith [ha.1],by linarith⟩
    have hbk : b+k ∈ Ioo (0:ℝ) (Real.pi/2) := ⟨by linarith [hb.1],hcut⟩
    have hh := convex_increment_Ioo (n22Prime_log_concave hp).neg ha.1 (show (0:ℝ) ≤ 0 from le_rfl) hab hk hcut
    simp only [add_zero,Pi.neg_apply] at hh
    have hl : Real.log (-n22Prime p (b+k))-Real.log (-n22Prime p b) ≤
        Real.log (-n22Prime p (a+k))-Real.log (-n22Prime p a) := by linarith
    have he := Real.exp_le_exp.mpr hl
    simpa only [Real.exp_sub,Real.exp_log (neg_pos.mpr (n22Prime_neg hp ha)),
      Real.exp_log (neg_pos.mpr (n22Prime_neg hp hb)),Real.exp_log (neg_pos.mpr (n22Prime_neg hp hak)),
      Real.exp_log (neg_pos.mpr (n22Prime_neg hp hbk)),neg_div_neg_eq] using he
  · have hz : n22Prime p (b+k) = 0 := by simp only [n22Prime,hcut,ite_false]
    rw [hz,zero_div]
    apply div_nonneg_of_nonpos
    · by_cases hh : a+k < Real.pi/2
      · exact (n22Prime_neg hp ⟨by linarith [ha.1],hh⟩).le
      · simp only [n22Prime,hh,ite_false,le_refl]
    · exact (n22Prime_neg hp ha).le

theorem n22Phi_mem {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) :
    Real.arcsin (1-u^θ) ∈ Ioo 0 (Real.pi/2) := by
  have hp := Real.rpow_pos_of_pos hu.1 θ
  have hl := Real.rpow_lt_one hu.1.le hu.2 hθ
  exact ⟨Real.arcsin_pos.mpr (by linarith),Real.arcsin_lt_pi_div_two.mpr (by linarith)⟩

theorem n22Phi_deriv {θ u : ℝ} (hθ : 0 < θ) (hu : u ∈ Ioo 0 1) :
    HasDerivAt (fun x : ℝ => Real.arcsin (1-x^θ))
      ((1/Real.sqrt (1-(1-u^θ)^2))*(-(θ*u^(θ-1)))) u := by
  have hp := Real.rpow_pos_of_pos hu.1 θ
  have hl := Real.rpow_lt_one hu.1.le hu.2 hθ
  have hh := (Real.hasDerivAt_arcsin (x := 1-u^θ) (by linarith) (by linarith)).comp u
    (((hasDerivAt_id u).rpow_const (p := θ) (Or.inl hu.1.ne')).const_sub 1)
  simpa only [Function.comp_def,id_eq,one_mul] using hh

theorem nelsen22_isCD_positive {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (nelsen22 θ ⟨hθ.le,hθ1⟩).IsCD := by
  have hp : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ).mpr hθ1
  simp only [nelsen22,hθ.ne',dite_false]
  apply generator_isCD_of_antitone_derivative_ratio (n22Generator θ hθ hθ1)
    (fun u => Real.arcsin (1-u^θ))
    (fun u => (1/Real.sqrt (1-(1-u^θ)^2))*(-(θ*u^(θ-1)))) (n22Prime θ⁻¹) (Ioo 0 (Real.pi/2))
  · intro u _ _
    simp only [n22Generator,BivariateGenerator.innerPower,n22BaseGenerator,coe_unitPower,inv_inv]
  · intro u hu; exact (n22Phi_mem hθ hu).1
  · intro u hu; exact n22Phi_deriv hθ hu
  · intro t _; exact n22Psi_deriv θ⁻¹ hp t
  · intro u hu; exact n22Phi_mem hθ hu
  · intro t ht; exact n22Prime_neg hp ht
  · exact n22Prime_ratio_antitone hp

theorem nelsen22_isCD (θ : ℝ) (hθ : θ ∈ Icc 0 1) : (nelsen22 θ hθ).IsCD := by
  by_cases hz : θ = 0
  · subst θ; rw [nelsen22_zero]; exact isCD_independence
  · exact nelsen22_isCD_positive (lt_of_le_of_ne hθ.1 (Ne.symm hz)) hθ.2

end Verification
