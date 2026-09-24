import Verification.ArchimedeanCI
import Copula.Families.Nelsen
import Copula.Dependence.BB1TotalPositivity

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

theorem convex_neg_log_one_add_power {α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ConvexOn ℝ (Ici 0) (fun t : ℝ => -Real.log (1 + t ^ α)) := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  have hx' : 0 < 1 + x ^ α := by
    have hp := Real.rpow_nonneg hx0 α
    linarith
  have hy' : 0 < 1 + y ^ α := by
    have hp := Real.rpow_nonneg hy0 α
    linarith
  have hp := (Real.concaveOn_rpow hα0 hα1).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hp ⊢
  have he : a * (1 + x ^ α) + b * (1 + y ^ α) =
      1 + (a * x ^ α + b * y ^ α) := by nlinarith
  have hsumpos : 0 < a * (1 + x ^ α) + b * (1 + y ^ α) := by
    rw [he]
    have hn : 0 ≤ a * x ^ α + b * y ^ α := by positivity
    linarith
  have hbound : a * (1 + x ^ α) + b * (1 + y ^ α) ≤
      1 + (a * x + b * y) ^ α := by
    rw [he]
    linarith
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 hx' hy' ha hb hab
  simp only [smul_eq_mul] at hlog
  have hmono := Real.log_le_log hsumpos hbound
  nlinarith


noncomputable def bbPsiDeriv (p q t : ℝ) : ℝ := -p*q*t^(p-1)*(1+t^p)^(-q-1)

theorem bbPsi_deriv {p q t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => (1+x^p)^(-q)) (bbPsiDeriv p q t) t := by
  have hB : 0 < 1+t^p := by positivity
  have hh := (((hasDerivAt_id t).rpow_const (p := p) (Or.inl ht.ne')).const_add 1).rpow_const
    (p := -q) (Or.inl hB.ne')
  convert hh using 1
  · rfl
  · dsimp [bbPsiDeriv]
    ring

theorem bbPsiDeriv_neg {p q t : ℝ} (hp : 0 < p) (hq : 0 < q) (ht : 0 < t) :
    bbPsiDeriv p q t < 0 := by
  have hB : 0 < 1+t^p := by positivity
  unfold bbPsiDeriv
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hp) hq) (Real.rpow_pos_of_pos ht _))
    (Real.rpow_pos_of_pos hB _)

theorem bbPsiDeriv_logconvex {p q : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (-bbPsiDeriv p q t)) := by
  have h₁ := strictConcaveOn_log_Ioi.concaveOn.neg.smul (sub_nonneg.mpr hp1)
  have h₂ := ((convex_neg_log_one_add_power hp.le hp1).subset Ioi_subset_Ici_self (convex_Ioi 0)).smul
    (show 0 ≤ q+1 by linarith)
  have hc := (h₁.add h₂).add_const (Real.log (p*q))
  apply hc.congr
  intro t ht
  have ht0 : 0 < t := ht
  have hB : 0 < 1+t^p := by positivity
  have he : -bbPsiDeriv p q t = (p*q)*t^(p-1)*(1+t^p)^(-q-1) := by unfold bbPsiDeriv; ring
  change (1-p)*(-Real.log t)+(q+1)*(-Real.log (1+t^p))+Real.log (p*q) = Real.log (-bbPsiDeriv p q t)
  rw [he, Real.log_mul (mul_ne_zero (mul_ne_zero hp.ne' hq.ne') (Real.rpow_pos_of_pos ht0 _).ne')
      (Real.rpow_pos_of_pos hB _).ne',
    Real.log_mul (mul_ne_zero hp.ne' hq.ne') (Real.rpow_pos_of_pos ht0 _).ne',
    Real.log_rpow ht0, Real.log_rpow hB]
  ring

theorem bb1_isCI (θ : ℝ) (hθ : 0 < θ) (δ : ℝ) (hδ : 1 ≤ δ) :
    (bb1 θ hθ δ hδ).IsCI := by
  let g := (claytonGenerator θ hθ).outerPower δ hδ
  let φ : ℝ → ℝ := fun u => (u^(-θ)-1)^δ
  let φ' : ℝ → ℝ := fun u => (-θ*u^(-θ-1))*δ*(u^(-θ)-1)^(δ-1)
  have hδ0 : 0 < δ := lt_of_lt_of_le zero_lt_one hδ
  have hbase (u : ℝ) (hu : u ∈ Ioo 0 1) : 0 < u^(-θ)-1 :=
    sub_pos.mpr (Real.one_lt_rpow_of_pos_of_lt_one_of_neg hu.1 hu.2 (neg_neg_of_pos hθ))
  apply generator_isCI_of_logconvex_neg_deriv g φ φ' (bbPsiDeriv δ⁻¹ θ⁻¹)
  · intro u _ _; rfl
  · intro u hu
    exact Real.rpow_pos_of_pos (hbase u hu) _
  · intro u hu
    have hh := (((hasDerivAt_id u).rpow_const (p := -θ) (Or.inl hu.1.ne')).sub_const 1).rpow_const
      (p := δ) (Or.inl (hbase u hu).ne')
    convert hh using 1
    · rfl
    · dsimp [φ']
      ring
  · intro t ht
    exact bbPsi_deriv ht
  · intro t ht
    exact bbPsiDeriv_neg (inv_pos.mpr hδ0) (inv_pos.mpr hθ) ht
  · exact bbPsiDeriv_logconvex (inv_pos.mpr hδ0) (inv_le_one_of_one_le₀ hδ) (inv_pos.mpr hθ)

theorem nelsen12_isCI (θ : ℝ) (hθ : 1 ≤ θ) : (nelsen12 θ hθ).IsCI :=
  bb1_isCI 1 (by norm_num) θ hθ

theorem nelsen14_isCI (θ : ℝ) (hθ : 1 ≤ θ) : (nelsen14 θ hθ).IsCI :=
  bb1_isCI θ⁻¹ (inv_pos.mpr (by linarith)) θ hθ

end Verification
