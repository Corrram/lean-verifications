import Verification.FinitePrefixMajorization
import Mathlib.Analysis.Convex.Deriv

/-! # Convex Karamata inequality from ordered partial sums -/

open Set Filter
open scoped BigOperators Topology

namespace Verification

/-- The right derivative supplies a supporting slope at every interior point. -/
theorem convex_right_support {φ : ℝ → ℝ} (hφ : ConvexOn ℝ (Icc 0 1) φ)
    {x y : ℝ} (hx : x ∈ Ioo 0 1) (hy : y ∈ Icc 0 1) :
    derivWithin φ (Ioi x) x*(y-x) ≤ φ y-φ x := by
  have hxi : x ∈ interior (Icc (0:ℝ) 1) := by simpa only [interior_Icc] using hx
  rcases lt_trichotomy x y with hxy | he | hyx
  · have h := hφ.rightDeriv_le_slope_of_mem_interior hxi hy hxy
    rw [slope_def_field] at h
    exact (le_div_iff₀ (sub_pos.mpr hxy)).mp h
  · subst y
    simp
  · have h := (hφ.slope_le_leftDeriv_of_mem_interior hy hxi hyx).trans
      (hφ.leftDeriv_le_rightDeriv_of_mem_interior hxi)
    rw [slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hyx)).mp h
    nlinarith only [hh]

/-- An interior version; endpoint values will follow by continuity. -/
theorem majorization_sum_convex_interior (a b : ℕ → ℝ) (n : ℕ)
    (hb : ∀ i, i<n-1 → b (i+1) ≤ b i)
    (hp : ∀ k, k≤n → (∑ i ∈ Finset.range k,b i) ≤ ∑ i ∈ Finset.range k,a i)
    (ht : (∑ i ∈ Finset.range n,a i) = ∑ i ∈ Finset.range n,b i)
    (ha : ∀ i, i<n → a i ∈ Icc 0 1) (hbi : ∀ i, i<n → b i ∈ Ioo 0 1)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Icc 0 1) φ) :
    (∑ i ∈ Finset.range n,φ (b i)) ≤ ∑ i ∈ Finset.range n,φ (a i) := by
  let w := fun i => derivWithin φ (Ioi (b i)) (b i)
  have hw : ∀ i, i<n-1 → w (i+1) ≤ w i := by
    intro i hi
    apply hφ.monotoneOn_rightDeriv
    · simpa only [interior_Icc] using hbi (i+1) (by omega)
    · simpa only [interior_Icc] using hbi i (by omega)
    · exact hb i hi
  have hs := decreasing_weighted_sum_nonneg w (fun i => a i-b i) n hw
    (fun k hk => by simpa only [Finset.sum_sub_distrib] using sub_nonneg.mpr (hp k hk))
    (by simp only [Finset.sum_sub_distrib,ht,sub_self])
  have hl : (∑ i ∈ Finset.range n,w i*(a i-b i)) ≤ ∑ i ∈ Finset.range n,(φ (a i)-φ (b i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact convex_right_support hφ (hbi i (Finset.mem_range.mp hi)) (ha i (Finset.mem_range.mp hi))
  rw [Finset.sum_sub_distrib] at hl
  linarith

/-- Karamata's inequality on the full closed interval, including endpoint singularities of slopes. -/
theorem majorization_sum_convex_unitInterval (a b : ℕ → ℝ) (n : ℕ)
    (hb : ∀ i, i<n-1 → b (i+1) ≤ b i)
    (hp : ∀ k, k≤n → (∑ i ∈ Finset.range k,b i) ≤ ∑ i ∈ Finset.range k,a i)
    (ht : (∑ i ∈ Finset.range n,a i) = ∑ i ∈ Finset.range n,b i)
    (ha : ∀ i, i<n → a i ∈ Icc 0 1) (hbi : ∀ i, i<n → b i ∈ Icc 0 1)
    (φ : ℝ → ℝ) (hc : Continuous φ) (hφ : ConvexOn ℝ (Icc 0 1) φ) :
    (∑ i ∈ Finset.range n,φ (b i)) ≤ ∑ i ∈ Finset.range n,φ (a i) := by
  have he (ε : ℝ) (hε : ε ∈ Ioo 0 (1/2)) :
      (∑ i ∈ Finset.range n,φ (ε+(1-2*ε)*b i)) ≤
        ∑ i ∈ Finset.range n,φ (ε+(1-2*ε)*a i) := by
    have hpε : 0 ≤ 1-2*ε := by linarith [hε.2]
    have hm {x : ℝ} (hx : x ∈ Icc 0 1) : ε+(1-2*ε)*x ∈ Ioo 0 1 := by
      have h₁ := mul_nonneg hpε hx.1
      have h₂ := mul_nonneg hpε (sub_nonneg.mpr hx.2)
      constructor <;> nlinarith [hε.1]
    apply majorization_sum_convex_interior (fun i => ε+(1-2*ε)*a i)
      (fun i => ε+(1-2*ε)*b i) n
    · intro i hi
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hb i hi) hpε)
    · intro k hk
      simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hp k hk) hpε)
    · simp only [Finset.sum_add_distrib,← Finset.mul_sum,ht]
    · intro i hi
      exact ⟨(hm (ha i hi)).1.le,(hm (ha i hi)).2.le⟩
    · intro i hi
      exact hm (hbi i hi)
    · exact hφ
  have hl (f : ℕ → ℝ) : Tendsto (fun ε : ℝ => ∑ i ∈ Finset.range n,φ (ε+(1-2*ε)*f i))
      (𝓝[>] (0:ℝ)) (𝓝 (∑ i ∈ Finset.range n,φ (f i))) := by
    have hcont : Continuous (fun ε : ℝ => ∑ i ∈ Finset.range n,φ (ε+(1-2*ε)*f i)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto (hl b) (hl a)
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (show (0:ℝ)<1/2 by norm_num)).filter_mono nhdsWithin_le_nhds] with ε hε hε2
  exact he ε ⟨hε,hε2⟩

/-- Finite-index form used for equal-width copula sections. -/
theorem majorization_fin_sum_convex {n : ℕ} (a b : Fin n → ℝ) (hb : Antitone b)
    (hp : ∀ k : Fin (n+1),
      (∑ i : Fin n, if i.val < k.val then b i else 0) ≤ ∑ i : Fin n, if i.val < k.val then a i else 0)
    (ht : (∑ i, a i) = ∑ i, b i)
    (ha : ∀ i, a i ∈ Icc 0 1) (hbi : ∀ i, b i ∈ Icc 0 1)
    (φ : ℝ → ℝ) (hc : Continuous φ) (hφ : ConvexOn ℝ (Icc 0 1) φ) :
    (∑ i, φ (b i)) ≤ ∑ i, φ (a i) := by
  have h := majorization_sum_convex_unitInterval (extendFin a) (extendFin b) n (by
    intro i hi
    have hi0 : i < n := by omega
    have hi1 : i+1 < n := by omega
    simp only [extendFin,dite_eq_left hi0,dite_eq_left hi1]
    exact hb (show (⟨i,hi0⟩ : Fin n) ≤ ⟨i+1,hi1⟩ by simp)) (by
    intro k hk
    simpa only [← sum_extendFin_prefix b k hk,← sum_extendFin_prefix a k hk] using hp ⟨k,by omega⟩) (by
    simpa only [Finset.sum_fin_eq_sum_range,extendFin] using ht)
    (by intro i hi; simpa only [extendFin,dite_eq_left hi] using ha ⟨i,hi⟩)
    (by intro i hi; simpa only [extendFin,dite_eq_left hi] using hbi ⟨i,hi⟩) φ hc hφ
  rw [← Fin.sum_univ_eq_sum_range (fun i => φ (extendFin b i)) n,
    ← Fin.sum_univ_eq_sum_range (fun i => φ (extendFin a i)) n] at h
  simpa only [extendFin,dite_eq_left (Fin.is_lt _)] using h

end Verification
