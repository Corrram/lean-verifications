import Verification.TEVZeroLimit
import Papers.AnsariRockel2024.TEV
import Papers.AnsariRockel2024.HuslerReissTails
import Papers.AnsariRockel2024.TailsAndOrders
import Copula.TailDependence.Examples

/-! # Table 4 audit: the degrees-of-freedom limits of the t-EV family

Table 4 prints `C^{tEV}_{0,ρ}=C^{MO}` and `C^{tEV}_{∞,ρ}=C^{HR}_ρ`. For a fixed correlation
`-1<ρ<1` we prove:

* as `ν → ∞` the t-EV copulas converge pointwise to independence; hence no Hüsler–Reiss
  copula with positive parameter is the fixed-correlation limit;
* as `ν → 0+` they converge pointwise to the Marshall–Olkin copula with both weights equal
  to `1/2+arcsin(ρ)/π`, which is not independence (so not a Marshall–Olkin copula with a zero
  weight).
-/

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem tEV_limit_infinity {ι : Type*} {l : Filter ι} (ν : ι → ℝ) (hν : ∀ i, 0<ν i)
    (hνt : Tendsto ν l atTop) (r : ℝ) (hr : r∈Ioo (-1) 1) (u v : I) :
    Tendsto (fun i => (Verification.tEV (ν i) r (hν i) ⟨hr.1.le,hr.2.le⟩).cdf ![u,v]) l
      (𝓝 ((independence 2).cdf ![u,v])) :=
  Verification.tEV_tendsto_independence ν hν hνt hr u v

theorem tEV_limit_zero {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (ν : ι → ℝ) (hν : ∀ i, 0<ν i) (hν1 : ∀ i, ν i≤1) (hνl : Tendsto ν l (𝓝 0))
    (r : ℝ) (hr : r∈Ioo (-1) 1) (u v : I) :
    Tendsto (fun i => (Verification.tEV (ν i) r (hν i) ⟨hr.1.le,hr.2.le⟩).cdf ![u,v]) l
      (𝓝 ((marshallOlkin (Verification.tEVZeroWeightI r) (Verification.tEVZeroWeightI r)).cdf ![u,v])) :=
  Verification.tEV_tendsto_marshallOlkin ν hν hν1 hνl hr u v

theorem tEV_zero_weight (r : ℝ) :
    ((Verification.tEVZeroWeightI r : I) : ℝ)=1/2+Real.arcsin r/Real.pi := rfl

theorem huslerReiss_ne_independence (δ : ℝ) (hδ : 0<δ) :
    Verification.huslerReissPositive δ hδ≠independence 2 := by
  intro h
  have ht := (huslerReiss_tails δ hδ).2
  rw [h] at ht
  have hu := ht.unique hasUpperTailDependence_independence
  have hn := Verification.standardNormalCDF_strictMono (show 1/δ<1/δ+1 by linarith)
  have hb := ProbabilityTheory.cdf_le_one (gaussianReal 0 1) (1/δ+1)
  linarith

/-- The printed `ν → ∞` limit fails: for fixed `ρ∈(-1,1)` the limit is independence, which is
not a Hüsler–Reiss copula with positive parameter. -/
theorem tEV_printed_infinity_limit_false (r : ℝ) (hr : r∈Ioo (-1) 1) (δ : ℝ) (hδ : 0<δ) :
    ¬ ∀ u v : I, Tendsto (fun n : ℕ => (Verification.tEV ((n:ℝ)+1) r (by positivity)
      ⟨hr.1.le,hr.2.le⟩).cdf ![u,v]) atTop
        (𝓝 ((Verification.huslerReissPositive δ hδ).cdf ![u,v])) := by
  intro h
  apply huslerReiss_ne_independence δ hδ
  apply ext_cdf_two
  intro u v
  have h1 := h u v
  have h2 := tEV_limit_infinity (fun n : ℕ => (n:ℝ)+1) (fun n => by positivity)
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop) r hr u v
  exact tendsto_nhds_unique h1 h2

theorem tEV_zero_weight_pos (r : ℝ) (hr : r∈Ioo (-1) 1) :
    0<((Verification.tEVZeroWeightI r : I) : ℝ) := by
  rw [tEV_zero_weight]
  have h : -(Real.pi/2)<Real.arcsin r := Real.neg_pi_div_two_lt_arcsin.mpr hr.1
  have hp := Real.pi_pos
  have : -(1/2:ℝ)<Real.arcsin r/Real.pi := by rw [lt_div_iff₀ hp]; linarith
  linarith

/-- The `ν → 0` limit is not independence (in particular not a Marshall–Olkin copula with a
zero weight): its upper tail coefficient is `1/2+arcsin(ρ)/π>0`. -/
theorem tEV_zero_limit_ne_independence (r : ℝ) (hr : r∈Ioo (-1) 1) :
    marshallOlkin (Verification.tEVZeroWeightI r) (Verification.tEVZeroWeightI r)≠independence 2 := by
  intro h
  have ht := (marshallOlkin_tails (Verification.tEVZeroWeightI r) (Verification.tEVZeroWeightI r)).2
  rw [h,min_self] at ht
  have hu := ht.unique hasUpperTailDependence_independence
  linarith [tEV_zero_weight_pos r hr]

end Papers.AnsariRockel2024
