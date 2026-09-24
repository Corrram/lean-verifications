import Copula.Dependence.Density
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open ProbabilityTheory MeasureTheory Set
open Copula
open scoped unitInterval

namespace Verification

private noncomputable def positiveRectCutoff (u v : I) (n : ℕ) : I := by
  let q : ℝ := min (u : ℝ) (v : ℝ) / ((n : ℝ) + 1)
  have hq0 : 0 ≤ q := div_nonneg (le_min u.property.1 v.property.1) (by positivity)
  have hq1 : q ≤ 1 := by
    have hmin : min (u : ℝ) (v : ℝ) ≤ 1 :=
      (min_le_left _ _).trans u.property.2
    have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact (div_le_self (le_min u.property.1 v.property.1) hden).trans hmin
  exact ⟨q, hq0, hq1⟩

private theorem positiveRectCutoff_pos (u v : I)
    (hu : 0 < (u : ℝ)) (hv : 0 < (v : ℝ)) (n : ℕ) :
    0 < (positiveRectCutoff u v n : ℝ) := by
  change 0 < min (u : ℝ) (v : ℝ) / ((n : ℝ) + 1)
  exact div_pos (lt_min hu hv) (by positivity)

private theorem positiveRectCutoff_le_left (u v : I) (n : ℕ) :
    positiveRectCutoff u v n ≤ u := by
  change min (u : ℝ) (v : ℝ) / ((n : ℝ) + 1) ≤ (u : ℝ)
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  exact (div_le_self (le_min u.property.1 v.property.1) hden).trans
    (min_le_left _ _)

private theorem positiveRectCutoff_le_right (u v : I) (n : ℕ) :
    positiveRectCutoff u v n ≤ v := by
  change min (u : ℝ) (v : ℝ) / ((n : ℝ) + 1) ≤ (v : ℝ)
  have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  exact (div_le_self (le_min u.property.1 v.property.1) hden).trans
    (min_le_right _ _)

private theorem positiveRectCutoff_tendsto_zero (u v : I) :
    Filter.Tendsto (fun n : ℕ => (positiveRectCutoff u v n : ℝ))
      Filter.atTop (nhds 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
    (min (u : ℝ) (v : ℝ))
  convert h using 1 <;> simp [positiveRectCutoff, div_eq_mul_inv]

private theorem positiveRectCutoff_antitone (u v : I) :
    Antitone (positiveRectCutoff u v) := by
  intro m n hmn
  change min (u : ℝ) (v : ℝ) / ((n : ℝ) + 1) ≤
    min (u : ℝ) (v : ℝ) / ((m : ℝ) + 1)
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hden : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
  have hq : 0 ≤ min (u : ℝ) (v : ℝ) := le_min u.property.1 v.property.1
  simpa only [div_eq_mul_inv, one_mul] using
    (mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (by positivity : 0 < (m : ℝ) + 1) hden) hq)

private def positiveRectCutoffRect (u v : I) (n : ℕ) : Set (Fin 2 → I) :=
  Set.pi Set.univ (fun i : Fin 2 =>
    Set.Ioc (positiveRectCutoff u v n) (![u, v] i))

private theorem positiveRectCutoffRect_mono (u v : I) :
    Monotone (positiveRectCutoffRect u v) := by
  intro m n hmn x hx
  apply Set.mem_pi.mpr
  intro i hi
  have hxi := (Set.mem_pi.mp hx) i hi
  exact ⟨lt_of_le_of_lt (positiveRectCutoff_antitone u v hmn) hxi.1, hxi.2⟩

private theorem positiveRectCutoffRect_iUnion (u v : I) :
    (⋃ n : ℕ, positiveRectCutoffRect u v n) =
      Set.pi Set.univ (fun i : Fin 2 => Set.Ioc 0 (![u, v] i)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_pi.mpr
    intro i hi
    have hxi := (Set.mem_pi.mp hn) i hi
    exact ⟨lt_of_le_of_lt (positiveRectCutoff u v n).property.1 hxi.1, hxi.2⟩
  · intro hx
    have hx0 := (Set.mem_pi.mp hx) 0 (by simp)
    have hx1 := (Set.mem_pi.mp hx) 1 (by simp)
    have hx0' : 0 < (x 0 : ℝ) := by simpa using hx0.1
    have hx1' : 0 < (x 1 : ℝ) := by simpa using hx1.1
    have h0 := (positiveRectCutoff_tendsto_zero u v).eventually_lt_const hx0'
    have h1 := (positiveRectCutoff_tendsto_zero u v).eventually_lt_const hx1'
    obtain ⟨n, hn0, hn1⟩ := (h0.and h1).exists
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    apply Set.mem_pi.mpr
    intro i hi
    fin_cases i
    · exact ⟨hn0, by simpa using hx0.2⟩
    · exact ⟨hn1, by simpa using hx1.2⟩

private theorem copula_axis_zero (C : Copula 2) (i : Fin 2) :
    C.toMeasure {x | x i = 0} = 0 := by
  change C.toMeasure ((fun x : Fin 2 → I => x i) ⁻¹' ({0} : Set I)) = 0
  rw [C.measure_preimage_eval i (measurableSet_singleton (0 : I))]
  simp

private theorem measure_Iic_eq_positiveIoc
    (δ : Measure (Fin 2 → I))
    (h0 : δ {x | x 0 = 0} = 0)
    (h1 : δ {x | x 1 = 0} = 0)
    (u v : I) :
    δ (Set.Iic ![u, v]) =
      δ (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc 0 (![u, v] i))) := by
  let s : Set (Fin 2 → I) :=
    Set.pi Set.univ (fun i : Fin 2 => Set.Ioc 0 (![u, v] i))
  have hs : s ⊆ Set.Iic ![u, v] := by
    intro x hx
    change x ≤ ![u, v]
    intro i
    exact ((Set.mem_pi.mp hx) i (by simp)).2
  have hdiff : Set.Iic ![u, v] \ s ⊆
      {x : Fin 2 → I | x 0 = 0} ∪ {x | x 1 = 0} := by
    intro x hx
    by_contra haxes
    have hne : x 0 ≠ 0 ∧ x 1 ≠ 0 := by simpa using haxes
    have hp0 : (0 : I) < x 0 :=
      lt_of_le_of_ne (by exact_mod_cast (x 0).property.1) (Ne.symm hne.1)
    have hp1 : (0 : I) < x 1 :=
      lt_of_le_of_ne (by exact_mod_cast (x 1).property.1) (Ne.symm hne.2)
    have hxs : x ∈ s := by
      apply Set.mem_pi.mpr
      intro i hi
      fin_cases i
      · exact ⟨hp0, hx.1 0⟩
      · exact ⟨hp1, hx.1 1⟩
    exact hx.2 hxs
  have hnull : δ (Set.Iic ![u, v] \ s) = 0 :=
    measure_mono_null hdiff (measure_union_null h0 h1)
  exact (measure_eq_measure_of_null_sdiff hs hnull).symm


/-- Equality on rectangles bounded away from the axes identifies an absolutely
continuous measure with a copula measure. No global density bound is required. -/
theorem measure_eq_copula_of_positive_rectangles (C : Copula 2) (ν : Measure (Fin 2 → I))
    (hac : ν ≪ volume)
    (hrect : ∀ a b c d : I, 0 < (a:ℝ) → a ≤ b → 0 < (c:ℝ) → c ≤ d →
      ν (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a,c] i) (![b,d] i))) =
      C.toMeasure (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc (![a,c] i) (![b,d] i)))) :
    ν = C.toMeasure := by
  have haxis (i : Fin 2) : ν {x | x i = 0} = 0 :=
    hac (copula_axis_zero (Copula.independence 2) i)
  have hpos (u v : I) (hu : 0 < (u:ℝ)) (hv : 0 < (v:ℝ)) :
      ν (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc 0 (![u,v] i))) =
      C.toMeasure (Set.pi Set.univ (fun i : Fin 2 => Set.Ioc 0 (![u,v] i))) := by
    rw [← positiveRectCutoffRect_iUnion u v,
      (positiveRectCutoffRect_mono u v).measure_iUnion (μ := ν),
      (positiveRectCutoffRect_mono u v).measure_iUnion (μ := C.toMeasure)]
    apply iSup_congr
    intro n
    have hset : Set.pi Set.univ (fun i : Fin 2 =>
        Set.Ioc (![positiveRectCutoff u v n,positiveRectCutoff u v n] i) (![u,v] i)) =
        positiveRectCutoffRect u v n := by
      ext x
      simp [positiveRectCutoffRect, Set.mem_pi, Fin.forall_fin_two]
    simpa only [hset] using hrect (positiveRectCutoff u v n) u (positiveRectCutoff u v n) v
      (positiveRectCutoff_pos u v hu hv n) (positiveRectCutoff_le_left u v n)
      (positiveRectCutoff_pos u v hu hv n) (positiveRectCutoff_le_right u v n)
  have hlo (u v : I) : ν (Iic ![u,v]) = C.toMeasure (Iic ![u,v]) := by
    rw [measure_Iic_eq_positiveIoc ν (haxis 0) (haxis 1),
      measure_Iic_eq_positiveIoc C.toMeasure (copula_axis_zero C 0) (copula_axis_zero C 1)]
    by_cases hu : 0 < (u:ℝ)
    · by_cases hv : 0 < (v:ℝ)
      · exact hpos u v hu hv
      · have hv0 : v = 0 := Subtype.ext (le_antisymm (le_of_not_gt hv) v.property.1)
        subst v
        have hs : Set.pi Set.univ (fun i : Fin 2 => Set.Ioc 0 (![u,0] i)) = ∅ := by
          ext x
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hx
          have h : x 1 ∈ Set.Ioc (0:I) 0 := (Set.mem_pi.mp hx) 1 (by simp)
          exact (not_lt_of_ge h.2) h.1
        simp [hs]
    · have hu0 : u = 0 := Subtype.ext (le_antisymm (le_of_not_gt hu) u.property.1)
      subst u
      have hs : Set.pi Set.univ (fun i : Fin 2 => Set.Ioc 0 (![0,v] i)) = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have h : x 0 ∈ Set.Ioc (0:I) 0 := (Set.mem_pi.mp hx) 0 (by simp)
        exact (not_lt_of_ge h.2) h.1
      simp [hs]
  have htop : Iic ![(1:I),1] = Set.univ := by
    ext x
    simp [Set.mem_Iic, Pi.le_def, Fin.forall_fin_two, unitInterval.le_one']
  have hprob : IsProbabilityMeasure ν := ⟨by simpa [htop] using hlo 1 1⟩
  have hμ (u : Fin 2 → I) : ν.real (Iic u) = C.cdf u := by
    have h := hlo (u 0) (u 1)
    have heta : ![u 0,u 1] = u := by ext i; fin_cases i <;> simp
    rw [heta] at h
    exact congrArg ENNReal.toReal h
  let D := C.isClassical_cdf.ofMeasure ⟨ν,hprob⟩ hμ
  have he : D = C := Copula.cdf_injective (C.isClassical_cdf.cdf_ofMeasure ⟨ν,hprob⟩ hμ)
  rw [← he]
  rfl

end Verification
