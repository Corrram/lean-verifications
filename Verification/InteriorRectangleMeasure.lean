import Verification.PositiveRectangleMeasure

open ProbabilityTheory MeasureTheory Set Filter
open Copula
open scoped unitInterval Topology

namespace Verification

private noncomputable def upperRectCutoff (n : ℕ) : I :=
  ⟨1-1/((n:ℝ)+1), by
    have hd : (1:ℝ) ≤ (n:ℝ)+1 := by
      have hN : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hh : 1/((n:ℝ)+1) ≤ 1 := by
      simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one hd
    constructor
    · linarith
    · have hp : 0 ≤ 1/((n:ℝ)+1) := by positivity
      linarith⟩

private theorem upperRectCutoff_lt_one (n : ℕ) : upperRectCutoff n < 1 := by
  change 1-1/((n:ℝ)+1) < 1
  have hh : 0 < 1/((n:ℝ)+1) := by positivity
  linarith

private theorem upperRectCutoff_mono : Monotone upperRectCutoff := by
  intro m n hmn
  change 1-1/((m:ℝ)+1) ≤ 1-1/((n:ℝ)+1)
  have hh := one_div_le_one_div_of_le (by positivity : 0 < (m:ℝ)+1)
    (show (m:ℝ)+1 ≤ (n:ℝ)+1 by exact_mod_cast Nat.add_le_add_right hmn 1)
  linarith

private theorem upperRectCutoff_tendsto : Tendsto (fun n => (upperRectCutoff n:ℝ)) atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1-1/((n:ℝ)+1)) atTop (𝓝 (1:ℝ))
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private theorem copula_boundary_one_zero (C : Copula 2) (i : Fin 2) :
    C.toMeasure {x | x i = 1} = 0 := by
  change C.toMeasure ((fun x : Fin 2 → I => x i) ⁻¹' ({1} : Set I)) = 0
  rw [C.measure_preimage_eval i (measurableSet_singleton (1:I))]
  simp

/-- Interior rectangle equality is sufficient, even when a density is unbounded
near any side or corner of the unit square. -/
theorem measure_eq_copula_of_interior_rectangles (C : Copula 2) (ν : Measure (Fin 2 → I))
    (hac : ν ≪ volume)
    (hrect : ∀ a b c d : I, 0 < (a:ℝ) → a ≤ b → (b:ℝ) < 1 →
      0 < (c:ℝ) → c ≤ d → (d:ℝ) < 1 →
      ν (Set.pi Set.univ (fun i : Fin 2 => Ioc (![a,c] i) (![b,d] i))) =
      C.toMeasure (Set.pi Set.univ (fun i : Fin 2 => Ioc (![a,c] i) (![b,d] i)))) :
    ν = C.toMeasure := by
  apply measure_eq_copula_of_positive_rectangles C ν hac
  intro a b c d ha hab hc hcd
  let s : Set (Fin 2 → I) := Set.pi Set.univ (fun i : Fin 2 => Ioc (![a,c] i) (![b,d] i))
  let S : ℕ → Set (Fin 2 → I) := fun n => Set.pi Set.univ
    (fun i : Fin 2 => Ioc (![a,c] i) (![min b (upperRectCutoff n),min d (upperRectCutoff n)] i))
  have hmono : Monotone S := by
    intro m n hmn x hx
    apply Set.mem_pi.mpr
    intro i hi
    have hh := (Set.mem_pi.mp hx) i hi
    fin_cases i
    · exact ⟨hh.1,hh.2.trans (min_le_min_left b (upperRectCutoff_mono hmn))⟩
    · exact ⟨hh.1,hh.2.trans (min_le_min_left d (upperRectCutoff_mono hmn))⟩
  have hsub : (⋃ n, S n) ⊆ s := by
    intro x hx
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_pi.mpr
    intro i hi
    have hh := (Set.mem_pi.mp hn) i hi
    fin_cases i
    · exact ⟨hh.1,hh.2.trans (min_le_left _ _)⟩
    · exact ⟨hh.1,hh.2.trans (min_le_left _ _)⟩
  have hdiff : s \ (⋃ n, S n) ⊆ {x | x 0 = 1} ∪ {x | x 1 = 1} := by
    intro x hx
    by_contra hn
    have hne : x 0 ≠ 1 ∧ x 1 ≠ 1 := by simpa using hn
    have h0 : (x 0:ℝ) < 1 := lt_of_le_of_ne (x 0).property.2 (fun h => hne.1 (Subtype.ext h))
    have h1 : (x 1:ℝ) < 1 := lt_of_le_of_ne (x 1).property.2 (fun h => hne.2 (Subtype.ext h))
    obtain ⟨n,hn0,hn1⟩ := ((upperRectCutoff_tendsto.eventually_const_lt h0).and
      (upperRectCutoff_tendsto.eventually_const_lt h1)).exists
    apply hx.2
    apply Set.mem_iUnion.mpr
    refine ⟨n,Set.mem_pi.mpr ?_⟩
    intro i hi
    have hh := (Set.mem_pi.mp hx.1) i hi
    fin_cases i
    · exact ⟨hh.1,le_min hh.2 hn0.le⟩
    · exact ⟨hh.1,le_min hh.2 hn1.le⟩
  have heq (μ : Measure (Fin 2 → I)) (h0 : μ {x | x 0 = 1} = 0) (h1 : μ {x | x 1 = 1} = 0) :
      μ s = μ (⋃ n, S n) :=
    (measure_eq_measure_of_null_sdiff hsub (measure_mono_null hdiff (measure_union_null h0 h1))).symm
  change ν s = C.toMeasure s
  rw [heq ν (hac (copula_boundary_one_zero (independence 2) 0))
    (hac (copula_boundary_one_zero (independence 2) 1)),
    heq C.toMeasure (copula_boundary_one_zero C 0) (copula_boundary_one_zero C 1),
    hmono.measure_iUnion, hmono.measure_iUnion]
  apply iSup_congr
  intro n
  by_cases hab' : a ≤ min b (upperRectCutoff n)
  · by_cases hcd' : c ≤ min d (upperRectCutoff n)
    · exact hrect a _ c _ ha hab' ((min_le_right _ _).trans_lt (upperRectCutoff_lt_one n))
        hc hcd' ((min_le_right _ _).trans_lt (upperRectCutoff_lt_one n))
    · have he : S n = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have hh := (Set.mem_pi.mp hx) 1 (by simp)
        exact hcd' (le_trans hh.1.le hh.2)
      simp [he]
  · have he : S n = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      have hh := (Set.mem_pi.mp hx) 0 (by simp)
      exact hab' (le_trans hh.1.le hh.2)
    simp [he]

end Verification
