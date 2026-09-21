import Papers.AnsariRockelSteinmassl2026RhoGamma.ThetaInputArcs

/-! # Global continuity through the source's countable theta junctions -/

open ProbabilityTheory Copula.RankRegion Set
open scoped unitInterval Topology

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

private theorem locallyFinite_nat_intervals : LocallyFinite (fun N : ℕ => Icc (N : ℝ) (N + 1)) := by
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt x
  refine ⟨Iio (n : ℝ), Iio_mem_nhds hn, (Set.finite_Iio n).subset ?_⟩
  rintro N ⟨y, hy, hyn⟩
  exact_mod_cast (show (N : ℝ) < n from hy.1.trans_lt hyn)

/-- The three auxiliary source formulas are continuous at all integer and midpoint junctions. -/
theorem continuous_thetaInput : ContinuousOn thetaInput (Ioi (0 : ℝ)) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let tiles (N : ℕ) : Set (Ioi (0 : ℝ)) := Subtype.val ⁻¹' Icc (N : ℝ) (N + 1)
  have hlf : LocallyFinite tiles := locallyFinite_nat_intervals.preimage_continuous continuous_subtype_val
  have hcov : (⋃ N, tiles N) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    refine ⟨⌊(x : ℝ)⌋₊, ?_⟩
    exact ⟨Nat.floor_le x.property.le, (Nat.lt_floor_add_one (x : ℝ)).le⟩
  apply hlf.continuous hcov (fun N => isClosed_Icc.preimage continuous_subtype_val)
  intro N
  by_cases hN : N = 0
  · subst N
    have hc : Continuous (fun x : Ioi (0 : ℝ) => (![1 / 2, 1 / 4, 3 / 8 - (1 / (x : ℝ)) / 2] : Fin 3 → ℝ)) := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_const
      · exact continuous_const
      · have hi : Continuous (fun x : Ioi (0 : ℝ) => 1 / (x : ℝ)) :=
          continuous_const.div continuous_subtype_val (fun x => ne_of_gt x.property)
        exact continuous_const.sub (hi.div_const 2)
    apply hc.continuousOn.congr
    intro x hx
    have hx1 : (x : ℝ) ≤ 1 := by simpa only [tiles, mem_preimage, Nat.cast_zero, zero_add] using hx.2
    change thetaInput (x : ℝ) = _
    simp only [thetaInput, thetaMean, thetaSquare, thetaOffset, hx1, ite_true]
  · have hc : Continuous (fun x : Ioi (0 : ℝ) => inputArc N (1 / (x : ℝ))) :=
      (continuous_inputArc N (Nat.pos_of_ne_zero hN)).comp
        (continuous_const.div continuous_subtype_val (fun x => ne_of_gt x.property))
    apply hc.continuousOn.congr
    intro x hx
    exact thetaInput_on_interval N (Nat.pos_of_ne_zero hN) hx

/-- Theorem 1.1: continuity of the source boundary coordinates for every positive theta. -/
theorem continuous_theta_coordinates : ContinuousOn (fun theta : ℝ => (thetaG theta, thetaP theta)) (Ioi 0) := by
  have hm : ContinuousOn thetaMean (Ioi (0 : ℝ)) := continuousOn_pi.mp continuous_thetaInput 0
  have hq : ContinuousOn thetaSquare (Ioi (0 : ℝ)) := continuousOn_pi.mp continuous_thetaInput 1
  have hc : ContinuousOn thetaOffset (Ioi (0 : ℝ)) := continuousOn_pi.mp continuous_thetaInput 2
  have ha : ContinuousOn thetaAlpha (Ioi (0 : ℝ)) := by
    unfold thetaAlpha
    exact (continuousOn_const.add (continuousOn_const.add
      ((continuousOn_const.mul (continuousOn_id.pow 2)).mul hc)).sqrt).div_const 2
  have ht : ContinuousOn thetaT (Ioi (0 : ℝ)) := by
    unfold thetaT
    apply continuousOn_const.div (continuousOn_id.add ha)
    intro theta htheta
    have hh := Real.sqrt_nonneg (1 + 2 * theta ^ 2 * thetaOffset theta)
    dsimp [thetaAlpha]
    linarith [show 0 < theta from htheta]
  have hA : ContinuousOn thetaA (Ioi (0 : ℝ)) := ha.mul ht
  have hZ : ContinuousOn thetaZ (Ioi (0 : ℝ)) := continuousOn_id.mul ht
  apply ContinuousOn.prodMk
  · exact (continuousOn_const.sub (continuousOn_const.mul (hA.pow 2))).sub ((hZ.pow 2).mul hm)
  · exact (continuousOn_const.sub (continuousOn_const.mul (hA.pow 3))).sub
      ((continuousOn_const.mul (hZ.pow 3)).mul hq)

end Papers.AnsariRockelSteinmassl2026RhoGamma
