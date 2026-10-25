import Papers.Rockel2026ExactBlest.Source.Potentials

/-! # Propositions 4.3 and 4.4: the potentials of the two regimes

The claims of Propositions 4.3 and 4.4 (the dual inequality and its equality
sets) and the well-definedness of `d_κ`, `κ`, `z_∓`, `R_b^∓`, `S_w` and of the
potentials (each potential's derivative is integrable), proved through
`Potentials` from the companion development. The article proves these
propositions by a computation that is not compiled, so the citation audit does
not restrict these proofs. -/

namespace Papers.Rockel2026ExactBlest.Source.Proofs
open Papers.Rockel2026ExactBlest.Source Papers.Rockel2026ExactBlest.Source.Bridge
open Proofread MeasureTheory Set
open scoped unitInterval
open Papers.Rockel2026ExactBlest (paper_dualA paper_contactA paper_dualB paper_contactB)

/-! ## Definitions -/

theorem defined18 : wellDefined18 := trivial

theorem defined24 : wellDefined24 := by
  intro b hb _
  have : (0 : ℝ) < 1 - b := by linarith [hb.2]
  positivity

theorem defined25 : wellDefined25 := by
  intro b hb _
  have : (0 : ℝ) < 1 - b := by linarith [hb.2]
  positivity

theorem defined26 : wellDefined26 := by
  intro w hw
  have : (0 : ℝ) < w := by linarith [hw.1]
  positivity

theorem defined27 : wellDefined27 := by
  intro w hw x hx
  refine ⟨by definedness [], (phiA_pieces hw hx (fun t ht => ite_eq_left ht)
    (fun t ht => (ite_eq_right (fun h => by linarith [h.2, ht.1])).trans (ite_eq_left ht))).1,
    by definedness []⟩

theorem defined28 : wellDefined28 := by
  intro w hw y hy
  refine ⟨by definedness [], (psiA_pieces hw hy (fun t ht => ite_eq_left ht)
    (fun t ht => (ite_eq_right (fun h => by linarith [h.2, ht.1])).trans (ite_eq_left ht))).1,
    by definedness []⟩

theorem defined29 : wellDefined29 := trivial

theorem defined30 : wellDefined30 := by
  unfold wellDefined30
  definedness []

theorem defined31 : wellDefined31 := trivial

theorem defined32 : wellDefined32 := by
  intro b hb _ h
  linarith [hb.2]

theorem defined33 : wellDefined33 := by
  intro b hb
  refine ⟨by norm_num, fun hA hB => (by linarith [hA.1, hB.2] : False).elim,
    fun hnA => ⟨by definedness [], fun hB => ?_, fun hnB _ => hb.elim hnA hnB⟩⟩
  intro x hx
  obtain ⟨hb0, hb1⟩ := hB
  refine ⟨by definedness [Or.inr ⟨hb0, hb1⟩], (phiB_pieces ⟨hb0, hb1⟩ hx (fun t ht => ite_eq_left ht)
    (fun t ht => (ite_eq_right (fun h => by linarith [h.2, ht.1])).trans (ite_eq_left ht))).1,
    by definedness [Or.inr ⟨hb0, hb1⟩]⟩

theorem defined34 : wellDefined34 := by
  intro b hb
  refine ⟨by norm_num, fun hA hB => (by linarith [hA.1, hB.2] : False).elim,
    fun hnA => ⟨by definedness [], fun hB => ?_, fun hnB _ => hb.elim hnA hnB⟩⟩
  intro y hy
  obtain ⟨hb0, hb1⟩ := hB
  have hzb := z_lt ⟨hb0, hb1⟩
  refine ⟨by definedness [Or.inr ⟨hb0, hb1⟩], (psiB_pieces ⟨hb0, hb1⟩ hy (fun t ht => ite_eq_left ht)
    (fun t ht => (ite_eq_right (fun h => by linarith [h.2, ht.1])).trans (ite_eq_left ht))
    (fun t ht => (ite_eq_right (fun h => by linarith [h.2, ht.1])).trans
      ((ite_eq_right (fun h => by linarith [h.2, ht.1])).trans (ite_eq_left ht)))).1,
    by definedness [Or.inr ⟨hb0, hb1⟩]⟩

/-! ## Proposition 4.3 -/

theorem unit_mem (x : I) : (0 : ℝ) ≤ x ∧ (x : ℝ) ≤ 1 := ⟨x.2.1, x.2.2⟩

theorem proof36 : obligation36 := by
  refine ⟨by unfold meaningful36; definedness [kappa_pos ⟨‹_›, ‹_›⟩, unitInterval.nonneg _, unitInterval.le_one _], fun w hw x y => ?_⟩
  rw [d_eq, varphi_eq hw (unit_mem x), psi_eq hw (unit_mem y), kappa_eq]
  exact paper_dualA w x y hw.1 hw.2.le (unit_mem x) (unit_mem y)

theorem proof37 : obligation37 := by
  refine ⟨by unfold meaningful37; definedness [kappa_pos ⟨‹_›, ‹_›⟩, unitInterval.nonneg _, unitInterval.le_one _], fun w hw hw' x y => ?_⟩
  have hc := paper_contactA w x y hw.1 hw.2 (unit_mem x) (unit_mem y)
  rw [sub_eq_zero] at hc
  rw [varphi_eq hw (unit_mem x), psi_eq hw (unit_mem y), d_eq, kappa_eq, hc, S_iff (unit_mem x)]
  constructor
  · rintro (h | h | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr h
    · linarith
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem proof38 : obligation38 := by
  refine ⟨by unfold meaningful38; definedness [kappa_pos ⟨‹_›, ‹_›⟩, unitInterval.nonneg _, unitInterval.le_one _], fun w hw hw' x y => ?_⟩
  subst hw'
  have hc := paper_contactA (1 / 2) x y hw.1 hw.2 (unit_mem x) (unit_mem y)
  rw [sub_eq_zero] at hc
  rw [varphi_eq hw (unit_mem x), psi_eq hw (unit_mem y), d_eq, kappa_eq, hc, S_iff (unit_mem x)]
  have hx1 := (unit_mem x).2
  constructor
  · rintro (h | h | ⟨-, h1, h2⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨⟨h1, hx1⟩, h2⟩
  · rintro ((h | h) | ⟨⟨h1, -⟩, h2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨rfl, h1, h2⟩)

/-! ## Proposition 4.4 -/

theorem proof39 : obligation39 := by
  refine ⟨by unfold meaningful39; definedness [kappa30_pos ⟨‹_›, ‹_›⟩, Or.inr ⟨‹_›, ‹_›⟩, unitInterval.nonneg _,
    unitInterval.le_one _], fun b hb x y => ?_⟩
  rw [d_eq, varphi33_eq hb (unit_mem x), psi34_eq hb (unit_mem y), kappa30_B hb]
  exact paper_dualB b x y hb.1 hb.2 (unit_mem x) (unit_mem y)

theorem proof40 : obligation40 := by
  refine ⟨by unfold meaningful40; definedness [kappa30_pos ⟨‹_›, ‹_›⟩, Or.inr ⟨‹_›, ‹_›⟩, unitInterval.nonneg _,
    unitInterval.le_one _], fun b hb x y => ?_⟩
  have hc := paper_contactB b x y hb.1 hb.2 (unit_mem x) (unit_mem y)
  rw [sub_eq_zero] at hc
  rw [varphi33_eq hb (unit_mem x), psi34_eq hb (unit_mem y), d_eq, kappa30_B hb, hc, Subtype.ext_iff,
    R_coe hb]

end Papers.Rockel2026ExactBlest.Source.Proofs
