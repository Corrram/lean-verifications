import Papers.Rockel2026ExactBlest.ArticleOriginalProof

open Set
namespace Papers.Rockel2026ExactBlest.ArticleOriginalProof
noncomputable section

-- The elementary calculus step used by both remaining rectangles: a function
-- which first increases and then decreases has its minimum at an endpoint.
private theorem endpoint_minimum {f g : ℝ → ℝ} {a c b x : ℝ}
    (hc : c ∈ Icc a b) (hx : x ∈ Icc a b)
    (hcont : ContinuousOn f (Icc a b))
    (hder : ∀ t ∈ Ioo a b, HasDerivAt f (g t) t)
    (hpos : ∀ t ∈ Ioo a c, 0 ≤ g t)
    (hneg : ∀ t ∈ Ioo c b, g t ≤ 0) :
    min (f a) (f b) ≤ f x := by
  have hm : MonotoneOn f (Icc a c) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a c)
      (hcont.mono (Icc_subset_Icc le_rfl hc.2))
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t ⟨ht.1,lt_of_lt_of_le ht.2 hc.2⟩).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact hpos t ht
  have ha : AntitoneOn f (Icc c b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc c b)
      (hcont.mono (Icc_subset_Icc hc.1 le_rfl))
    · intro t ht
      rw [interior_Icc] at ht
      exact (hder t ⟨lt_of_le_of_lt hc.1 ht.1,ht.2⟩).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact hneg t ht
  by_cases hxc : x ≤ c
  · exact (min_le_left _ _).trans (hm ⟨le_rfl,hc.1⟩ ⟨hx.1,hxc⟩ hx.1)
  · exact (min_le_right _ _).trans (ha ⟨(not_le.mp hxc).le,hx.2⟩ ⟨hc.2,le_rfl⟩ hx.2)

theorem continuous_deltaA_x (w z : ℝ) : Continuous (fun x => deltaA w x z) := by
  unfold deltaA paperPhiA
  apply ((continuous_phiA (1-w)).add_const (paperPsiA w z)).sub
  unfold cost
  fun_prop

theorem continuous_deltaA_z (w x : ℝ) : Continuous (fun z => deltaA w x z) := by
  unfold deltaA paperPsiA
  apply ((continuous_psiA (1-w)).const_add (paperPhiA w x)).sub
  unfold cost
  fun_prop

theorem graph_third_comparison (w x z : ℝ) (hw : 1/2 ≤ w) (hw1 : w ≤ 1)
    (hx : x ∈ Icc 0 (1-w)) (hz : z ∈ Icc 0 w) :
    deltaA w (1-w) z ≤ deltaA w x z := by
  have ha : AntitoneOn (fun t => deltaA w t z) (Icc 0 (1-w)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (1-w))
      (continuous_deltaA_x w z).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (graph_derivative_00 w t z (by linarith) ht.2).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact graph_derivative_00_nonpos w t z hw hw1 ht.2.le hz.1 hz.2
  exact ha hx ⟨by linarith,le_rfl⟩ hx.2

theorem graph_third_endpoints (w : ℝ) (hw : 1/2 ≤ w) :
    deltaA w (1-w) 0 = 0 ∧ deltaA w (1-w) w = 0 := by
  constructor
  · rw [graph_rectangle_10 w (1-w) 0 (by linarith) le_rfl (by linarith)]
    ring
  · rw [graph_rectangle_01 w (1-w) w (by linarith) le_rfl le_rfl]
    ring

theorem graph_third_edge_minimum (w z : ℝ) (hw : 1/2 ≤ w) (hw1 : w ≤ 1)
    (hz : z ∈ Icc 0 w) :
    min (deltaA w (1-w) 0) (deltaA w (1-w) w) ≤ deltaA w (1-w) z := by
  apply endpoint_minimum (g := fun t => -(1-w)*t*(3*t-2*w)/w)
    (c := 2*w/3) (by constructor <;> linarith) hz (continuous_deltaA_z w (1-w)).continuousOn
  · intro t ht
    exact graph_edge_derivative_z w t (by linarith) ht.2
  · intro t ht
    apply div_nonneg _ (by linarith)
    apply mul_nonneg_of_nonpos_of_nonpos
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) ht.1.le
    · linarith [ht.2]
  · intro t ht
    apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
    apply mul_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [ht.1])
    · linarith [ht.1]

theorem graph_fourth_comparison (w x z : ℝ) (hw : 1/2 ≤ w) (hw1 : w ≤ 1)
    (hx : x ∈ Icc (1-w) 1) (hz : z ∈ Icc w 1) :
    deltaA w x w ≤ deltaA w x z := by
  have hm : MonotoneOn (fun t => deltaA w x t) (Icc w 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc w 1)
      (continuous_deltaA_z w x).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (graph_derivative_11 w x t (by linarith) ht.1).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact graph_derivative_11_nonneg w x t hw hw1 hx.1 hx.2 ht.1.le
  exact hm ⟨le_rfl,hw1⟩ hz hz.1

theorem graph_fourth_endpoints (w : ℝ) (hw : 1/2 ≤ w) (_hw1 : w ≤ 1) :
    deltaA w (1-w) w = 0 ∧ deltaA w 1 w = 0 := by
  refine ⟨(graph_third_endpoints w hw).2,?_⟩
  rw [graph_rectangle_10 w 1 w (by linarith) (by linarith) le_rfl]
  ring

theorem graph_fourth_edge_minimum (w x : ℝ) (hw : 1/2 ≤ w) (_hw1 : w ≤ 1)
    (hx : x ∈ Icc (1-w) 1) :
    min (deltaA w (1-w) w) (deltaA w 1 w) ≤ deltaA w x w := by
  apply endpoint_minimum (g := fun t => (1-t)*(2*w-1)*(3-2*w-3*t)/(2*w))
    (c := (3-2*w)/3) (by constructor <;> linarith) hx (continuous_deltaA_x w w).continuousOn
  · intro t ht
    exact graph_edge_derivative_x w t (by linarith) ht.1
  · intro t ht
    apply div_nonneg _ (by linarith)
    apply mul_nonneg
    · exact mul_nonneg (by linarith [ht.2]) (by linarith)
    · linarith [ht.2]
  · intro t ht
    apply div_nonpos_of_nonpos_of_nonneg _ (by linarith)
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact mul_nonneg (by linarith [ht.2]) (by linarith)
    · linarith [ht.1]

-- The strict versions justify the printed assertion that no other contact
-- points occur in the interiors of the last two rectangles.
theorem graph_third_strict_comparison (w x z : ℝ) (hw : 1/2 ≤ w) (hw1 : w < 1)
    (hx : x ∈ Ico 0 (1-w)) (hz : z ∈ Icc 0 w) :
    deltaA w (1-w) z < deltaA w x z := by
  have ha : StrictAntiOn (fun t => deltaA w t z) (Icc 0 (1-w)) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 (1-w))
      (continuous_deltaA_x w z).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (graph_derivative_00 w t z (by linarith) ht.2).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      apply div_neg_of_neg_of_pos _ (by linarith)
      apply mul_neg_of_neg_of_pos
      · linarith [ht.2,hz.2]
      · have hA : 0 ≤ w*(2*w-1) := mul_nonneg (by linarith) (by linarith)
        have hB : 0 ≤ (3-2*w)*z := mul_nonneg (by linarith) hz.1
        have hC : 0 < (3+2*w)*(1-w-t) := mul_pos (by linarith) (by linarith [ht.2])
        nlinarith
  exact ha ⟨hx.1,hx.2.le⟩ ⟨by linarith,le_rfl⟩ hx.2

theorem graph_fourth_strict_comparison (w x z : ℝ) (hw : 1/2 ≤ w) (hw1 : w < 1)
    (hx : x ∈ Icc (1-w) 1) (hz : z ∈ Ioc w 1) :
    deltaA w x w < deltaA w x z := by
  have hm : StrictMonoOn (fun t => deltaA w x t) (Icc w 1) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc w 1)
      (continuous_deltaA_z w x).continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (graph_derivative_11 w x t (by linarith) ht.1).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      apply div_pos _ (by linarith)
      apply mul_pos
      · linarith [hx.1,ht.1]
      · have hA : 0 < w*(2-w-x) := mul_pos (by linarith) (by linarith [hx.2])
        have hB : 0 < (3-w)*(t-w) := mul_pos (by linarith) (by linarith [ht.1])
        nlinarith
  exact hm ⟨le_rfl,hw1.le⟩ ⟨hz.1.le,hz.2⟩ hz.1

theorem graph_third_edge_factor (w z : ℝ) (hw : 1/2 ≤ w) (hz : z ≤ w) :
    deltaA w (1-w) z = (1-w)*z^2*(w-z)/w := by
  rw [graph_rectangle_10 w (1-w) z (by linarith) le_rfl hz]
  ring

theorem graph_fourth_edge_factor (w x : ℝ) (hw : 1/2 ≤ w) (hx : 1-w ≤ x) :
    deltaA w x w = (1-x)^2*(2*w-1)*(x+w-1)/(2*w) := by
  rw [graph_rectangle_10 w x w (by linarith) hx le_rfl]
  ring

theorem graph_first_contact (w x z : ℝ) (hw : 1/2 ≤ w) (hw1 : w < 1)
    (hx : x ∈ Icc (1-w) 1) (hz : z ∈ Icc 0 w) :
    deltaA w x z = 0 ↔ z = x+w-1 ∨
      (x = 1-w ∧ z = w) ∨ (w = 1/2 ∧ z = w) := by
  rw [graph_rectangle_10 w x z (by linarith) hx.1 hz.2,
    div_eq_zero_iff,mul_eq_zero,sq_eq_zero_iff]
  have hden : 2*w ≠ 0 := by linarith
  simp only [hden,or_false]
  have hA : 0 ≤ (2*w-1)*(x+w-1) := mul_nonneg (by linarith) (by linarith [hx.1])
  have hB : 0 ≤ 2*(1-w)*(w-z) := mul_nonneg (by linarith) (by linarith [hz.2])
  constructor
  · rintro (hs|hf)
    · exact Or.inl (by linarith)
    · have hb : z = w := by nlinarith
      have hp : (2*w-1)*(x+w-1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hp with ha|ha
      · exact Or.inr (Or.inr ⟨by linarith,hb⟩)
      · exact Or.inr (Or.inl ⟨by linarith,hb⟩)
  · rintro (h|⟨h,hz⟩|⟨h,hz⟩)
    · exact Or.inl (by linarith)
    · right
      rw [h,hz]
      ring
    · right
      rw [hz,h]
      norm_num

theorem graph_third_contact (w x z : ℝ) (hw : 1/2 ≤ w) (hw1 : w < 1)
    (hx : x ∈ Icc 0 (1-w)) (hz : z ∈ Icc 0 w) :
    deltaA w x z = 0 ↔ x = 1-w ∧ (z = 0 ∨ z = w) := by
  have he : deltaA w (1-w) z = 0 ↔ z = 0 ∨ z = w := by
    rw [graph_third_edge_factor w z hw hz.2, div_eq_zero_iff, mul_eq_zero, mul_eq_zero]
    have ha : 1-w ≠ 0 := by linarith
    have hb : w ≠ 0 := by linarith
    simp only [ha,hb,false_or,or_false,sq_eq_zero_iff,sub_eq_zero]
    rw [eq_comm (a := w)]
  constructor
  · intro h
    have hnonneg := (graph_third_endpoints w hw)
    have hmin := graph_third_edge_minimum w z hw hw1.le hz
    rw [hnonneg.1,hnonneg.2,min_self] at hmin
    have hxe : x = 1-w := by
      by_contra hne
      have hs := graph_third_strict_comparison w x z hw hw1
        ⟨hx.1,lt_of_le_of_ne hx.2 hne⟩ hz
      linarith
    exact ⟨hxe,he.mp (hxe ▸ h)⟩
  · rintro ⟨rfl,hz⟩
    exact he.mpr hz

theorem graph_fourth_contact (w x z : ℝ) (hw : 1/2 ≤ w) (hw1 : w < 1)
    (hx : x ∈ Icc (1-w) 1) (hz : z ∈ Icc w 1) :
    deltaA w x z = 0 ↔ z = w ∧ (x = 1-w ∨ x = 1 ∨ w = 1/2) := by
  have he : deltaA w x w = 0 ↔ x = 1-w ∨ x = 1 ∨ w = 1/2 := by
    rw [graph_fourth_edge_factor w x hw hx.1,div_eq_zero_iff,mul_eq_zero,mul_eq_zero]
    have hden : 2*w ≠ 0 := by linarith
    simp only [hden,or_false,sq_eq_zero_iff]
    constructor
    · rintro ((h|h)|h)
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inr (Or.inr (by linarith))
      · exact Or.inl (by linarith)
    · rintro (h|h|h)
      · exact Or.inr (by linarith)
      · exact Or.inl (Or.inl (by linarith))
      · exact Or.inl (Or.inr (by linarith))
  constructor
  · intro h
    have hends := graph_fourth_endpoints w hw hw1.le
    have hmin := graph_fourth_edge_minimum w x hw hw1.le hx
    rw [hends.1,hends.2,min_self] at hmin
    have hze : z = w := by
      by_contra hne
      have hs := graph_fourth_strict_comparison w x z hw hw1 hx
        ⟨lt_of_le_of_ne hz.1 (Ne.symm hne),hz.2⟩
      linarith
    exact ⟨hze,he.mp (hze ▸ h)⟩
  · rintro ⟨rfl,hx⟩
    exact he.mpr hx

end
end Papers.Rockel2026ExactBlest.ArticleOriginalProof
