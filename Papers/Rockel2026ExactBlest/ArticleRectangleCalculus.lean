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

end
end Papers.Rockel2026ExactBlest.ArticleOriginalProof
