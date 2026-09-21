import Papers.AnsariRockelSteinmassl2026RhoGamma.ShuffleSupport
import Copula.Order.Survival

/-! # Identification with the paper's five-piece measure-preserving graph map -/

open MeasureTheory ProbabilityTheory Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

/-- The five cases of Example 3.10, with exactly the source's endpoint convention. -/
noncomputable def fivePieceMapReal (d u : ℝ) : ℝ :=
  if u < d / 2 then u + d / 2
  else if u < d then u - d / 2
  else if u ≤ 1 - d then 1 - u
  else if u < 1 - d / 2 then u + d / 2
  else u - d / 2

private theorem fivePiece_mem {d : ℝ} (hd : d ∈ Set.Icc 0 (1 / 2 : ℝ)) (u : I) :
    fivePieceMapReal d u ∈ Set.Icc 0 1 := by
  rcases hd with ⟨hd0, hd1⟩
  rcases u.property with ⟨hu0, hu1⟩
  unfold fivePieceMapReal
  split_ifs <;> constructor <;> linarith

noncomputable def fivePieceMap (d : ℝ) (hd : d ∈ Set.Icc 0 (1 / 2 : ℝ)) (u : I) : I :=
  ⟨fivePieceMapReal d u, fivePiece_mem hd u⟩

private theorem measurable_fivePieceMap (d : ℝ) (hd : d ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    Measurable (fivePieceMap d hd) := by
  apply Measurable.subtype_mk
  change Measurable (fun u : I => fivePieceMapReal d u)
  unfold fivePieceMapReal
  apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop)
  apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop)
  apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const) (by fun_prop)
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop) (by fun_prop)

private theorem support_graph {d : ℝ} (hd : 0 < d) (hd1 : d < 1 / 2) (x : Fin 2 → I)
    (hs : FivePieceSupport d x) (hmid : (x 0 : ℝ) ≠ d) (hmid' : (x 0 : ℝ) ≠ 1 - d)
    (hlo : (x 0 : ℝ) ≠ d / 2) (hhi : (x 0 : ℝ) ≠ 1 - d / 2) :
    (x 1 : ℝ) = fivePieceMapReal d (x 0) := by
  rcases (x 0).property with ⟨hu0, hu1⟩
  rcases (x 1).property with ⟨hv0, hv1⟩
  rcases hs with ⟨hl, hr, hv⟩ | ⟨hu, hv, ha⟩ | ⟨hu, hv, ha⟩
  · unfold fivePieceMapReal
    split_ifs <;> first | exact hv | exfalso; linarith
  · have hu' : (x 0 : ℝ) < d := lt_of_le_of_ne hu hmid
    rcases lt_or_gt_of_ne hlo with hcut | hcut
    all_goals
      rcases (abs_eq (by positivity : 0 ≤ d / 2)).mp ha with h | h
      all_goals unfold fivePieceMapReal; split_ifs <;> linarith
  · have hu' : 1 - d < (x 0 : ℝ) := lt_of_le_of_ne hu hmid'.symm
    rcases lt_or_gt_of_ne hhi with hcut | hcut
    all_goals
      rcases (abs_eq (by positivity : 0 ≤ d / 2)).mp ha with h | h
      all_goals unfold fivePieceMapReal; split_ifs <;> linarith

private theorem ae_coe_eval_ne (C : Copula 2) (r : ℝ) :
    ∀ᵐ x ∂C.toMeasure, (x 0 : ℝ) ≠ r := by
  by_cases hr : r ∈ Set.Icc (0 : ℝ) 1
  · filter_upwards [C.ae_eval_ne 0 ⟨r, hr⟩] with x hx
    exact fun he => hx (Subtype.ext he)
  · filter_upwards [] with x
    exact fun he => hr (he ▸ (x 0).property)

/-- The five-segment support identifies the source's graph map almost everywhere. -/
theorem elementary_shuffle_graph {s : ℝ} (hs : 1 ≤ s) :
    let A := RhoGamma.AuxiliaryCertificate.halfShift s hs
    ∀ᵐ x ∂A.copula.toMeasure, (x 1 : ℝ) = fivePieceMapReal (A.z / 2) (x 0) := by
  dsimp only
  let A := RhoGamma.AuxiliaryCertificate.halfShift s hs
  have hz : A.z < 1 := by linarith [A.a_pos, A.a_add_z]
  filter_upwards [elementary_shuffle_support hs,
    ae_coe_eval_ne A.copula (A.z / 2), ae_coe_eval_ne A.copula (1 - A.z / 2),
    ae_coe_eval_ne A.copula (A.z / 2 / 2), ae_coe_eval_ne A.copula (1 - A.z / 2 / 2)]
      with x hx h1 h2 h3 h4
  exact support_graph (by linarith [A.z_pos]) (by linarith) x hx h1 h2 h3 h4

/-- Example 3.10: equality of probability measures with the uniform graph construction. -/
theorem elementary_shuffle_law {s : ℝ} (hs : 1 ≤ s)
    (hd : (RhoGamma.AuxiliaryCertificate.halfShift s hs).z / 2 ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    let A := RhoGamma.AuxiliaryCertificate.halfShift s hs
    A.copula.toMeasure = volume.map (fun u : I => ![u, fivePieceMap (A.z / 2) hd u]) := by
  dsimp only
  let A := RhoGamma.AuxiliaryCertificate.halfShift s hs
  rw [← A.copula.map_eval 0, Measure.map_map
    (show Measurable (fun u : I => ![u, fivePieceMap (A.z / 2) hd u]) by
      apply Measurable.of_eval
      intro i
      fin_cases i
      · exact measurable_id
      · exact measurable_fivePieceMap _ hd) (measurable_pi_apply 0)]
  conv_lhs => rw [← Measure.map_id (μ := A.copula.toMeasure)]
  apply Measure.map_congr
  filter_upwards [elementary_shuffle_graph hs] with x hx
  funext i
  fin_cases i
  · rfl
  · exact Subtype.ext hx

/-- The exact piecewise map preserves the uniform law. -/
theorem elementary_shuffle_measurePreserving {s : ℝ} (hs : 1 ≤ s)
    (hd : (RhoGamma.AuxiliaryCertificate.halfShift s hs).z / 2 ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    MeasurePreserving (fivePieceMap ((RhoGamma.AuxiliaryCertificate.halfShift s hs).z / 2) hd) := by
  let A := RhoGamma.AuxiliaryCertificate.halfShift s hs
  refine ⟨measurable_fivePieceMap _ hd, ?_⟩
  have h := A.copula.map_eval 1
  rw [elementary_shuffle_law hs hd, Measure.map_map (measurable_pi_apply 1)
    (show Measurable (fun u : I => ![u, fivePieceMap (A.z / 2) hd u]) by
      apply Measurable.of_eval
      intro i
      fin_cases i
      · exact measurable_id
      · exact measurable_fivePieceMap _ hd)] at h
  exact h

end Papers.AnsariRockelSteinmassl2026RhoGamma
