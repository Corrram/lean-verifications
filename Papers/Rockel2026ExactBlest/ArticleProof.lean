import Papers.Rockel2026ExactBlest.ArticleCalculus
import Papers.Rockel2026ExactBlest.ArticleBridge

namespace Papers.Rockel2026ExactBlest.ArticleProof
open Companion MeasureTheory ProbabilityTheory Set
open Papers.Rockel2026XiBlest
open scoped unitInterval
open Ty
set_option linter.unusedSimpArgs false

abbrev cop : Ty := .base "Copula"
abbrev realfun : Ty := real ⇒ₘ real
noncomputable abbrev extremizer := paperD Copula.unitHalf
noncomputable def tent (u : ℝ) := min (2*u) (2-2*u)
noncomputable def vee (u : ℝ) := |2*u-1|
def OnGraph (C : Copula 2) (f : ℝ → ℝ) : Prop :=
  ∀ᵐ x ∂C.toMeasure, (x 1 : ℝ) = f (x 0)

theorem extremizer_values : extremizer.spearmanRho = 0 ∧ blestNu extremizer = 1/4 := by
  rw [(paperD_values _).1, (paperD_values _).2]
  norm_num [Copula.unitHalf]

theorem extremizer_graph : OnGraph extremizer tent := by
  simpa only [OnGraph, extremizer, paperD_half, tent] using rho_midpoint_original_graph

theorem survival_graph : OnGraph extremizer.survivalCopula vee := by
  simpa only [OnGraph, extremizer, paperD_half, vee] using rho_midpoint_reflected_graph

noncomputable def tentUnit (u : I) : I := ⟨tent u, by
  constructor
  · exact le_min (by linarith [u.property.1]) (by linarith [u.property.2])
  · apply min_le_iff.mpr
    rcases le_total (u : ℝ) (1/2) with h | h
    · left; linarith
    · right; linarith⟩

/-- The readable description of D is a law, not an arbitrary name for an extremizer. -/
theorem extremizer_definition : extremizer.toMeasure =
    (volume : Measure I).map (fun u => ![u, tentUnit u]) := by
  apply dual_certificate_graph _ _ (by unfold tentUnit tent; fun_prop) ∅ ∅
  filter_upwards [extremizer_graph] with x hx
  exact Or.inl (Subtype.ext hx)

-- The paper's derivation from the exact region, rather than the existing transport bound.
theorem bound_from_region (C : Copula 2)
    (hgap : ∀ r ∈ Icc (-1 : ℝ) 1, rhoBoundary r - r ≤ 1/4) :
    |blestNu C - C.spearmanRho| ≤ 1/4 := by
  have h := (rho_fibre_complete C.spearmanRho (blestNu C)).mp ⟨C, rfl, rfl⟩
  have hg := hgap _ h.1
  exact abs_le.mpr ⟨by linarith [h.2.1], by linarith [h.2.2]⟩

theorem maximum_from_region (C : Copula 2)
    (hgap : ∀ r ∈ Icc (-1 : ℝ) 1,
      rhoBoundary r - r ≤ 1/4 ∧ (rhoBoundary r - r = 1/4 ↔ r = 0)) :
    blestNu C - C.spearmanRho = 1/4 ↔ C = extremizer := by
  constructor
  · intro he
    have h := (rho_fibre_complete C.spearmanRho (blestNu C)).mp ⟨C, rfl, rfl⟩
    have hg := hgap _ h.1
    have hz : C.spearmanRho = 0 := hg.2.mp (by linarith [h.2.2])
    apply paper_rho_upper_unique Copula.unitHalf C
    · exact hz.trans extremizer_values.1.symm
    · rw [hz]
      norm_num [rhoBoundary]
      linarith
  · rintro rfl
    rw [extremizer_values.1, extremizer_values.2]; norm_num

theorem minimum_from_survival (C : Copula 2)
    (hmax : ∀ D : Copula 2, blestNu D - D.spearmanRho = 1/4 ↔ D = extremizer) :
    blestNu C - C.spearmanRho = -(1/4) ↔ C = extremizer.survivalCopula := by
  have h := hmax C.survivalCopula
  rw [nu_survival, Copula.spearmanRho_survivalCopula] at h
  constructor
  · intro he
    have hs := h.mp (by linarith)
    simpa using congrArg Copula.survivalCopula hs
  · intro he
    have hs : C.survivalCopula = extremizer := by simp [he]
    have := h.mpr hs
    linarith

inductive Symbol : Ty → Type where
  | rho : Symbol (cop ⇒ₘ real)
  | nu : Symbol (cop ⇒ₘ real)
  | Phi : Symbol realfun
  | negBranch : Symbol realfun
  | posBranch : Symbol realfun
  | tentMap : Symbol realfun
  | veeMap : Symbol realfun
  | power : Symbol (real ⇒ₘ real ⇒ₘ real)
  | minimum : Symbol (real ⇒ₘ real ⇒ₘ real)
  | cdf : Symbol (cop ⇒ₘ unit ⇒ₘ unit ⇒ₘ real)
  | reflectUnit : Symbol (unit ⇒ₘ unit)
  | derivative : Symbol (realfun ⇒ₘ real ⇒ₘ real ⇒ₘ prop)
  | increasing : Symbol (realfun ⇒ₘ real ⇒ₘ real ⇒ₘ prop)
  | decreasing : Symbol (realfun ⇒ₘ real ⇒ₘ real ⇒ₘ prop)
  | D : Symbol cop
  | survival : Symbol (cop ⇒ₘ cop)
  | graph : Symbol (cop ⇒ₘ realfun ⇒ₘ prop)

noncomputable def model : Model Symbol where
  base _ := Copula 2
  symbol
    | .rho => Copula.spearmanRho
    | .nu => blestNu
    | .Phi => rhoBoundary
    | .negBranch => leftGap
    | .posBranch => rightGap
    | .power => Real.rpow
    | .minimum => min
    | .cdf => fun C u v => C.cdf ![u,v]
    | .reflectUnit => unitInterval.symm
    | .derivative => fun f r d => HasDerivAt f d r
    | .increasing => fun f a b => StrictMonoOn f (Icc a b)
    | .decreasing => fun f a b => StrictAntiOn f (Icc a b)
    | .D => extremizer
    | .survival => Copula.survivalCopula
    | .tentMap => tent
    | .veeMap => vee
    | .graph => OnGraph
open Symbol

def leftDefinition : Expr Symbol [real] real :=
  [math| r |- r+1-\frac{3}{4}*\power(1+r,\frac{4}{3})]
def rightDefinition : Expr Symbol [real] real :=
  [math| r |- 1-r-\frac{3}{4}*\power(1-r,\frac{4}{3})]
theorem left_definition (r : ℝ) : leftDefinition.eval model (r,()) = leftGap r := by
  simp [leftDefinition, Expr.eval, model, Var.get, leftGap]
theorem right_definition (r : ℝ) : rightDefinition.eval model (r,()) = rightGap r := by
  simp [rightDefinition, Expr.eval, model, Var.get, rightGap]

def tentDefinition : Expr Symbol [real] real := [math| u |- \minimum(2*u,2-2*u)]
def veeDefinition : Expr Symbol [real] real := [math| u |- \abs{2*u-1}]
theorem tent_definition (u : ℝ) : tentDefinition.eval model (u,()) = tent u := rfl
theorem vee_definition (u : ℝ) : veeDefinition.eval model (u,()) = vee u := by
  simp [veeDefinition, Expr.eval, model, Var.get, vee]
def survivalDefinition : Expr Symbol [unit,unit,cop] real :=
  [math| C,u,v |- \real{u}+\real{v}-1+\cdf(C,\reflectUnit(u),\reflectUnit(v))]
theorem survival_definition (C : Copula 2) (u v : I) :
    survivalDefinition.eval model (v,u,C,()) = C.survivalCopula.cdf ![u,v] := by
  simpa [survivalDefinition, Expr.eval, model, Var.get] using (C.cdf_survivalCopula u v).symm

/-- Each displayed assertion is a typed expression, including derivative existence,
strict monotonicity, all equality cases, attainment, and the support graphs. -/
def corollaryProof : Argument Symbol [] := [proof|
  Have Forall r : real. (0-1 \le r \land r \le 0) \implies \Phi(r)-r = \negBranch(r);
  Have Forall r : real. (0 \le r \land r \le 1) \implies \Phi(r)-r = \posBranch(r);
  Have Forall r : real. (0-1 < r \land r < 0) \implies \derivative(\negBranch,r,1-\power(1+r,\frac{1}{3}));
  Have Forall r : real. (0-1 \le r \land r < 0) \implies 0 < 1-\power(1+r,\frac{1}{3});
  Have Forall r : real. (0 < r \land r < 1) \implies \derivative(\posBranch,r,\power(1-r,\frac{1}{3})-1);
  Have Forall r : real. (0 < r \land r \le 1) \implies \power(1-r,\frac{1}{3})-1 < 0;
  Have \increasing(\negBranch,0-1,0) \land \decreasing(\posBranch,0,1);
  Have Forall r : real. (0-1 \le r \land r \le 1) \implies
    (\Phi(r)-r \le \frac{1}{4} \land (\Phi(r)-r = \frac{1}{4} \iff r=0));
  Have \rho(\D)=0 \land \nu(\D)=\frac{1}{4};
  Have Forall C : cop. \nu(C)-\rho(C)=\frac{1}{4} \iff C=\D;
  Have \graph(\D,\tentMap);
  Have Forall C : cop. \nu(\survival(C))-\rho(\survival(C)) = \rho(C)-\nu(C);
  Have Forall C : cop. \nu(C)-\rho(C)=0-\frac{1}{4} \iff C=\survival(\D);
  Have \graph(\survival(\D),\veeMap);
  Fix C : cop named "C";
  Have \abs{\nu(C)-\rho(C)} \le \frac{1}{4};
  Conclude \abs{\nu(C)-\rho(C)} \le \frac{1}{4} \land
    (\nu(C)-\rho(C)=\frac{1}{4} \iff C=\D) \land
    (\nu(C)-\rho(C)=0-\frac{1}{4} \iff C=\survival(\D)) \land
    (\rho(\D)=0 \land \nu(\D)=\frac{1}{4}) \land
    (\graph(\D,\tentMap) \land \graph(\survival(\D),\veeMap))]

theorem corollary_valid : corollaryProof.Valid model (fun _ => True) := by
  simp only [corollaryProof, Argument.Valid, Argument.goal, Expr.eval, Var.get, model,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, zero_sub, cop, realfun, Ty.denote]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ r hr; exact left_formula r hr.2
  · intro _ _ r hr; exact right_formula r hr.1
  · intro _ _ r _; exact left_derivative r
  · intro _ _ r hr; exact left_derivative_positive r hr
  · intro _ _ r _; exact right_derivative r
  · intro _ _ r hr; exact right_derivative_negative r hr
  · intro _ _; exact ⟨left_increasing, right_decreasing⟩
  · intro _ _ r hr; exact gap_maximum r hr
  · intro _ _; exact extremizer_values
  · intro _ h C; exact maximum_from_region C h.1.2
  · intro _ _; exact extremizer_graph
  · intro _ _ C; rw [nu_survival, Copula.spearmanRho_survivalCopula]; ring
  · intro _ h C; exact minimum_from_survival C h.1.1.2
  · intro _ _; exact survival_graph
  · rintro ⟨C,⟨⟩⟩ h
    exact bound_from_region C (fun r hr => (h.1.1.1.1.1.1.2 r hr).1)
  · rintro ⟨C,⟨⟩⟩ h
    exact ⟨h.2, h.1.1.1.1.1.2 C, h.1.1.2 C, h.1.1.1.1.1.1.2,
      h.1.1.1.1.2, h.1.2⟩

theorem corollary_verified : corollaryProof.goal.eval model () :=
  corollaryProof.sound model _ corollary_valid () trivial

def NativeStatement : Prop := ∀ C : Copula 2,
  |blestNu C - C.spearmanRho| ≤ 1/4 ∧
  (blestNu C - C.spearmanRho = 1/4 ↔ C = extremizer) ∧
  (blestNu C - C.spearmanRho = -(1/4) ↔ C = extremizer.survivalCopula) ∧
  (extremizer.spearmanRho = 0 ∧ blestNu extremizer = 1/4) ∧
  (OnGraph extremizer tent ∧ OnGraph extremizer.survivalCopula vee)

/-- Definitional correspondence; the proved inequality is not used here. -/
theorem corollary_correspondence : corollaryProof.goal.eval model () ↔ NativeStatement := by
  simp only [corollaryProof, Argument.goal, Expr.eval, model, Var.get, NativeStatement,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, zero_sub]

/-- Extract the actual types of all existing paper theorems, not display labels. -/
def ExistingCorollary : Prop :=
  (statement_of% nu_rho_bound) ∧
  (statement_of% paper_nu_rho_max_unique) ∧
  (statement_of% paper_nu_rho_min_unique) ∧
  (statement_of% (paperD_values Copula.unitHalf)) ∧
  (statement_of% rho_midpoint_original_graph) ∧
  (statement_of% rho_midpoint_reflected_graph)

/-- This is a correspondence between statements; no proof of the corollary is used. -/
theorem existing_correspondence : NativeStatement ↔ ExistingCorollary := by
  have hv : (statement_of% (paperD_values Copula.unitHalf)) ↔
      (extremizer.spearmanRho = 0 ∧ blestNu extremizer = 1/4) := by
    norm_num [extremizer, Copula.unitHalf]
  unfold ExistingCorollary
  rw [hv]
  simp only [neg_div]
  change NativeStatement ↔
    (∀ C : Copula 2, |blestNu C - C.spearmanRho| ≤ 1/4) ∧
    (∀ C : Copula 2, blestNu C - C.spearmanRho = 1/4 → C = extremizer) ∧
    (∀ C : Copula 2, blestNu C - C.spearmanRho = -(1/4) → C = extremizer.survivalCopula) ∧
    (extremizer.spearmanRho = 0 ∧ blestNu extremizer = 1/4) ∧
    OnGraph (rhoFullFamily Copula.unitHalf) tent ∧
    OnGraph (rhoFullFamily Copula.unitHalf).survivalCopula vee
  rw [← paperD_half]
  constructor
  · intro h
    exact ⟨fun C => (h C).1, fun C hc => (h C).2.1.mp hc,
      fun C hc => (h C).2.2.1.mp hc, (h extremizer).2.2.2.1,
      (h extremizer).2.2.2.2⟩
  · rintro ⟨hb, hmax, hmin, hvalues, hgraphs⟩ C
    refine ⟨hb C, ⟨hmax C, ?_⟩, ⟨hmin C, ?_⟩, hvalues, hgraphs⟩
    · rintro rfl; rw [hvalues.1, hvalues.2]; norm_num
    · rintro rfl
      rw [nu_survival, Copula.spearmanRho_survivalCopula, hvalues.1, hvalues.2]
      norm_num

theorem full_correspondence : corollaryProof.goal.eval model () ↔ ExistingCorollary :=
  corollary_correspondence.trans existing_correspondence

#assert_companion_axioms corollary_valid
#assert_companion_axioms corollary_correspondence
#assert_companion_axioms full_correspondence
#assert_companion_axioms left_definition
#assert_companion_axioms phi_definition
#assert_companion_axioms right_definition
#assert_companion_axioms tent_definition
#assert_companion_axioms vee_definition
#assert_companion_axioms survival_definition
#assert_companion_axioms extremizer_definition
#assert_companion_axioms corollary_verified
end Papers.Rockel2026ExactBlest.ArticleProof
