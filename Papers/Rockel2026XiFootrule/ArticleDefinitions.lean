import Companion
import Papers.Rockel2026XiFootrule.Main

open ProbabilityTheory MeasureTheory
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule.ArticleDefinitions
open Companion Ty Lean
abbrev copula : Ty := .base "copula"

inductive Symbol : Ty → Type where
  | xi : Symbol (copula ⇒ₘ real)
  | psi : Symbol (copula ⇒ₘ real)
  | cdf : Symbol (copula ⇒ₘ unit ⇒ₘ unit ⇒ₘ real)
  | firstPartial : Symbol (copula ⇒ₘ unit ⇒ₘ unit ⇒ₘ real)
  | square : Symbol (real ⇒ₘ real)
  | cube : Symbol (real ⇒ₘ real)
  | cubic : Symbol (real ⇒ₘ real ⇒ₘ real)
  | different : Symbol (real ⇒ₘ real ⇒ₘ prop)
  | minimum : Symbol (real ⇒ₘ real ⇒ₘ real)
  | sqrt : Symbol (real ⇒ₘ real)
  | maximizer : Symbol (unit ⇒ₘ copula)

noncomputable def model : Model Symbol where
  base
    | "copula" => Copula 2
    | _ => Unit
  symbol
    | .xi => Copula.chatterjeeXi
    | .psi => Copula.spearmanFootrule
    | .cdf => fun C u v => C.cdf ![u,v]
    | .firstPartial => fun C u v => deriv (Copula.cdfSection C v) (u : ℝ)
    | .square => fun x => x^2
    | .cube => fun x => x^3
    | .cubic => Verification.footruleCubic
    | .different => fun x y => x ≠ y
    | .minimum => min
    | .sqrt => Real.sqrt
    | .maximizer => fun x => upperBoundary (boundaryParameter x)
open Symbol

def footruleDefinition : Expr Symbol [copula] real :=
  [math| C |- 6*\int_{0}^{1}{t}{\cdf(C,t,t)}-2]

theorem footrule_definition (C : Copula 2) :
    footruleDefinition.eval model (C,()) = C.spearmanFootrule := by
  norm_num [footruleDefinition, Expr.eval, Var.get, model, Ty.denote, Copula.spearmanFootrule]
  rfl

def xiDefinition : Expr Symbol [copula] real :=
  [math| C |- 6*\int_{0}^{1}{v}{\int_{0}^{1}{u}{\square(\firstPartial(C,u,v))}}-2]

theorem xi_definition (C : Copula 2) :
    xiDefinition.eval model (C,()) = C.chatterjeeXi := by
  simp only [xiDefinition, Expr.eval, Var.get, model, Ty.denote, Nat.cast_ofNat]
  exact (xi_derivative_formula C).symm

def frechetDefinition : Expr Symbol [unit,unit,unit] real :=
  [math| a,u,v |- (1-\real{a})*(\real{u}*\real{v})+
    \real{a}*\minimum(\real{u},\real{v})]

theorem frechet_definition (a u v : I) :
    frechetDefinition.eval model (v,u,a,()) = (upperBoundary a).cdf ![u,v] := by
  simp only [frechetDefinition, Expr.eval, Var.get, model, Ty.denote, Nat.cast_one]
  exact (cdf_upperBoundary a u v).symm

def upperStatement : Expr Symbol [] prop :=
  [math| |- Forall x : unit.
    \xi(\maximizer(x))=\real{x} \land
    \psi(\maximizer(x))=\sqrt(\real{x}) \land
    (Forall C : copula. \xi(C)=\real{x} \implies
      \psi(C) \le \sqrt(\real{x}) \land
      (\psi(C)=\sqrt(\real{x}) \iff C=\maximizer(x)))]

def existingUpper : Prop := statement_of% maximal_footrule

-- Interpretation only: this correspondence does not call maximal_footrule.
theorem upper_correspondence : upperStatement.eval model () ↔ existingUpper := Iff.rfl

theorem upper_verified : upperStatement.eval model () :=
  upper_correspondence.mpr maximal_footrule

def upperStatementProof : Argument Symbol [] := [proof|
  Conclude Forall x : unit.
    \xi(\maximizer(x))=\real{x} \land
    \psi(\maximizer(x))=\sqrt(\real{x}) \land
    (Forall C : copula. \xi(C)=\real{x} \implies
      \psi(C) \le \sqrt(\real{x}) \land
      (\psi(C)=\sqrt(\real{x}) \iff C=\maximizer(x)))]

theorem upper_statement_valid : upperStatementProof.Valid model (fun _ => True) := by
  intro _ _
  exact upper_verified

def cubicDefinition : Expr Symbol [real,real] real :=
  [math| y,m |- \cube(m)-(4+2*y)*\square(m)-(4+8*y)*m-8*y]

theorem cubic_definition (y m : ℝ) :
    cubicDefinition.eval model (m,y,()) = Verification.footruleCubic y m := by
  norm_num [cubicDefinition, Expr.eval, Var.get, model, Ty.denote, Verification.footruleCubic]
  rfl

theorem different_definition (x y : ℝ) : model.symbol different x y ↔ x ≠ y := Iff.rfl

-- The two evaluations are separate proof obligations; the conclusion cannot
-- borrow an already-proved final counterexample to conceal a false step.
def cubicCounterexample : Argument Symbol [] := [proof|
  Have \cubic(0-\frac{1}{2},2)=0;
  Have \cubic(0-\frac{1}{2},0-1)=0;
  Conclude \cubic(0-\frac{1}{2},2)=0 \land
    \cubic(0-\frac{1}{2},0-1)=0 \land \different(2,0-1)]

theorem cubic_counterexample_valid : cubicCounterexample.Valid model (fun _ => True) := by
  simp only [cubicCounterexample, Argument.Valid, Expr.eval, model, Ty.denote,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  refine ⟨?_,?_,?_⟩
  · intro _ _
    norm_num [Verification.footruleCubic]
  · intro _ _
    norm_num [Verification.footruleCubic]
  · intro _ h
    exact ⟨h.1.2,h.2,by norm_num⟩

def existingCubicCounterexample : Prop := statement_of% footrule_cubic_not_unique_real

theorem cubic_counterexample_correspondence :
    cubicCounterexample.goal.eval model () ↔ existingCubicCounterexample := by
  simp only [cubicCounterexample, Argument.goal, Expr.eval, model, Ty.denote,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, existingCubicCounterexample, zero_sub, neg_div]

theorem cubic_counterexample_verified : cubicCounterexample.goal.eval model () :=
  cubicCounterexample.sound model _ cubic_counterexample_valid () trivial

def vocabulary : Vocabulary Symbol where
  key _ := "xi-footrule"
  typeLatex
    | .base "copula" => "\\mathcal{C}"
    | .unit => "[0,1]"
    | .real => "\\mathbb{R}"
    | _ => ""
  noun _ := ""
  application
    | .xi, [C] => "\\xi("++C++")"
    | .psi, [C] => "\\psi("++C++")"
    | .cdf, [C,u,v] => C++"("++u++","++v++")"
    | .firstPartial, [C,u,v] => "\\partial_1"++C++"("++u++","++v++")"
    | .square, [x] => "\\left("++x++"\\right)^2"
    | .cube, [x] => "\\left("++x++"\\right)^3"
    | .cubic, [y,m] => "p_{"++y++"}("++m++")"
    | .different, [x,y] => x++"\\ne "++y
    | .minimum, [u,v] => "\\min\\{"++u++","++v++"\\}"
    | .sqrt, [x] => "\\sqrt{"++x++"}"
    | .maximizer, [x] => "C^{\\mathrm{Fr}}_{\\sqrt{"++x++"}}"
    | _, _ => "\\mathrm{unsupported}"

def documents : Json := Json.mkObj [
  (toString ``upper_statement_valid, Json.mkObj [
    ("checked", checked_document% (vocabulary) upper_statement_valid),
    ("presentation", .str "statement"),
    ("title", .str "Theorem 2.1: the maximum, attainment and unique maximizer"),
    ("note", .str "The complete maximum statement is independently encoded, including both endpoints and uniqueness. Its correspondence unfolds interpretation only. The statement certificate reuses the existing compiled theorem, whose squared-distance proof is different from the article's printed KKT proof. That printed proof is not certified by this statement check."),
    ("correspondence", .str (toString ``upper_correspondence)),
    ("verified", .str (toString ``upper_verified)),
    ("definitionBridge", .str (toString ``frechet_definition)),
    ("definition", .str ("C^{\\mathrm{Fr}}_a(u,v):="++frechetDefinition.latex vocabulary ["v","u","a"]))
  ]),
  (toString ``cubic_counterexample_valid, Json.mkObj [
    ("checked", checked_document% (vocabulary) cubic_counterexample_valid),
    ("title", .str "Why the cubic does not have a unique real root"),
    ("note", .str "Both polynomial evaluations are checked independently from the displayed polynomial definition. They refute the printed unrestricted uniqueness at y=-1/2. The corrected theorem restricts the root to [0,2]; the other root, -1, is outside that interval."),
    ("correspondence", .str (toString ``cubic_counterexample_correspondence)),
    ("verified", .str (toString ``cubic_counterexample_verified)),
    ("definitionBridge", .str (toString ``cubic_definition)),
    ("definition", .str ("p_y(m):="++cubicDefinition.latex vocabulary ["m","y"]))
  ])
]

#assert_companion_axioms footrule_definition
#assert_companion_axioms xi_definition
#assert_companion_axioms frechet_definition
#assert_companion_axioms upper_correspondence
#assert_companion_axioms upper_verified
#assert_companion_axioms upper_statement_valid
#assert_companion_axioms cubic_definition
#assert_companion_axioms different_definition
#assert_companion_axioms cubic_counterexample_valid
#assert_companion_axioms cubic_counterexample_correspondence
#assert_companion_axioms cubic_counterexample_verified
end Papers.Rockel2026XiFootrule.ArticleDefinitions
