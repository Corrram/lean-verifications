import Companion
import Papers.OrendayLaresRockel2026XiBeta.Main

open ProbabilityTheory
namespace Papers.OrendayLaresRockel2026XiBeta.ArticleDefinitions
open Companion Ty Lean
abbrev copula : Ty := .base "copula"

inductive Symbol : Ty → Type where
  | beta : Symbol (copula ⇒ₘ real)
  | xi : Symbol (copula ⇒ₘ real)
  | midpointCDF : Symbol (copula ⇒ₘ real)
  | cube : Symbol (real ⇒ₘ real)

noncomputable def model : Model Symbol where
  base
    | "copula" => Copula 2
    | _ => Unit
  symbol
    | .beta => Copula.blomqvistBeta
    | .xi => Copula.chatterjeeXi
    | .midpointCDF => fun C => C.cdf ![Copula.unitHalf,Copula.unitHalf]
    | .cube => fun x => x^3
open Symbol

def betaDefinition : Expr Symbol [copula] real :=
  [math| C |- 4*\midpointCDF(C)-1]

theorem beta_definition (C : Copula 2) :
    betaDefinition.eval model (C,()) = C.blomqvistBeta := by
  norm_num [betaDefinition, Expr.eval, Var.get, model, Ty.denote, Copula.blomqvistBeta]
  rfl

-- The universal inequality is parsed independently from the existing theorem.
-- Its correspondence unfolds interpretation only, not the theorem's proof.
def lowerBound : Expr Symbol [] prop :=
  [math| |- Forall C : copula. \cube(\abs{\beta(C)}) \le 2*\xi(C)]

def existingLowerBound : Prop := statement_of% beta_cubic_le_two_xi

theorem lower_bound_correspondence : lowerBound.eval model () ↔ existingLowerBound := Iff.rfl

theorem lower_bound_verified : lowerBound.eval model () :=
  lower_bound_correspondence.mpr beta_cubic_le_two_xi

-- The region definition is independently encoded as attainability, so the
-- quantifier over copulas is visible rather than hidden behind set notation.
def regionDefinition : Expr Symbol [real,real] prop :=
  [math| x,y |- Exists C : copula. \xi(C)=x \land \beta(C)=y]

theorem region_definition (x y : ℝ) :
    regionDefinition.eval model (y,x,()) ↔
      (x,y) ∈ xiBetaRegion (Set.univ : Set (Copula 2)) := by
  simp only [regionDefinition, Expr.eval, Var.get, model, Ty.denote,
    xiBetaRegion, Set.mem_ofPred_eq, Set.mem_univ, true_and]
  rfl

def exactRegionStatement : Expr Symbol [] prop :=
  [math| |- Forall x : real. Forall y : real.
    (Exists C : copula. \xi(C)=x \land \beta(C)=y) \iff
      (0 \le x \land x \le 1) \land
      ((0-1 \le y \land y \le 1) \land \cube(\abs{y}) \le 2*x)]

def existingRegion : Prop := statement_of% theorem_1_1_region

-- Only definitions and set extensionality are used here, never the theorem.
theorem exact_region_correspondence : exactRegionStatement.eval model () ↔ existingRegion := by
  simp only [exactRegionStatement, Expr.eval, Var.get, model, Ty.denote,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  change (∀ x y : ℝ, (∃ C : Copula 2, C.chatterjeeXi=x ∧ C.blomqvistBeta=y) ↔
    (0 ≤ x ∧ x ≤ 1) ∧ ((0-1 ≤ y ∧ y ≤ 1) ∧ |y|^3 ≤ 2*x)) ↔ _
  simp only [existingRegion, Set.ext_iff, Prod.forall, xiBetaRegion, exactRegion,
    Set.mem_ofPred_eq, Set.mem_univ, true_and, Set.mem_Icc, zero_sub]

theorem exact_region_verified : exactRegionStatement.eval model () :=
  exact_region_correspondence.mpr theorem_1_1_region

def regionStatementProof : Argument Symbol [] := [proof|
  Conclude Forall x : real. Forall y : real.
    (Exists C : copula. \xi(C)=x \land \beta(C)=y) \iff
      (0 \le x \land x \le 1) \land
      ((0-1 \le y \land y \le 1) \land \cube(\abs{y}) \le 2*x)]

theorem region_statement_valid : regionStatementProof.Valid model (fun _ => True) := by
  intro _ _
  exact exact_region_verified

def lowerBoundProof : Argument Symbol [] := [proof|
  Fix C : copula named "C";
  Conclude \cube(\abs{\beta(C)}) \le 2*\xi(C)]

theorem lower_bound_document_valid : lowerBoundProof.Valid model (fun _ => True) := by
  simp only [lowerBoundProof, Argument.Valid, Expr.eval, Var.get, model, Ty.denote,
    Nat.cast_ofNat]
  exact fun ⟨C,⟨⟩⟩ _ => beta_cubic_le_two_xi C

def vocabulary : Vocabulary Symbol where
  key _ := "copula-coefficients"
  typeLatex
    | .base "copula" => "\\mathcal{C}"
    | .real => "\\mathbb{R}"
    | _ => ""
  noun _ := ""
  application
    | .beta, [C] => "\\beta("++C++")"
    | .xi, [C] => "\\xi("++C++")"
    | .midpointCDF, [C] => C++"\\left(\\tfrac12,\\tfrac12\\right)"
    | .cube, [x] => "\\left("++x++"\\right)^3"
    | _, _ => "\\mathrm{unsupported}"

def documents : Json := Json.mkObj [
  (toString ``lower_bound_document_valid, Json.mkObj [
    ("checked", checked_document% (vocabulary) lower_bound_document_valid),
    ("presentation", .str "statement"),
    ("title", .str "The universal cubic inequality: checked statement correspondence"),
    ("note", .str "This one-step statement proof reuses the existing compiled lower-bound theorem. It verifies this inequality component of Theorem 1.1; it does not certify the article's printed proof of Proposition 4.1."),
    ("correspondence", .str (toString ``lower_bound_correspondence)),
    ("verified", .str (toString ``lower_bound_verified)),
    ("definitionBridge", .str (toString ``beta_definition)),
    ("definition", .str ("\\beta(C):=" ++ betaDefinition.latex vocabulary ["C"]))
  ]),
  (toString ``region_statement_valid, Json.mkObj [
    ("checked", checked_document% (vocabulary) region_statement_valid),
    ("presentation", .str "statement"),
    ("title", .str "Exact region: checked mathematical statement"),
    ("note", .str "This is a statement certificate using the compiled region theorem. The correspondence proof uses only interpretation of the definitions and set extensionality. It does not certify the article's printed variational proof."),
    ("correspondence", .str (toString ``exact_region_correspondence)),
    ("verified", .str (toString ``exact_region_verified)),
    ("definitionBridge", .str (toString ``region_definition)),
    ("definition", .str ("(x,y)\\in\\mathcal{R}_{\\xi,\\beta}\\;\\Longleftrightarrow\\;" ++ regionDefinition.latex vocabulary ["y","x"]))
  ])
]

#assert_companion_axioms beta_definition
#assert_companion_axioms region_definition
#assert_companion_axioms exact_region_correspondence
#assert_companion_axioms exact_region_verified
#assert_companion_axioms region_statement_valid
#assert_companion_axioms lower_bound_correspondence
#assert_companion_axioms lower_bound_verified
#assert_companion_axioms lower_bound_document_valid
end Papers.OrendayLaresRockel2026XiBeta.ArticleDefinitions
