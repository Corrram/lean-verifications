import Companion
import Papers.AnsariRockel2024.Main
import Verification.StochasticRho
import Copula.Rank.ConditionalDerivative

open ProbabilityTheory MeasureTheory Set Matrix
open Copula
open scoped unitInterval
namespace Papers.AnsariRockel2024.ArticleDefinitions
open Companion Ty Lean
abbrev copula : Ty := .base "copula"
inductive Symbol : Ty → Type where
  | rho : Symbol (copula ⇒ₘ real)
  | xi : Symbol (copula ⇒ₘ real)
  | cdf : Symbol (copula ⇒ₘ unit ⇒ₘ unit ⇒ₘ real)
  | partialOne : Symbol (copula ⇒ₘ unit ⇒ₘ unit ⇒ₘ real)
  | survive : Symbol (copula ⇒ₘ copula)
  | reflect : Symbol (unit ⇒ₘ unit)
noncomputable def model : Model Symbol where
  base
    | "copula" => Copula 2
    | _ => Unit
  symbol
    | .rho => Copula.spearmanRho
    | .xi => Copula.chatterjeeXi
    | .cdf => fun C u v => C.cdf ![u,v]
    | .partialOne => fun C u v => deriv (Copula.cdfSection C v) (u : ℝ)
    | .survive => Copula.survivalCopula
    | .reflect => unitInterval.symm
open Symbol

def rhoDefinition : Expr Symbol [copula] real :=
  [math| C |- 12*\int_{0}^{1}{v}{\int_{0}^{1}{u}{\cdf(C,u,v)}}-3]
def xiDefinition : Expr Symbol [copula] real :=
  [math| C |- 6*\int_{0}^{1}{v}{\int_{0}^{1}{u}{\partialOne(C,u,v)*\partialOne(C,u,v)}}-2]
theorem rho_definition (C : Copula 2) : rhoDefinition.eval model (C,())=C.spearmanRho := by
  simpa only [rhoDefinition,Expr.eval,Var.get,model,Ty.denote,Nat.cast_ofNat] using
    (Verification.spearmanRho_eq_iterated_cdf C).symm
theorem xi_definition (C : Copula 2) : xiDefinition.eval model (C,())=C.chatterjeeXi := by
  simpa only [xiDefinition,Expr.eval,Var.get,model,Ty.denote,Nat.cast_ofNat,pow_two] using
    C.chatterjeeXi_eq_integral_deriv.symm


def survivalDefinition : Expr Symbol [unit,unit,copula] real :=
  [math| C v u |- \real{u}+\real{v}-1+\cdf(C,\reflect(u),\reflect(v))]
theorem survival_definition (C : Copula 2) (u v : I) :
    survivalDefinition.eval model (u,v,C,())=C.survivalCopula.cdf ![u,v] := by
  simpa only [survivalDefinition,Expr.eval,Var.get,model,Ty.denote,Nat.cast_one] using
    (C.cdf_survivalCopula u v).symm

def lowerDefinition : Expr Symbol [copula,copula] prop := [math| E D |-
  Forall u : unit. Forall v : unit. \cdf(D,u,v) \le \cdf(E,u,v)]
theorem lower_definition (D E : Copula 2) : lowerDefinition.eval model (D,E,()) ↔ D.LowerOrthantLE E := by
  simp only [lowerDefinition,Expr.eval,Var.get,model,Ty.denote,Copula.LowerOrthantLE]
  constructor
  · intro h z
    have hz : z=![z 0,z 1] := by ext i; fin_cases i <;> rfl
    simpa only [hz] using h (z 0) (z 1)
  · intro h u v
    exact h ![u,v]

def survivalProof : Argument Symbol [] := [proof|
  Fix D : copula named "D";
  Fix E : copula named "E";
  Have Forall u : unit. Forall v : unit.
    \cdf(\survive(D),u,v)=\real{u}+\real{v}-1+\cdf(D,\reflect(u),\reflect(v));
  Have Forall u : unit. Forall v : unit.
    \cdf(\survive(E),u,v)=\real{u}+\real{v}-1+\cdf(E,\reflect(u),\reflect(v));
  Have (Forall u : unit. Forall v : unit. \cdf(D,u,v) \le \cdf(E,u,v)) \iff
    (Forall u : unit. Forall v : unit. \cdf(D,\reflect(u),\reflect(v)) \le \cdf(E,\reflect(u),\reflect(v)));
  Conclude (Forall u : unit. Forall v : unit. \cdf(D,u,v) \le \cdf(E,u,v)) \iff
    (Forall u : unit. Forall v : unit. \cdf(\survive(D),u,v) \le \cdf(\survive(E),u,v))]

theorem survival_valid : survivalProof.Valid model (fun _ => True) := by
  simp only [survivalProof,Argument.Valid,Expr.eval,Var.get,model,Ty.denote,Nat.cast_one]
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨E,D,⟨⟩⟩ _ u v
    exact D.cdf_survivalCopula u v
  · rintro ⟨E,D,⟨⟩⟩ _ u v
    exact E.cdf_survivalCopula u v
  · rintro ⟨E,D,⟨⟩⟩ _
    constructor
    · intro h u v
      exact h (unitInterval.symm u) (unitInterval.symm v)
    · intro h u v
      simpa only [unitInterval.symm_symm] using h (unitInterval.symm u) (unitInterval.symm v)
  · rintro ⟨E,D,⟨⟩⟩ ⟨⟨⟨_,hD⟩,hE⟩,hr⟩
    refine hr.trans ?_
    apply forall_congr'
    intro u
    apply forall_congr'
    intro v
    rw [hD u v,hE u v]
    exact add_le_add_iff_left _ |>.symm

def survivalTarget : Prop := statement_of% survival_lowerOrthant_iff
theorem survival_correspondence : survivalProof.goal.eval model () ↔ survivalTarget := by
  simp only [survivalProof,Argument.goal,Expr.eval,Var.get,model,Ty.denote,survivalTarget]
  constructor
  · intro h D E
    exact (lower_definition D E).symm.trans ((h D E).trans (lower_definition D.survivalCopula E.survivalCopula))
  · intro h D E
    exact (lower_definition D E).trans ((h D E).trans (lower_definition D.survivalCopula E.survivalCopula).symm)
theorem survival_verified : survivalProof.goal.eval model () := survivalProof.sound model _ survival_valid () trivial

def vocabulary : Vocabulary Symbol where
  key _ := "dependence"
  typeLatex
    | .base "copula" => "\\mathcal{C}_2"
    | .unit => "[0,1]"
    | .real => "\\mathbb{R}"
    | _ => ""
  noun _ := ""
  application
    | .rho,[C] => "\\rho_S("++C++")"
    | .xi,[C] => "\\xi("++C++")"
    | .cdf,[C,u,v] => C++"("++u++","++v++")"
    | .partialOne,[C,u,v] => "\\partial_1 "++C++"("++u++","++v++")"
    | .survive,[C] => "\\widehat{"++C++"}"
    | .reflect,[u] => "(1-"++u++")"
    | _,_ => "\\mathrm{unsupported}"
def documents : Json := Json.mkObj [
  (toString ``survival_valid,Json.mkObj [
    ("checked",checked_document% (vocabulary) survival_valid),
    ("title",.str "Proposition 3.2(i): the printed survival-copula comparison"),
    ("note",.str "Both directions follow from the displayed survival formula, reindexing u,v by 1-u,1-v, and canceling the common affine term. The source lower-orthant definition is independently encoded and identified with the native coordinate-vector comparison. This proof does not invoke the existing survival-order equivalence. The later CIS and Schur clauses have separate compiled counterparts; their full printed proofs are not certified by this document."),
    ("correspondence",.str (toString ``survival_correspondence)),("verified",.str (toString ``survival_verified)),
    ("definitionBridge",.str (toString ``survival_definition)),
    ("definition",.str ("\\widehat{C}(u,v):="++survivalDefinition.latex vocabulary ["u","v","C"]))
  ])
]
#assert_companion_axioms rho_definition
#assert_companion_axioms xi_definition
#assert_companion_axioms survival_definition
#assert_companion_axioms lower_definition
#assert_companion_axioms survival_valid
#assert_companion_axioms survival_correspondence
end Papers.AnsariRockel2024.ArticleDefinitions
