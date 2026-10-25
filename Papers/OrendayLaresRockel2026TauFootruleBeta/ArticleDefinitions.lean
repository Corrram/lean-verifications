import Companion
import Papers.OrendayLaresRockel2026TauFootruleBeta.Main

open ProbabilityTheory MeasureTheory Set
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026TauFootruleBeta.ArticleDefinitions
open Companion Ty Lean
abbrev copula : Ty := .base "copula"

inductive Symbol : Ty → Type where
  | tau : Symbol (copula ⇒ₘ real)
  | phi : Symbol (copula ⇒ₘ real)
  | beta : Symbol (copula ⇒ₘ real)
  | cdf : Symbol (copula ⇒ₘ unit ⇒ₘ unit ⇒ₘ real)
  | cdfMoment : Symbol (copula ⇒ₘ real)
  | crossMoment : Symbol (copula ⇒ₘ copula ⇒ₘ real)
  | medianCdf : Symbol (copula ⇒ₘ real)
  | square : Symbol (real ⇒ₘ real)
  | lowerPhi : Symbol (real ⇒ₘ real)
  | upperPhi : Symbol (real ⇒ₘ real)
  | lowerTau : Symbol (real ⇒ₘ real)
  | upperTau : Symbol (real ⇒ₘ real)
  | Q : Symbol (copula ⇒ₘ copula ⇒ₘ real)
  | mixture : Symbol (copula ⇒ₘ copula ⇒ₘ unit ⇒ₘ copula)

noncomputable def model : Model Symbol where
  base
    | "copula" => Copula 2
    | _ => Unit
  symbol
    | .tau => Copula.kendallTau
    | .phi => Copula.spearmanFootrule
    | .beta => Copula.blomqvistBeta
    | .cdf => fun C u v => C.cdf ![u,v]
    | .cdfMoment => fun C => ∫ x, C.cdf x ∂C.toMeasure
    | .crossMoment => fun C D => ∫ x, D.cdf x ∂C.toMeasure
    | .medianCdf => fun C => C.cdf ![Copula.unitHalf,Copula.unitHalf]
    | .square => fun x => x^2
    | .lowerPhi => fun b => 3/16*(1+b)^2-1/2
    | .upperPhi => fun b => 1-3/8*(1-b)^2
    | .lowerTau => fun p => 4/3*p-1/3
    | .upperTau => fun p => 2/3*p+1/3
    | .Q => Copula.concordanceQ
    -- The article weights C by 1-s and D by s; mix weights its first argument.
    | .mixture => fun C D s => D.mix C s
open Symbol

def tauDefinition : Expr Symbol [copula] real := [math| C |- 4*\cdfMoment(C)-1]
def phiDefinition : Expr Symbol [copula] real :=
  [math| C |- 6*\int_{0}^{1}{u}{\cdf(C,u,u)}-2]
def betaDefinition : Expr Symbol [copula] real := [math| C |- 4*\medianCdf(C)-1]
def qDefinition : Expr Symbol [copula,copula] real := [math| C,D |- 4*\crossMoment(C,D)-1]

theorem tau_definition (C : Copula 2) : tauDefinition.eval model (C,()) = C.kendallTau := by
  norm_num [tauDefinition,Expr.eval,Var.get,model,Ty.denote,Copula.kendallTau]
  rfl

theorem phi_definition (C : Copula 2) : phiDefinition.eval model (C,()) = C.spearmanFootrule := by
  norm_num [phiDefinition,Expr.eval,Var.get,model,Ty.denote,Copula.spearmanFootrule]
  rfl

theorem beta_definition (C : Copula 2) : betaDefinition.eval model (C,()) = C.blomqvistBeta := by
  norm_num [betaDefinition,Expr.eval,Var.get,model,Ty.denote,Copula.blomqvistBeta]
  rfl

theorem q_definition (C D : Copula 2) : qDefinition.eval model (D,C,()) = C.concordanceQ D := by
  simp only [qDefinition,Expr.eval,Var.get,model,Ty.denote,Nat.cast_ofNat,Nat.cast_one]
  rw [Copula.concordanceQ_comm C D]
  rfl

def lowerPhiDefinition : Expr Symbol [real] real :=
  [math| b |- \frac{3}{16}*\square(1+b)-\frac{1}{2}]
def upperPhiDefinition : Expr Symbol [real] real :=
  [math| b |- 1-\frac{3}{8}*\square(1-b)]
def lowerTauDefinition : Expr Symbol [real] real := [math| p |- \frac{4}{3}*p-\frac{1}{3}]
def upperTauDefinition : Expr Symbol [real] real := [math| p |- \frac{2}{3}*p+\frac{1}{3}]

theorem boundary_definitions (x : ℝ) :
    lowerPhiDefinition.eval model (x,()) = model.symbol lowerPhi x ∧
    upperPhiDefinition.eval model (x,()) = model.symbol upperPhi x ∧
    lowerTauDefinition.eval model (x,()) = model.symbol lowerTau x ∧
    upperTauDefinition.eval model (x,()) = model.symbol upperTau x := by
  norm_num [lowerPhiDefinition,upperPhiDefinition,lowerTauDefinition,upperTauDefinition,
    Expr.eval,Var.get,model,Ty.denote]
  exact ⟨rfl,rfl,rfl,rfl⟩

def regionStatement : Expr Symbol [] prop := [math|
  |- Forall t : real. Forall p : real. Forall b : real.
    (Exists C : copula. \tau(C)=t \land \phi(C)=p \land \beta(C)=b) \iff
    (0-1 \le b \land b \le 1) \land
    \lowerPhi(b) \le p \land p \le \upperPhi(b) \land
    \lowerTau(p) \le t \land t \le \upperTau(p)]

def existingRegion : Prop := statement_of% exact_joint_region

-- Pure interpretation and interval membership, independent of the region proof.
theorem region_correspondence : regionStatement.eval model () ↔ existingRegion := by
  simp only [regionStatement,Expr.eval,Var.get,model,Ty.denote,Nat.cast_one,Nat.cast_zero,
    zero_sub,existingRegion,mem_Icc]
  exact Iff.rfl

theorem region_verified : regionStatement.eval model () := by
  apply region_correspondence.mpr
  exact exact_joint_region

def regionStatementProof : Argument Symbol [] := [proof|
  Conclude Forall t : real. Forall p : real. Forall b : real.
    (Exists C : copula. \tau(C)=t \land \phi(C)=p \land \beta(C)=b) \iff
    (0-1 \le b \land b \le 1) \land
    \lowerPhi(b) \le p \land p \le \upperPhi(b) \land
    \lowerTau(p) \le t \land t \le \upperTau(p)]

theorem region_statement_valid : regionStatementProof.Valid model (fun _ => True) := by
  intro _ _
  exact region_verified

-- The final paragraph of the printed main proof, with supplied endpoints.
-- Each intermediate assertion is an obligation; no use of exact_joint_region.
def fibreProof : Argument Symbol [] := [proof|
  Fix p : real named "p"; Fix b : real named "b"; Fix t : real named "t";
  Fix C : copula named "C^-"; Fix D : copula named "C^+";
  Assume \phi(C)=p \land \phi(D)=p \land \beta(C)=b \land \beta(D)=b \land
    \tau(C) \le t \land t \le \tau(D);
  Have Forall s : unit. \phi(\mixture(C,D,s))=p \land \beta(\mixture(C,D,s))=b;
  Have Forall s : unit. \tau(\mixture(C,D,s))=
    \square(1-\real{s})*\tau(C)+2*\real{s}*(1-\real{s})*\Q(C,D)+\square(\real{s})*\tau(D);
  Have Exists s : unit. \tau(\mixture(C,D,s))=t;
  Conclude Exists E : copula. \tau(E)=t \land \phi(E)=p \land \beta(E)=b]

theorem fibre_valid : fibreProof.Valid model (fun _ => True) := by
  simp only [fibreProof,Argument.Valid,Expr.eval,Var.get,model,Ty.denote,
    Nat.cast_ofNat,Nat.cast_one]
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨D,C,t,b,p,⟨⟩⟩ ⟨_,h⟩ s
    rcases h with ⟨hCp,hDp,hCb,hDb,_,_⟩
    constructor
    · rw [Copula.spearmanFootrule_mix,hDp,hCp]; ring
    · rw [Copula.blomqvistBeta_mix,hDb,hCb]; ring
  · rintro ⟨D,C,t,b,p,⟨⟩⟩ _ s
    rw [Copula.kendallTau_mix,Copula.concordanceQ_comm D C]
    ring
  · rintro ⟨D,C,t,b,p,⟨⟩⟩ h
    have continuous : Continuous (fun s : I => (D.mix C s).kendallTau) := by
      simp_rw [h.2]
      fun_prop
    exact Verification.exists_unitInterval_eq continuous
      (by simpa using h.1.1.2.2.2.2.2.1)
      (by simpa using h.1.1.2.2.2.2.2.2)
  · rintro ⟨D,C,t,b,p,⟨⟩⟩ h
    obtain ⟨s,hs⟩ := h.2
    exact ⟨D.mix C s,hs,(h.1.1.2 s).1,(h.1.1.2 s).2⟩

def existingFibre : Prop := statement_of% fixed_footrule_beta_intermediate

theorem fibre_correspondence : fibreProof.goal.eval model () ↔ existingFibre := by
  simp only [fibreProof,Argument.goal,Expr.eval,Var.get,model,Ty.denote,existingFibre]
  constructor
  · intro h C D p b t hpC hpD hbC hbD htC htD
    obtain ⟨E,ht,hp,hb⟩ := h p b t C D ⟨hpC,hpD,hbC,hbD,htC,htD⟩
    exact ⟨E,hp,hb,ht⟩
  · intro h p b t C D ⟨hpC,hpD,hbC,hbD,htC,htD⟩
    obtain ⟨E,hp,hb,ht⟩ := h C D hpC hpD hbC hbD htC htD
    exact ⟨E,ht,hp,hb⟩

theorem fibre_verified : fibreProof.goal.eval model () :=
  fibreProof.sound model _ fibre_valid () trivial

theorem mixture_definition (C D : Copula 2) (s : I) :
    model.symbol mixture C D s = D.mix C s := rfl

def vocabulary : Vocabulary Symbol where
  key _ := "tau-footrule-beta"
  typeLatex
    | .base "copula" => "\\mathcal{C}"
    | .unit => "[0,1]"
    | .real => "\\mathbb{R}"
    | _ => ""
  noun _ := ""
  application
    | .tau,[C] => "\\tau("++C++")"
    | .phi,[C] => "\\phi("++C++")"
    | .beta,[C] => "\\beta("++C++")"
    | .cdf,[C,u,v] => C++"("++u++","++v++")"
    | .cdfMoment,[C] => "\\int_{[0,1]^2}"++C++"(u,v)\\,\\mathrm{d}"++C++"(u,v)"
    | .crossMoment,[C,D] => "\\int_{[0,1]^2}"++D++"(u,v)\\,\\mathrm{d}"++C++"(u,v)"
    | .medianCdf,[C] => C++"(\\tfrac12,\\tfrac12)"
    | .square,[x] => "\\left("++x++"\\right)^2"
    | .lowerPhi,[b] => "L("++b++")"
    | .upperPhi,[b] => "U("++b++")"
    | .lowerTau,[p] => "\\ell("++p++")"
    | .upperTau,[p] => "u("++p++")"
    | .Q,[C,D] => "\\mathcal{Q}("++C++","++D++")"
    | .mixture,[C,D,s] => "\\left[(1-"++s++")"++C++"+"++s++D++"\\right]"
    | _,_ => "\\mathrm{unsupported}"

def documents : Json := Json.mkObj [
  (toString ``region_statement_valid,Json.mkObj [
    ("checked",checked_document% (vocabulary) region_statement_valid),
    ("presentation",.str "statement"),
    ("title",.str "Theorem 1.1: the exact joint region"),
    ("note",.str "The statement and boundary definitions have independent typed encodings. The correspondence proof unfolds interpretation and interval membership only. This statement certificate reuses the existing region theorem; the complete printed seed and ordinal-sum proof is not yet a checked proof document."),
    ("correspondence",.str (toString ``region_correspondence)),
    ("verified",.str (toString ``region_verified)),
    ("definitionBridge",.str (toString ``boundary_definitions)),
    ("definition",.str ("\\begin{gathered}L(b):="++lowerPhiDefinition.latex vocabulary ["b"]++
      "\\\\U(b):="++upperPhiDefinition.latex vocabulary ["b"]++
      "\\\\\\ell(p):="++lowerTauDefinition.latex vocabulary ["p"]++
      "\\\\u(p):="++upperTauDefinition.latex vocabulary ["p"]++"\\end{gathered}"))
  ]),
  (toString ``fibre_valid,Json.mkObj [
    ("checked",checked_document% (vocabulary) fibre_valid),
    ("title",.str "Filling the vertical fibre: the article's final mixture argument"),
    ("note",.str "This checks the final paragraph with both endpoint copulas supplied and sharing the same footrule and beta. The affine coefficients, quadratic tau formula and intermediate-value step are separate obligations. It does not certify the preceding construction of the endpoints."),
    ("correspondence",.str (toString ``fibre_correspondence)),
    ("verified",.str (toString ``fibre_verified)),
    ("definitionBridge",.str (toString ``mixture_definition)),
    ("definition",.str "C_s:=(1-s)C^-+sC^+,\\qquad s\\in[0,1].")
  ])
]

#assert_companion_axioms tau_definition
#assert_companion_axioms phi_definition
#assert_companion_axioms beta_definition
#assert_companion_axioms q_definition
#assert_companion_axioms boundary_definitions
#assert_companion_axioms region_correspondence
#assert_companion_axioms region_verified
#assert_companion_axioms region_statement_valid
#assert_companion_axioms fibre_valid
#assert_companion_axioms fibre_correspondence
#assert_companion_axioms fibre_verified
#assert_companion_axioms mixture_definition
end Papers.OrendayLaresRockel2026TauFootruleBeta.ArticleDefinitions
