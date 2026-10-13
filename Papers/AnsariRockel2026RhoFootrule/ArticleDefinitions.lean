import LeanMirror
import Papers.AnsariRockel2026RhoFootrule.Main

open ProbabilityTheory MeasureTheory Set
open scoped unitInterval
namespace Papers.AnsariRockel2026RhoFootrule.ArticleDefinitions
open LeanMirror Ty Lean
abbrev copula : Ty := .base "copula"

inductive Symbol : Ty → Type where
  | rho : Symbol (copula ⇒ₘ real)
  | phi : Symbol (copula ⇒ₘ real)
  | cdf : Symbol (copula ⇒ₘ unit ⇒ₘ unit ⇒ₘ real)
  | squareRoot : Symbol (real ⇒ₘ real)
  | threeHalves : Symbol (real ⇒ₘ real)
  | upper : Symbol (real ⇒ₘ real)
  | mixture : Symbol (copula ⇒ₘ copula ⇒ₘ unit ⇒ₘ copula)

noncomputable def model : Model Symbol where
  base
    | "copula" => Copula 2
    | _ => Unit
  symbol
    | .rho => Copula.spearmanRho
    | .phi => Copula.spearmanFootrule
    | .cdf => fun C u v => C.cdf ![u,v]
    | .squareRoot => Real.sqrt
    | .threeHalves => fun x => x ^ (3/2:ℝ)
    | .upper => upperRho
    | .mixture => fun C D s => D.mix C s
open Symbol

def rhoDefinition : Expr Symbol [copula] real :=
  [math| C |- 12*\int_{0}^{1}{v}{\int_{0}^{1}{u}{\cdf(C,u,v)}}-3]
def phiDefinition : Expr Symbol [copula] real :=
  [math| C |- 6*\int_{0}^{1}{u}{\cdf(C,u,u)}-2]

theorem rho_definition (C : Copula 2) : rhoDefinition.eval model (C,())=C.spearmanRho := by
  simpa only [rhoDefinition,Expr.eval,Var.get,model,Ty.denote,Nat.cast_ofNat] using
    (Verification.spearmanRho_eq_iterated_cdf C).symm

theorem phi_definition (C : Copula 2) : phiDefinition.eval model (C,())=C.spearmanFootrule := by
  norm_num [phiDefinition,Expr.eval,Var.get,model,Ty.denote,Copula.spearmanFootrule]
  rfl

def lowerDefinition : Expr Symbol [real] real :=
  [math| x |- \frac{2*\squareRoot(3)}{9}*\threeHalves(1+2*x)-1]

-- The printed power 3/2 and the native cubed square root agree on the source domain.
theorem lower_formula {x : ℝ} (hx : x ∈ Icc (-1/2:ℝ) 1) :
    (2*Real.sqrt 3/9)*(1+2*x)^(3/2:ℝ)-1 =
      Copula.RankRegion.RhoFootrule.lowerBoundary x := by
  have hn : 0 ≤ 1+2*x := by linarith [hx.1]
  have hp : (1+2*x)^(3/2:ℝ)=(1+2*x)*Real.sqrt (1+2*x) := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,
      Real.rpow_add_of_nonneg hn (by norm_num) (by norm_num),Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hs := Real.sq_sqrt hn
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hpos : Real.sqrt (3:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [hp]
  unfold Copula.RankRegion.RhoFootrule.lowerBoundary
  rw [Real.sqrt_div hn,div_pow]
  have hs3 : Real.sqrt (1+2*x)^3=(1+2*x)*Real.sqrt (1+2*x) := by
    rw [pow_succ,hs]
  have h33 : Real.sqrt (3:ℝ)^3=3*Real.sqrt (3:ℝ) := by rw [pow_succ,h3]
  rw [hs3,h33]
  field_simp
  ring_nf
  rw [h3]
  ring

theorem lower_definition {x : ℝ} (hx : x ∈ Icc (-1/2:ℝ) 1) :
    lowerDefinition.eval model (x,())=Copula.RankRegion.RhoFootrule.lowerBoundary x := by
  simpa only [lowerDefinition,Expr.eval,Var.get,model,Ty.denote,Nat.cast_ofNat,
    Nat.cast_one] using lower_formula hx

def regionStatement : Expr Symbol [] prop := [math|
  |- Forall r : real. Forall x : real.
    (Exists C : copula. \rho(C)=r \land \phi(C)=x) \iff
    (0-\frac{1}{2} \le x \land x \le 1) \land
    \frac{2*\squareRoot(3)}{9}*\threeHalves(1+2*x)-1 \le r \land r \le \upper(x)]

def existingRegion : Prop := statement_of% exact_region

theorem region_correspondence : regionStatement.eval model () ↔ existingRegion := by
  simp only [regionStatement,Expr.eval,Var.get,model,Ty.denote,Nat.cast_ofNat,
    Nat.cast_one,Nat.cast_zero,existingRegion,zero_sub,mem_Icc,neg_div]
  constructor
  · intro h r x
    have h0 := h r x
    change (∃ C : Copula 2,C.spearmanRho=r ∧ C.spearmanFootrule=x) ↔ _ at h0
    rw [h0]
    constructor
    · rintro ⟨hx,hl,hu⟩
      exact ⟨hx,by simpa only [lower_formula (by simpa only [mem_Icc,neg_div] using hx)] using hl,hu⟩
    · rintro ⟨hx,hl,hu⟩
      exact ⟨hx,by simpa only [lower_formula (by simpa only [mem_Icc,neg_div] using hx)] using hl,hu⟩
  · intro h r x
    change (∃ C : Copula 2,C.spearmanRho=r ∧ C.spearmanFootrule=x) ↔ _
    have h0 := h r x
    change (∃ C : Copula 2,C.spearmanRho=r ∧ C.spearmanFootrule=x) ↔ _ at h0
    rw [h0]
    constructor
    · rintro ⟨hx,hl,hu⟩
      exact ⟨hx,by simpa only [lower_formula (by simpa only [mem_Icc,neg_div] using hx)] using hl,hu⟩
    · rintro ⟨hx,hl,hu⟩
      exact ⟨hx,by simpa only [lower_formula (by simpa only [mem_Icc,neg_div] using hx)] using hl,hu⟩

theorem region_verified : regionStatement.eval model () := region_correspondence.mpr exact_region

def regionStatementProof : Argument Symbol [] := .finish regionStatement
theorem region_statement_valid : regionStatementProof.Valid model (fun _ => True) := by
  intro _ _
  exact region_verified

def fibreProof : Argument Symbol [] := [proof|
  Fix x : real named "x"; Fix r : real named "r";
  Fix C : copula named "B_x"; Fix D : copula named "C_x^+";
  Assume \phi(C)=x \land \phi(D)=x \land \rho(C) \le r \land r \le \rho(D);
  Have Forall t : unit. \phi(\mixture(C,D,t))=x \land
    \rho(\mixture(C,D,t))=\real{t}*\rho(D)+(1-\real{t})*\rho(C);
  Have Exists t : unit. \rho(\mixture(C,D,t))=r;
  Conclude Exists E : copula. \phi(E)=x \land \rho(E)=r]

theorem fibre_valid : fibreProof.Valid model (fun _ => True) := by
  simp only [fibreProof,Argument.Valid,Expr.eval,Var.get,model,Ty.denote,Nat.cast_one]
  refine ⟨?_,?_,?_⟩
  · rintro ⟨D,C,r,x,⟨⟩⟩ ⟨_,h⟩ t
    constructor
    · rw [Copula.spearmanFootrule_mix,h.1,h.2.1]; ring
    · exact Copula.spearmanRho_mix D C t
  · rintro ⟨D,C,r,x,⟨⟩⟩ h
    have hc : Continuous (fun t : I => (D.mix C t).spearmanRho) := by
      simp_rw [(h.2 _).2]
      fun_prop
    exact Verification.exists_unitInterval_eq hc
      (by simpa using h.1.2.2.2.1) (by simpa using h.1.2.2.2.2)
  · rintro ⟨D,C,r,x,⟨⟩⟩ h
    obtain ⟨t,ht⟩ := h.2
    exact ⟨D.mix C t,(h.1.2 t).1,ht⟩

def existingFibre : Prop := statement_of% fixed_footrule_intermediate
theorem fibre_correspondence : fibreProof.goal.eval model () ↔ existingFibre := by
  simp only [fibreProof,Argument.goal,Expr.eval,Var.get,model,Ty.denote,existingFibre]
  constructor
  · intro h C D x r hC hD hrC hrD
    exact h x r C D ⟨hC,hD,hrC,hrD⟩
  · intro h x r C D ⟨hC,hD,hrC,hrD⟩
    exact h C D hC hD hrC hrD

theorem fibre_verified : fibreProof.goal.eval model () :=
  fibreProof.sound model _ fibre_valid () trivial

def mixtureDefinition : Expr Symbol [unit,unit,unit,copula,copula] real :=
  [math| C,D,t,u,v |- \real{t}*\cdf(D,u,v)+(1-\real{t})*\cdf(C,u,v)]
theorem mixture_definition (C D : Copula 2) (t u v : I) :
    mixtureDefinition.eval model (v,u,t,D,C,())=(D.mix C t).cdf ![u,v] := by
  simpa only [mixtureDefinition,Expr.eval,Var.get,model,Ty.denote,Nat.cast_one] using
    (Copula.cdf_mix D C t ![u,v]).symm

def vocabulary : Vocabulary Symbol where
  key _ := "rho-footrule"
  typeLatex
    | .base "copula" => "\\mathcal{C}"
    | .unit => "[0,1]"
    | .real => "\\mathbb{R}"
    | _ => ""
  noun _ := ""
  application
    | .rho,[C] => "\\varrho("++C++")"
    | .phi,[C] => "\\phi("++C++")"
    | .cdf,[C,u,v] => C++"("++u++","++v++")"
    | .squareRoot,[x] => "\\sqrt{"++x++"}"
    | .threeHalves,[x] => "\\left("++x++"\\right)^{3/2}"
    | .upper,[x] => "\\overline{\\varrho}("++x++")"
    | .mixture,[C,D,t] => "\\left["++t++D++"+(1-"++t++")"++C++"\\right]"
    | _,_ => "\\mathrm{unsupported}"

def documents : Json := Json.mkObj [
  (toString ``region_statement_valid,Json.mkObj [
    ("checked",checked_document% (vocabulary) region_statement_valid),
    ("presentation",.str "statement"),
    ("title",.str "Corollary 1.2: the exact rho–footrule region"),
    ("note",.str "The printed lower-bound formula, including its real power 3/2, is independently encoded and proved equal to the native square-root normalization on the stated interval. The upper boundary uses the native scalar function; its arithmetic arcs have separate compiled counterparts. This statement certificate reuses the native region theorem and does not certify its entire printed proof."),
    ("correspondence",.str (toString ``region_correspondence)),
    ("verified",.str (toString ``region_verified)),
    ("definitionBridge",.str (toString ``lower_definition)),
    ("definition",.str ("\\underline{\\varrho}(x):="++lowerDefinition.latex vocabulary ["x"]++",\\qquad x\\in[-\\tfrac12,1]."))
  ]),
  (toString ``fibre_valid,Json.mkObj [
    ("checked",checked_document% (vocabulary) fibre_valid),
    ("title",.str "Corollary 1.2: filling the interval at fixed footrule"),
    ("note",.str "This checks the printed mixture paragraph with its two endpoint copulas supplied. Affineness, attainment of each intermediate rho value, and the final copula witness are separate obligations. It does not certify the preceding construction of the boundary copulas or the subsequent x=1 paragraph."),
    ("correspondence",.str (toString ``fibre_correspondence)),
    ("verified",.str (toString ``fibre_verified)),
    ("definitionBridge",.str (toString ``mixture_definition)),
    ("definition",.str ("C_{x,t}(u,v):="++mixtureDefinition.latex vocabulary ["B_x","C_x^+","t","u","v"]++"."))
  ])
]

#assert_lean_mirror_axioms rho_definition
#assert_lean_mirror_axioms phi_definition
#assert_lean_mirror_axioms lower_formula
#assert_lean_mirror_axioms lower_definition
#assert_lean_mirror_axioms region_correspondence
#assert_lean_mirror_axioms region_verified
#assert_lean_mirror_axioms region_statement_valid
#assert_lean_mirror_axioms fibre_valid
#assert_lean_mirror_axioms fibre_correspondence
#assert_lean_mirror_axioms fibre_verified
#assert_lean_mirror_axioms mixture_definition
end Papers.AnsariRockel2026RhoFootrule.ArticleDefinitions
