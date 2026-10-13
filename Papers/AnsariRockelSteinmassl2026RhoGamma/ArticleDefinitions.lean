import LeanMirror
import Papers.AnsariRockelSteinmassl2026RhoGamma.Main
import Verification.StochasticRho

open ProbabilityTheory MeasureTheory Set
open scoped unitInterval
namespace Papers.AnsariRockelSteinmassl2026RhoGamma.ArticleDefinitions
open LeanMirror Ty Lean
abbrev copula : Ty := .base "copula"

inductive Symbol : Ty → Type where
  | rho : Symbol (copula ⇒ₘ real)
  | gamma : Symbol (copula ⇒ₘ real)
  | cdf : Symbol (copula ⇒ₘ unit ⇒ₘ unit ⇒ₘ real)
  | complement : Symbol (unit ⇒ₘ unit)
  | upper : Symbol (real ⇒ₘ real)
  | mixture : Symbol (copula ⇒ₘ copula ⇒ₘ unit ⇒ₘ copula)
  | mCopula : Symbol copula
  | square : Symbol (real ⇒ₘ real)
  | cube : Symbol (real ⇒ₘ real)
  | squareRoot : Symbol (real ⇒ₘ real)
  | potentialOffset : Symbol (real ⇒ₘ real)
  | mean : Symbol (real ⇒ₘ real)
  | secondMoment : Symbol (real ⇒ₘ real)
  | alpha : Symbol (real ⇒ₘ real)
  | t : Symbol (real ⇒ₘ real)
  | a : Symbol (real ⇒ₘ real)
  | z : Symbol (real ⇒ₘ real)

noncomputable def model : Model Symbol where
  base
    | "copula" => Copula 2
    | _ => Unit
  symbol
    | .rho => Copula.spearmanRho
    | .gamma => Copula.giniGamma
    | .cdf => fun C u v => C.cdf ![u,v]
    | .complement => unitInterval.symm
    | .upper => upperRho
    | .mixture => fun C D s => D.mix C s
    | .mCopula => Copula.comonotonic 2
    | .square => fun x => x^2
    | .cube => fun x => x^3
    | .squareRoot => Real.sqrt
    | .potentialOffset => thetaOffset
    | .mean => thetaMean
    | .secondMoment => thetaSquare
    | .alpha => thetaAlpha
    | .t => thetaT
    | .a => thetaA
    | .z => thetaZ
open Symbol

def rhoDefinition : Expr Symbol [copula] real :=
  [math| C |- 12*\int_{0}^{1}{v}{\int_{0}^{1}{u}{\cdf(C,u,v)}}-3]
def gammaDefinition : Expr Symbol [copula] real :=
  [math| C |- 4*\int_{0}^{1}{u}{\cdf(C,u,u)+\cdf(C,u,\complement(u))}-2]

theorem rho_definition (C : Copula 2) : rhoDefinition.eval model (C,())=C.spearmanRho := by
  simpa only [rhoDefinition,Expr.eval,Var.get,model,Ty.denote,Nat.cast_ofNat] using
    (Verification.spearmanRho_eq_iterated_cdf C).symm

theorem gamma_definition (C : Copula 2) : gammaDefinition.eval model (C,())=C.giniGamma := by
  simp only [gammaDefinition,Expr.eval,Var.get,model,Ty.denote,Nat.cast_ofNat]
  change 4*(∫ u : I,C.cdf ![u,u]+C.cdf ![u,unitInterval.symm u])-2=C.giniGamma
  rw [integral_add (Copula.integrable_continuous_unit volume (by fun_prop))
    (Copula.integrable_continuous_unit volume (by fun_prop))]
  rfl

-- The introductory C_0=M convention conflicts with G(0)=-1 and G(theta)=gamma(C_theta).
theorem intro_zero_endpoint_incompatible :
    thetaG 0 ≠ (Copula.comonotonic 2).giniGamma := by
  have hzero := congrArg Prod.fst theta_coordinates_zero
  change thetaG 0 = (-1 : ℝ) at hzero
  rw [hzero,Copula.giniGamma_comonotonic]
  norm_num

def alphaDefinition : Expr Symbol [real] real :=
  [math| theta |- \frac{1+\squareRoot(1+2*\square(theta)*\potentialOffset(theta))}{2}]
def tDefinition : Expr Symbol [real] real := [math| theta |- \frac{1}{theta+\alpha(theta)}]
def aDefinition : Expr Symbol [real] real := [math| theta |- \alpha(theta)*\t(theta)]
def zDefinition : Expr Symbol [real] real := [math| theta |- theta*\t(theta)]
def gDefinition : Expr Symbol [real] real :=
  [math| theta |- 1-2*\square(\a(theta))-\square(\z(theta))*\mean(theta)]
def pDefinition : Expr Symbol [real] real :=
  [math| theta |- 1-2*\cube(\a(theta))-\frac{3}{2}*\cube(\z(theta))*\secondMoment(theta)]

theorem splitting_definitions (theta : ℝ) :
    alphaDefinition.eval model (theta,())=thetaAlpha theta ∧
    tDefinition.eval model (theta,())=thetaT theta ∧
    aDefinition.eval model (theta,())=thetaA theta ∧
    zDefinition.eval model (theta,())=thetaZ theta := by
  simp only [alphaDefinition,tDefinition,aDefinition,zDefinition,Expr.eval,Var.get,model,
    Ty.denote,Nat.cast_one,Nat.cast_ofNat]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem coordinate_definitions (theta : ℝ) :
    gDefinition.eval model (theta,())=thetaG theta ∧
    pDefinition.eval model (theta,())=thetaP theta := by
  norm_num [gDefinition,pDefinition,Expr.eval,Var.get,model,Ty.denote,thetaG,thetaP]
  exact ⟨rfl,rfl⟩

-- The original maximum definition is characterized by attainment and the upper-bound property.
def upperDefinition : Expr Symbol [real] prop := [math| g |-
  Exists C : copula. \gamma(C)=g \land \rho(C)=\upper(g) \land
    Forall D : copula. \gamma(D)=g \implies \rho(D) \le \upper(g)]
theorem upper_definition {g : ℝ} (hg : g ∈ Icc (-1:ℝ) 1) :
    upperDefinition.eval model (g,()) := by
  simp only [upperDefinition,Expr.eval,Var.get,model,Ty.denote]
  obtain ⟨C,hCg,hCr⟩ := upper_boundary_attained hg
  refine ⟨C,hCg,hCr,?_⟩
  intro D hD
  simpa only [hD] using sharp_upper_bound D

def regionStatement : Expr Symbol [] prop := [math|
  |- Forall r : real. Forall g : real.
    (Exists C : copula. \rho(C)=r \land \gamma(C)=g) \iff
    (0-1 \le g \land g \le 1) \land
    0-\upper(0-g) \le r \land r \le \upper(g)]
def existingRegion : Prop := statement_of% exact_region

theorem region_correspondence : regionStatement.eval model () ↔ existingRegion := by
  simp only [regionStatement,Expr.eval,Var.get,model,Ty.denote,Nat.cast_zero,Nat.cast_one,
    zero_sub,existingRegion,region,mem_range,mem_Icc]
  constructor
  · intro h r g
    have h0 := h r g
    change (∃ C : Copula 2,C.spearmanRho=r ∧ C.giniGamma=g) ↔ _ at h0
    rw [← h0]
    constructor
    · rintro ⟨C,hC⟩
      exact ⟨C,congrArg Prod.fst hC,congrArg Prod.snd hC⟩
    · rintro ⟨C,hr,hg⟩
      exact ⟨C,Prod.ext hr hg⟩
  · intro h r g
    change (∃ C : Copula 2,C.spearmanRho=r ∧ C.giniGamma=g) ↔ _
    rw [← h r g]
    constructor
    · rintro ⟨C,hr,hg⟩
      exact ⟨C,Prod.ext hr hg⟩
    · rintro ⟨C,hC⟩
      exact ⟨C,congrArg Prod.fst hC,congrArg Prod.snd hC⟩

theorem region_verified : regionStatement.eval model () := region_correspondence.mpr exact_region
def regionStatementProof : Argument Symbol [] := .finish regionStatement
theorem region_statement_valid : regionStatementProof.Valid model (fun _ => True) := by
  intro _ _
  exact region_verified

def strictProof : Argument Symbol [] := [proof|
  Fix g1 : real named "g_1"; Fix g2 : real named "g_2";
  Assume 0-1 \le g1 \land g1 < g2 \land g2 \le 1;
  Choose C : copula named "C_1" satisfying \gamma(C)=g1 \land \rho(C)=\upper(g1)
    to prove \upper(g1) < \upper(g2);
  Have \rho(C) < 1;
  Choose eta : unit named "\\eta" satisfying
    \real{eta}=\frac{g2-g1}{1-g1} \land 0 < \real{eta}
    to prove \upper(g1) < \upper(g2);
  Have \gamma(\mixture(C,\mCopula,eta))=g2 \land
    \rho(\mixture(C,\mCopula,eta))=(1-\real{eta})*\upper(g1)+\real{eta};
  Have \upper(g1) < \rho(\mixture(C,\mCopula,eta));
  Have \rho(\mixture(C,\mCopula,eta)) \le \upper(g2);
  Conclude \upper(g1) < \upper(g2)]

theorem strict_valid : strictProof.Valid model (fun _ => True) := by
  simp only [strictProof,Argument.Valid,Argument.goal,Expr.weaken,Expr.rename,
    Expr.eval,Var.get,model,Ty.denote,Nat.cast_zero,Nat.cast_one,zero_sub]
  refine ⟨?_,trivial,?_,?_,trivial,?_,?_,?_,?_⟩
  · rintro ⟨g2,g1,⟨⟩⟩ ⟨_,h⟩
    exact upper_boundary_attained ⟨h.1,h.2.1.le.trans h.2.2⟩
  · rintro ⟨C,g2,g1,⟨⟩⟩ ⟨⟨_,h⟩,hC⟩
    apply lt_of_le_of_ne C.spearmanRho_mem_Icc.2
    intro he
    have hm := C.spearmanRho_eq_one_iff.mp he
    rw [hm,Copula.giniGamma_comonotonic] at hC
    linarith [h.2.1,h.2.2,hC.1]
  · rintro ⟨C,g2,g1,⟨⟩⟩ ⟨⟨⟨_,h⟩,_⟩,_⟩
    have hd : 0 < 1-g1 := by linarith [h.2.1,h.2.2]
    have hp : 0 < (g2-g1)/(1-g1) := div_pos (sub_pos.mpr h.2.1) hd
    exact ⟨⟨(g2-g1)/(1-g1),hp.le,(div_le_one hd).mpr (by linarith [h.2.2])⟩,rfl,hp⟩
  · rintro ⟨eta,C,g2,g1,⟨⟩⟩ ⟨⟨⟨⟨_,h⟩,hC⟩,_⟩,he⟩
    constructor
    · rw [Copula.giniGamma_mix,Copula.giniGamma_comonotonic,hC.1,he.1]
      have hd : 1-g1 ≠ 0 := by linarith [h.2.1,h.2.2]
      field_simp
      ring
    · rw [Copula.spearmanRho_mix,Copula.spearmanRho_comonotonic,hC.2]
      ring
  · rintro ⟨eta,C,g2,g1,⟨⟩⟩ ⟨⟨⟨⟨_,hC⟩,hr⟩,he⟩,hm⟩
    rw [hm.2]
    have hp := mul_pos he.2 (sub_pos.mpr hr)
    rw [hC.2] at hp
    nlinarith only [hp]
  · rintro ⟨eta,C,g2,g1,⟨⟩⟩ ⟨⟨_,hm⟩,_⟩
    simpa only [hm.1] using sharp_upper_bound ((Copula.comonotonic 2).mix C eta)
  · rintro ⟨eta,C,g2,g1,⟨⟩⟩ h
    exact h.1.2.trans_le h.2

def existingStrict : Prop := statement_of% upperRho_strictMono
theorem strict_correspondence : strictProof.goal.eval model () ↔ existingStrict := by
  simp only [strictProof,Argument.goal,Expr.eval,Var.get,model,Ty.denote,
    Nat.cast_zero,Nat.cast_one,zero_sub,existingStrict,StrictMonoOn]
  constructor
  · intro h x hx y hy hxy
    exact h x y ⟨hx.1,hxy,hy.2⟩
  · intro h x y ⟨hx,hxy,hy⟩
    exact h ⟨hx,hxy.le.trans hy⟩ ⟨hx.trans hxy.le,hy⟩ hxy
theorem strict_verified : strictProof.goal.eval model () :=
  strictProof.sound model _ strict_valid () trivial

def mixtureDefinition : Expr Symbol [unit,unit,unit,copula,copula] real :=
  [math| C,D,t,u,v |- (1-\real{t})*\cdf(C,u,v)+\real{t}*\cdf(D,u,v)]
theorem mixture_definition (C D : Copula 2) (t u v : I) :
    mixtureDefinition.eval model (v,u,t,D,C,())=(D.mix C t).cdf ![u,v] := by
  simp only [mixtureDefinition,Expr.eval,Var.get,model,Ty.denote,Nat.cast_one,Copula.cdf_mix]
  ring

def vocabulary : Vocabulary Symbol where
  key _ := "rho-gamma"
  typeLatex
    | .base "copula" => "\\mathcal{C}"
    | .unit => "[0,1]"
    | .real => "\\mathbb{R}"
    | _ => ""
  noun _ := ""
  application
    | .rho,[C] => "\\rho("++C++")"
    | .gamma,[C] => "\\gamma("++C++")"
    | .cdf,[C,u,v] => C++"("++u++","++v++")"
    | .complement,[u] => "(1-"++u++")"
    | .upper,[g] => "\\overline{\\rho}("++g++")"
    | .mixture,[C,D,s] => "\\left[(1-"++s++")"++C++"+"++s++" "++D++"\\right]"
    | .mCopula,[] => "M"
    | .square,[x] => "\\left("++x++"\\right)^2"
    | .cube,[x] => "\\left("++x++"\\right)^3"
    | .squareRoot,[x] => "\\sqrt{"++x++"}"
    | .potentialOffset,[x] => "c_{"++x++"}"
    | .mean,[x] => "m_{"++x++"}"
    | .secondMoment,[x] => "q_{"++x++"}"
    | .alpha,[x] => "\\alpha_{"++x++"}"
    | .t,[x] => "t_{"++x++"}"
    | .a,[x] => "a_{"++x++"}"
    | .z,[x] => "z_{"++x++"}"
    | _,_ => "\\mathrm{unsupported}"

def documents : Json := Json.mkObj [
  (toString ``region_statement_valid,Json.mkObj [
    ("checked",checked_document% (vocabulary) region_statement_valid),
    ("presentation",.str "statement"),
    ("title",.str "Theorem 1.1: the exact-region clause"),
    ("note",.str "Equation (6) has an independent typed encoding, with the source coordinate order (rho,gamma). The correspondence identifies attainable coefficient pairs with the native range. It does not invoke the region theorem. The scalar upper boundary is separately characterized as an attained maximum. The theta parametrization, compactness and other clauses have separate compiled counterparts; this statement certificate does not certify their full printed proofs."),
    ("correspondence",.str (toString ``region_correspondence)),
    ("verified",.str (toString ``region_verified)),
    ("definitionBridge",.str (toString ``upper_definition)),
    ("definition",.str (upperDefinition.latex vocabulary ["g"]))
  ]),
  (toString ``strict_valid,Json.mkObj [
    ("checked",checked_document% (vocabulary) strict_valid),
    ("title",.str "Theorem 1.1: the printed strict-monotonicity argument"),
    ("note",.str "This checks the final paragraph of the main proof: choose a boundary optimizer, prove its rho is below one, choose eta=(g2-g1)/(1-g1), and mix it with M. The prescribed gamma, affine rho, strict increase, and comparison with the upper boundary are separate obligations. Boundary attainment and the global upper bound are supplied compiled results from the preceding construction. The other main-proof paragraphs are not certified by this document."),
    ("correspondence",.str (toString ``strict_correspondence)),
    ("verified",.str (toString ``strict_verified)),
    ("definitionBridge",.str (toString ``mixture_definition)),
    ("definition",.str ("C_\\eta(u,v):="++mixtureDefinition.latex vocabulary ["C_1","M","\\eta","u","v"]++"."))
  ])
]

#assert_lean_mirror_axioms rho_definition
#assert_lean_mirror_axioms gamma_definition
#assert_lean_mirror_axioms intro_zero_endpoint_incompatible
#assert_lean_mirror_axioms splitting_definitions
#assert_lean_mirror_axioms coordinate_definitions
#assert_lean_mirror_axioms upper_definition
#assert_lean_mirror_axioms region_correspondence
#assert_lean_mirror_axioms region_verified
#assert_lean_mirror_axioms region_statement_valid
#assert_lean_mirror_axioms strict_valid
#assert_lean_mirror_axioms strict_correspondence
#assert_lean_mirror_axioms strict_verified
#assert_lean_mirror_axioms mixture_definition
end Papers.AnsariRockelSteinmassl2026RhoGamma.ArticleDefinitions
