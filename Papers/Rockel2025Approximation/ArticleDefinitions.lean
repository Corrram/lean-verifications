import Companion
import Papers.Rockel2025Approximation.Main
import Verification.StochasticRho
import Copula.Rank.ConditionalDerivative

set_option maxRecDepth 1024

open ProbabilityTheory MeasureTheory Set Matrix
open Copula
open scoped unitInterval BigOperators
namespace Papers.Rockel2025Approximation.ArticleDefinitions
open Companion Ty Lean
abbrev copula : Ty := .base "copula"
abbrev permutation : Ty := .base "permutation"
abbrev squareData : Ty := .base "squareData"
abbrev dimensions : Ty := .base "dimensions"
abbrev SquareMass (n : ℕ) := CellMass (IntervalPartition.uniform (n+1) (by omega))
  (IntervalPartition.uniform (n+1) (by omega))
abbrev SquareData := Σ n : ℕ, SquareMass n
abbrev PermData := Σ n : ℕ, Equiv.Perm (Fin (n+1))
def indexValue {n : ℕ} (i : Fin (n+1)) : ℝ := (i.val : ℝ)+1
def displacement (P : PermData) (i : Fin (P.1+1)) : ℝ := indexValue (P.2 i)-indexValue i
structure Dimensions where
  m : ℕ
  n : ℕ
  hm : 0<m
  hn : 0<n

inductive Symbol : Ty → Type where
  | rho : Symbol (copula ⇒ₘ real)
  | xi : Symbol (copula ⇒ₘ real)
  | cdf : Symbol (copula ⇒ₘ unit ⇒ₘ unit ⇒ₘ real)
  | partialOne : Symbol (copula ⇒ₘ unit ⇒ₘ unit ⇒ₘ real)
  | mtp : Symbol (copula ⇒ₘ prop)
  | coarse : Symbol (copula ⇒ₘ dimensions ⇒ₘ copula)
  | piFill : Symbol (squareData ⇒ₘ copula)
  | minFill : Symbol (squareData ⇒ₘ copula)
  | xiTrace : Symbol (squareData ⇒ₘ real)
  | selfTrace : Symbol (squareData ⇒ₘ real)
  | squares : Symbol (squareData ⇒ₘ real)
  | rowSquares : Symbol (squareData ⇒ₘ real)
  | order : Symbol (squareData ⇒ₘ real)
  | estimate : Symbol (squareData ⇒ₘ real)
  | pFirst : Symbol (permutation ⇒ₘ real)
  | iFirst : Symbol (permutation ⇒ₘ real)
  | pSecond : Symbol (permutation ⇒ₘ real)
  | iSecond : Symbol (permutation ⇒ₘ real)
  | cross : Symbol (permutation ⇒ₘ real)
  | dFirst : Symbol (permutation ⇒ₘ real)
  | dWeighted : Symbol (permutation ⇒ₘ real)
  | dSecond : Symbol (permutation ⇒ₘ real)


noncomputable def model : Model Symbol where
  base
    | "copula" => Copula 2
    | "squareData" => SquareData
    | "dimensions" => Dimensions
    | "permutation" => PermData
    | _ => Unit
  symbol
    | .rho => Copula.spearmanRho
    | .xi => Copula.chatterjeeXi
    | .cdf => fun C u v => C.cdf ![u,v]
    | .partialOne => fun C u v => deriv (Copula.cdfSection C v) (u : ℝ)
    | .mtp => Copula.HasMTP2Density
    | .coarse => fun C R => (C.cellMass (IntervalPartition.uniform R.m R.hm)
        (IntervalPartition.uniform R.n R.hn)).checkerboard
    | .piFill => fun D => D.2.checkerboard
    | .minFill => fun D => D.2.checkMin
    | .xiTrace => fun D => Matrix.trace ((Matrix.of D.2.mass)ᵀ * Matrix.of D.2.mass *
        Verification.checkerboardXiMatrix (D.1+1))
    | .selfTrace => fun D => Matrix.trace ((Matrix.of D.2.mass)ᵀ * Matrix.of D.2.mass)
    | .squares => fun D => ∑ i, ∑ j, D.2.mass i j^2
    | .rowSquares => fun D => ∑ i, (∑ j, D.2.mass i j)^2
    | .order => fun D => (D.1 : ℝ)+1
    | .estimate => fun D => Verification.checkerboardEstimator D.2
    | .pFirst => fun P => ∑ i, indexValue (P.2 i)
    | .iFirst => fun P => ∑ i : Fin (P.1+1), indexValue i
    | .pSecond => fun P => ∑ i, indexValue (P.2 i)^2
    | .iSecond => fun P => ∑ i : Fin (P.1+1), indexValue i^2
    | .cross => fun P => ∑ i, indexValue i*indexValue (P.2 i)
    | .dFirst => fun P => ∑ i, displacement P i
    | .dWeighted => fun P => ∑ i, displacement P i*(2*indexValue i-1)
    | .dSecond => fun P => ∑ i, displacement P i^2

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

def estimatorDefinition : Expr Symbol [squareData] real :=
  [math| D |- 6*\xiTrace(D)+\frac{\selfTrace(D)}{2}-2]
theorem estimator_definition (D : SquareData) :
    estimatorDefinition.eval model (D,())=Verification.checkerboardEstimator D.2 := by
  rfl
theorem xi_matrix_definition (n : ℕ) : Verification.checkerboardXiMatrix (n+1)=
    Verification.strictUpperMatrix (n+1)*(Verification.strictUpperMatrix (n+1))ᵀ+
    (Verification.strictUpperMatrix (n+1))ᵀ+(1/3 : ℝ) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) := rfl

def lowerStatement : Expr Symbol [] prop := [math| |- Forall C : copula.
  Forall R : dimensions. \mtp(C) \implies \xi(\coarse(C,R)) \le \xi(C)]
def lowerTarget : Prop := statement_of% checkerboard_xi_le_of_mtp2
theorem lower_correspondence : lowerStatement.eval model () ↔ lowerTarget := by
  simp only [lowerStatement,Expr.eval,Var.get,model,Ty.denote,lowerTarget]
  constructor
  · intro h C hC m n hm hn
    exact h C ⟨m,n,hm,hn⟩ hC
  · intro h C R hC
    exact h C hC R.m R.n R.hm R.hn
theorem lower_verified : lowerStatement.eval model () :=
  lower_correspondence.mpr checkerboard_xi_le_of_mtp2
def lowerStatementProof : Argument Symbol [] := .finish lowerStatement
theorem lower_statement_valid : lowerStatementProof.Valid model (fun _ => True) := by
  intro _ _
  exact lower_verified

def rangeProof : Argument Symbol [] := [proof|
  Fix D : squareData named "\\Delta";
  Have \estimate(D)=\frac{\xi(\piFill(D))+\xi(\minFill(D))}{2};
  Have 0 \le \xi(\piFill(D)) \land \xi(\piFill(D)) \le 1;
  Have 0 \le \xi(\minFill(D)) \land \xi(\minFill(D)) \le 1;
  Conclude 0 \le \estimate(D) \land \estimate(D) \le 1]
theorem range_valid : rangeProof.Valid model (fun _ => True) := by
  simp only [rangeProof,Argument.Valid,
    Expr.eval,Var.get,model,Ty.denote,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨D,⟨⟩⟩ _
    exact checkerboardEstimator_eq_average D.2
  · rintro ⟨D,⟨⟩⟩ _
    exact D.2.checkerboard.chatterjeeXi_mem_Icc
  · rintro ⟨D,⟨⟩⟩ _
    exact D.2.checkMin.chatterjeeXi_mem_Icc
  · rintro ⟨D,⟨⟩⟩ ⟨⟨⟨_,hav⟩,hpi⟩,hmin⟩
    constructor <;> linarith [hav,hpi.1,hpi.2,hmin.1,hmin.2]
def rangeTarget : Prop := statement_of% checkerboardEstimator_mem
theorem range_correspondence : rangeProof.goal.eval model () ↔ rangeTarget := by
  simp only [rangeProof,Argument.goal,Expr.eval,Var.get,model,Ty.denote,Nat.cast_zero,Nat.cast_one,
    rangeTarget,mem_Icc]
  constructor
  · intro h n A
    exact h ⟨n,A⟩
  · intro h D
    exact h D.2
theorem range_verified : rangeProof.goal.eval model () := rangeProof.sound model _ range_valid () trivial

theorem row_square_bound (D : SquareData) :
    (∑ i, ∑ j, D.2.mass i j^2) ≤ ∑ i, (∑ j, D.2.mass i j)^2 := by
  apply Finset.sum_le_sum
  intro i _
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => D.2.nonneg i j)
theorem row_square_value (D : SquareData) :
    (∑ i, (∑ j, D.2.mass i j)^2)=1/((D.1 : ℝ)+1) := by
  simp only [D.2.row_sum,IntervalPartition.width_uniform]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_one,nsmul_eq_mul]
  have h : (D.1 : ℝ)+1 ≠ 0 := by positivity
  field_simp

def traceProof : Argument Symbol [] := [proof|
  Fix D : squareData named "\\Delta";
  Have \selfTrace(D)=\squares(D);
  Have \squares(D) \le \rowSquares(D);
  Have \rowSquares(D)=\frac{1}{\order(D)};
  Conclude \selfTrace(D) \le \frac{1}{\order(D)}]
theorem trace_valid : traceProof.Valid model (fun _ => True) := by
  simp only [traceProof,Argument.Valid,
    Expr.eval,Var.get,model,Ty.denote,Nat.cast_one]
  refine ⟨?_,?_,?_,?_⟩
  · rintro ⟨D,⟨⟩⟩ _
    exact Verification.cellMass_frobenius D.2
  · rintro ⟨D,⟨⟩⟩ _
    exact row_square_bound D
  · rintro ⟨D,⟨⟩⟩ _
    exact row_square_value D
  · rintro ⟨D,⟨⟩⟩ ⟨⟨⟨_,ht⟩,hb⟩,hv⟩
    rw [ht]
    exact hb.trans_eq hv
def traceTarget : Prop := ∀ (n : ℕ) (A : SquareMass n),
  Matrix.trace ((Matrix.of A.mass)ᵀ*Matrix.of A.mass) ≤ 1/((n : ℝ)+1)
theorem trace_correspondence : traceProof.goal.eval model () ↔ traceTarget := by
  simp only [traceProof,Argument.goal,Expr.eval,Var.get,model,Ty.denote,Nat.cast_one,traceTarget]
  constructor
  · intro h n A
    exact h ⟨n,A⟩
  · intro h D
    exact h D.1 D.2
theorem trace_verified : traceProof.goal.eval model () := traceProof.sound model _ trace_valid () trivial


-- The published lemma uses 1,...,n. Fin labels are explicitly shifted by one.
theorem displacement_definition (P : PermData) (i : Fin (P.1+1)) :
    displacement P i = ((P.2 i).val : ℝ)+1-((i.val : ℝ)+1) := rfl

def permutationProof : Argument Symbol [] := [proof|
  Fix P : permutation named "\\pi";
  Have \pFirst(P)=\iFirst(P);
  Have \pSecond(P)=\iSecond(P);
  Have \dFirst(P)=\pFirst(P)-\iFirst(P);
  Have \dWeighted(P)=2*\cross(P)-\pFirst(P)-2*\iSecond(P)+\iFirst(P);
  Have \dSecond(P)=\pSecond(P)-2*\cross(P)+\iSecond(P);
  Conclude \dFirst(P)=0 \land \dWeighted(P)=0-\dSecond(P)]
theorem permutation_valid : permutationProof.Valid model (fun _ => True) := by
  simp only [permutationProof,Argument.Valid,Expr.eval,Var.get,model,Ty.denote,
    Nat.cast_zero,Nat.cast_ofNat]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rintro ⟨P,⟨⟩⟩ _
    exact Equiv.sum_comp P.2 indexValue
  · rintro ⟨P,⟨⟩⟩ _
    exact Equiv.sum_comp P.2 (fun i => indexValue i^2)
  · rintro ⟨P,⟨⟩⟩ _
    simp only [displacement,Finset.sum_sub_distrib]
    rfl
  · rintro ⟨P,⟨⟩⟩ _
    have he : ∀ i : Fin (P.1+1), displacement P i*(2*indexValue i-1)=
        2*(indexValue i*indexValue (P.2 i))-indexValue (P.2 i)-2*indexValue i^2+indexValue i := by
      intro i
      dsimp [displacement]
      ring
    simp_rw [he]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
    rfl
  · rintro ⟨P,⟨⟩⟩ _
    have he : ∀ i : Fin (P.1+1), displacement P i^2=
        indexValue (P.2 i)^2-2*(indexValue i*indexValue (P.2 i))+indexValue i^2 := by
      intro i
      dsimp [displacement]
      ring
    simp_rw [he]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
    rfl
  · rintro ⟨P,⟨⟩⟩ ⟨⟨⟨⟨⟨_,h1⟩,h2⟩,hd⟩,hw⟩,hs⟩
    constructor <;> linarith

def permutationTarget : Prop := ∀ (n : ℕ) (π : Equiv.Perm (Fin (n+1))),
  (∑ i, (indexValue (π i)-indexValue i))=0 ∧
  (∑ i, (indexValue (π i)-indexValue i)*(2*indexValue i-1))=
    -(∑ i, (indexValue (π i)-indexValue i)^2)
theorem permutation_correspondence : permutationProof.goal.eval model () ↔ permutationTarget := by
  simp only [permutationProof,Argument.goal,Expr.eval,Var.get,model,Ty.denote,
    Nat.cast_zero,permutationTarget,displacement,zero_sub]
  constructor
  · intro h n π
    exact h ⟨n,π⟩
  · intro h P
    exact h P.1 P.2
theorem permutation_verified : permutationProof.goal.eval model () :=
  permutationProof.sound model _ permutation_valid () trivial

def vocabulary : Vocabulary Symbol where
  key _ := "approximation"
  typeLatex
    | .base "copula" => "\\mathcal{C}_2"
    | .base "squareData" => "\\mathcal{D}_{\\mathrm{sq}}"
    | .base "dimensions" => "\\mathbb{N}_{>0}^2"
    | .base "permutation" => "\\bigsqcup_{n>0}\\mathfrak{S}_n"
    | .unit => "[0,1]"
    | .real => "\\mathbb{R}"
    | _ => ""
  noun _ := ""
  application
    | .rho,[C] => "\\rho_S("++C++")"
    | .xi,[C] => "\\xi("++C++")"
    | .cdf,[C,u,v] => C++"("++u++","++v++")"
    | .partialOne,[C,u,v] => "\\partial_1 "++C++"("++u++","++v++")"
    | .mtp,[C] => C++"\\text{ has an MTP}_2\\text{ density}"
    | .coarse,[C,R] => "\\operatorname{Check}_{"++R++"}("++C++")"
    | .piFill,[D] => "C_{\\Pi}^{"++D++"}"
    | .minFill,[D] => "C_{\\nearrow}^{"++D++"}"
    | .xiTrace,[D] => "\\operatorname{tr}\\left("++D++"^\\top "++D++" M_\\xi\\right)"
    | .selfTrace,[D] => "\\operatorname{tr}\\left("++D++"^\\top "++D++"\\right)"
    | .squares,[D] => "\\sum_{i,j=1}^{K("++D++")} "++D++"_{i,j}^2"
    | .rowSquares,[D] => "\\sum_{i=1}^{K("++D++")}\\left(\\sum_{j=1}^{K("++D++")} "++D++"_{i,j}\\right)^2"
    | .order,[D] => "K("++D++")"
    | .estimate,[D] => "\\widehat{\\xi}("++D++")"
    | .pFirst,[P] => "\\sum_{i=1}^n \\pi(i)"
    | .iFirst,[P] => "\\sum_{i=1}^n i"
    | .pSecond,[P] => "\\sum_{i=1}^n \\pi(i)^2"
    | .iSecond,[P] => "\\sum_{i=1}^n i^2"
    | .cross,[P] => "\\sum_{i=1}^n i\\pi(i)"
    | .dFirst,[P] => "\\sum_{i=1}^n d_i"
    | .dWeighted,[P] => "\\sum_{i=1}^n d_i(2i-1)"
    | .dSecond,[P] => "\\sum_{i=1}^n d_i^2"
    | _,_ => "\\mathrm{unsupported}"

def documents : Json := Json.mkObj [
  (toString ``permutation_valid,Json.mkObj [
    ("checked",checked_document% (vocabulary) permutation_valid),
    ("title",.str "Lemma 5.1: the printed permutation sum proof"),
    ("note",.str "The source labels 1,...,n are retained by shifting the native Fin labels by one. Reindexing preserves the first and second sums, and the two printed expansions give both displacement identities. Every positive n and every permutation are quantified. The finite sums denote the actual sums of the displayed expressions."),
    ("correspondence",.str (toString ``permutation_correspondence)),("verified",.str (toString ``permutation_verified)),
    ("definitionBridge",.str (toString ``displacement_definition)),
    ("definition",.str "d_i:=\\pi(i)-i,\\quad i=1,\\ldots,n.")
  ]),
  (toString ``lower_statement_valid,Json.mkObj [
    ("checked",checked_document% (vocabulary) lower_statement_valid),
    ("presentation",.str "statement"),
    ("title",.str "Theorem 4.2: the rectangular checkerboard bound"),
    ("note",.str "Both positive grid dimensions are quantified, and Check_R(C) uses the actual masses of C on that uniform rectangular grid. MTP2 means existence of an MTP2 Lebesgue density. The pure interpretation bridge reorders hypotheses without invoking the proved inequality. The statement certificate reuses the existing theorem and does not certify the printed Karamata proof."),
    ("correspondence",.str (toString ``lower_correspondence)),("verified",.str (toString ``lower_verified)),
    ("definitionBridge",.str (toString ``xi_definition)),
    ("definition",.str ("\\xi(C):="++xiDefinition.latex vocabulary ["C"]))
  ]),
  (toString ``range_valid,Json.mkObj [
    ("checked",checked_document% (vocabulary) range_valid),
    ("title",.str "The printed estimator average and its range"),
    ("note",.str "Delta ranges over square checkerboard matrices of every positive order K(Delta). The trace operations and M_xi are the actual finite matrix operations; the arithmetic expression is independently parsed. The averaging identity is supplied by the preceding coefficient formulas. The range conclusion uses the two copula xi bounds and arithmetic, without invoking the existing estimator-range theorem. This does not establish sample consistency."),
    ("correspondence",.str (toString ``range_correspondence)),("verified",.str (toString ``range_verified)),
    ("definitionBridge",.str (toString ``estimator_definition)),
    ("definition",.str ("\\widehat{\\xi}(\\Delta):="++estimatorDefinition.latex vocabulary ["\\Delta"]))
  ]),
  (toString ``trace_valid,Json.mkObj [
    ("checked",checked_document% (vocabulary) trace_valid),
    ("title",.str "Theorem 4.5: the printed trace correction bound"),
    ("note",.str "This checks the finite-matrix inequality in the second proof paragraph. Nonnegative entries bound each sum of squares by the square of its row sum; each row sums to 1/K. The matrix trace is the sum of squared entries. This certificate does not assume or invoke the native correction-bound or consistency theorem. The limit K_n to infinity and almost-sure convergence remain separate compiled counterparts."),
    ("correspondence",.str (toString ``trace_correspondence)),("verified",.str (toString ``trace_verified)),
    ("definitionBridge",.str (toString ``estimator_definition)),
    ("definition",.str "\\mathcal{D}_{\\mathrm{sq}}:=\\{\\Delta\\in\\mathbb{R}^{K\\times K}:K\\in\\mathbb{N}_{>0},\\ \\Delta_{i,j}\\ge0,\\ \\sum_j\\Delta_{i,j}=\\sum_i\\Delta_{i,j}=1/K\\}.")
  ])
]

#assert_companion_axioms permutation_valid
#assert_companion_axioms permutation_correspondence
#assert_companion_axioms displacement_definition
#assert_companion_axioms rho_definition
#assert_companion_axioms xi_definition
#assert_companion_axioms estimator_definition
#assert_companion_axioms xi_matrix_definition
#assert_companion_axioms lower_correspondence
#assert_companion_axioms lower_statement_valid
#assert_companion_axioms range_valid
#assert_companion_axioms range_correspondence
#assert_companion_axioms trace_valid
#assert_companion_axioms trace_correspondence
end Papers.Rockel2025Approximation.ArticleDefinitions
