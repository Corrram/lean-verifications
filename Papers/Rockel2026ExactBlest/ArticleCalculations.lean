import Papers.Rockel2026ExactBlest.ArticleOriginalProof

namespace Papers.Rockel2026ExactBlest.ArticleCalculations
open LeanMirror Ty Lean
open ArticleOriginalProof

inductive Symbol : Ty → Type where
  | delta : Symbol (real ⇒ₘ real ⇒ₘ real ⇒ₘ real)
  | phi : Symbol (real ⇒ₘ real ⇒ₘ real)
  | psi : Symbol (real ⇒ₘ real ⇒ₘ real)
  | sq : Symbol (real ⇒ₘ real)
  | factor : Symbol (real ⇒ₘ real ⇒ₘ real ⇒ₘ real)

noncomputable def model : Model Symbol where
  base _ := Unit
  symbol
    | .delta => deltaA
    | .phi => paperPhiA
    | .psi => paperPsiA
    | .sq => fun t => t^2
    | .factor => fun w x z => (6-2*w)*z-(3+2*w)*x+3-4*w
open Symbol

-- Independent syntax for the slack's definition, rather than a proved inequality.
def deltaDefinition : Expr Symbol [real,real,real] real :=
  [math| w,x,z |- \phi(w,x)+\psi(w,z)-(\sq(x)*z-\frac{3-2*w}{2*w}*x*\sq(z))]

theorem delta_definition (w x z : ℝ) :
    deltaDefinition.eval model (z,x,w,()) = deltaA w x z := rfl

-- The first rectangle's calculation, in the same order as the printed proof.
def firstRectangle : Argument Symbol [] := [proof|
  Fix w : real named "w";
  Fix x : real named "x";
  Fix z : real named "z";
  Assume \frac{1}{2} \le w \land w \le 1;
  Assume 1-w \le x \land x \le 1;
  Assume 0 \le z \land z \le w;
  Have \delta(w,x,z)=\frac{\sq(x+w-1-z)*(1-w+(2*w-1)*x-2*(1-w)*z)}{2*w};
  Have 2*(1-w)*(w-z) \le 1-w+(2*w-1)*x-2*(1-w)*z;
  Have 0 \le 2*(1-w)*(w-z);
  Conclude 0 \le \delta(w,x,z)]

theorem first_rectangle_valid : firstRectangle.Valid model (fun _ => True) := by
  simp only [firstRectangle, Argument.Valid, Expr.eval, Var.get,
    model, Ty.denote, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨_,hw⟩,hx⟩,hz⟩
    exact graph_rectangle_10 w x z (by linarith [hw.1]) hx.1 hz.2
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨_,hw⟩,hx⟩,_⟩,_⟩
    exact graph_first_factor w x z hw.1 hx.1
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨_,hw⟩,_⟩,hz⟩,_⟩,_⟩
    exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hw.2))
      (sub_nonneg.mpr hz.2)
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨⟨_,hw⟩,_⟩,_⟩,he⟩,hf⟩,hp⟩
    rw [he]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (hp.trans hf)) (by linarith [hw.1])

theorem first_rectangle_verified : firstRectangle.goal.eval model () :=
  firstRectangle.sound model _ first_rectangle_valid () trivial

-- This correspondence is proved by interpreting the displayed statement only.
theorem first_rectangle_correspondence : firstRectangle.goal.eval model () ↔
    ∀ w x z : ℝ, (1/2 ≤ w ∧ w ≤ 1) → (1-w ≤ x ∧ x ≤ 1) →
      (0 ≤ z ∧ z ≤ w) → 0 ≤ deltaA w x z := by
  simp only [firstRectangle, Argument.goal, Expr.eval, Var.get, model, Ty.denote,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

def factorDefinition : Expr Symbol [real,real,real] real :=
  [math| w,x,z |- (6-2*w)*z-(3+2*w)*x+3-4*w]

theorem factor_definition (w x z : ℝ) :
    factorDefinition.eval model (z,x,w,()) = (6-2*w)*z-(3+2*w)*x+3-4*w := rfl

def secondRectangle : Argument Symbol [] := [proof|
  Fix w : real named "w";
  Fix x : real named "x";
  Fix z : real named "z";
  Assume \frac{1}{2} \le w \land w \le 1;
  Assume 0 \le x \land x \le 1-w;
  Assume w \le z \land z \le 1;
  Have \delta(w,x,z)=\frac{\sq(x+z-1)*\factor(w,x,z)}{6*w};
  Have 3*w \le \factor(w,x,z);
  Have 0 < 3*w;
  Have 0 \le \delta(w,x,z);
  Conclude \delta(w,x,z)=0 \iff x+z=1]

theorem second_rectangle_valid : secondRectangle.Valid model (fun _ => True) := by
  simp only [secondRectangle, Argument.Valid, Expr.eval, Var.get, model, Ty.denote,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨_,hw⟩,hx⟩,hz⟩
    exact graph_rectangle_01 w x z (by linarith [hw.1]) hx.2 hz.1
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨_,hw⟩,hx⟩,hz⟩,_⟩
    exact graph_second_factor w x z hw.1 hw.2 hx.2 hz.1
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨_,hw⟩,_⟩,_⟩,_⟩,_⟩
    linarith [hw.1]
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨⟨_,hw⟩,_⟩,_⟩,he⟩,hf⟩,hp⟩
    rw [he]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (hp.le.trans hf)) (by linarith [hw.1])
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨⟨⟨_,hw⟩,_⟩,_⟩,he⟩,hf⟩,hp⟩,_⟩
    have hden : 6*w ≠ 0 := by linarith [hw.1]
    have hfactor : (6-2*w)*z-(3+2*w)*x+3-4*w ≠ 0 := by linarith
    rw [he, div_eq_zero_iff, mul_eq_zero]
    simp only [hfactor, hden, or_false, sq_eq_zero_iff]
    constructor <;> intro h <;> linarith

theorem second_rectangle_verified : secondRectangle.goal.eval model () :=
  secondRectangle.sound model _ second_rectangle_valid () trivial

theorem second_rectangle_correspondence : secondRectangle.goal.eval model () ↔
    ∀ w x z : ℝ, (1/2 ≤ w ∧ w ≤ 1) → (0 ≤ x ∧ x ≤ 1-w) →
      (w ≤ z ∧ z ≤ 1) → (deltaA w x z = 0 ↔ x+z=1) := by
  simp only [secondRectangle, Argument.goal, Expr.eval, Var.get, model, Ty.denote,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

def vocabulary : Vocabulary Symbol where
  key _ := "graph-slack"
  typeLatex _ := "\\mathbb{R}"
  noun _ := ""
  application
    | .delta, [w,x,z] => "\\Delta_{"++w++"}("++x++","++z++")"
    | .phi, [w,x] => "\\varphi_{"++w++"}("++x++")"
    | .psi, [w,z] => "\\psi_{"++w++"}("++z++")"
    | .sq, [x] => "\\left("++x++"\\right)^2"
    | .factor, [w,x,z] => "F_{"++w++"}("++x++","++z++")"
    | _, _ => "\\mathrm{unsupported}"

def documents : Json := Json.mkObj [
  (toString ``first_rectangle_valid, Json.mkObj [
    ("checked", checked_document% (vocabulary) first_rectangle_valid),
    ("title", .str "The first rectangle: the printed factorization and sign estimates"),
    ("correspondence", .str (toString ``first_rectangle_correspondence)),
    ("verified", .str (toString ``first_rectangle_verified)),
    ("definitionBridge", .str (toString ``delta_definition)),
    ("definition", .str ("\\Delta_w(x,z):=" ++ deltaDefinition.latex vocabulary ["z","x","w"]))
  ]),
  (toString ``second_rectangle_valid, Json.mkObj [
    ("checked", checked_document% (vocabulary) second_rectangle_valid),
    ("title", .str "The second rectangle: nonnegativity and its exact equality set"),
    ("correspondence", .str (toString ``second_rectangle_correspondence)),
    ("verified", .str (toString ``second_rectangle_verified)),
    ("definitionBridge", .str (toString ``factor_definition)),
    ("definition", .str ("F_w(x,z):=" ++ factorDefinition.latex vocabulary ["z","x","w"]))
  ])
]

#assert_lean_mirror_axioms second_rectangle_valid
#assert_lean_mirror_axioms second_rectangle_verified
#assert_lean_mirror_axioms second_rectangle_correspondence
#assert_lean_mirror_axioms factor_definition
#assert_lean_mirror_axioms first_rectangle_valid
#assert_lean_mirror_axioms first_rectangle_verified
#assert_lean_mirror_axioms first_rectangle_correspondence
#assert_lean_mirror_axioms delta_definition
end Papers.Rockel2026ExactBlest.ArticleCalculations
