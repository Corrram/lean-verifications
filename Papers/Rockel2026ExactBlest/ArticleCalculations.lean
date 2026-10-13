import Papers.Rockel2026ExactBlest.ArticleRectangleCalculus

namespace Papers.Rockel2026ExactBlest.ArticleCalculations
open LeanMirror Ty Lean
open ArticleOriginalProof

inductive Symbol : Ty → Type where
  | delta : Symbol (real ⇒ₘ real ⇒ₘ real ⇒ₘ real)
  | phi : Symbol (real ⇒ₘ real ⇒ₘ real)
  | psi : Symbol (real ⇒ₘ real ⇒ₘ real)
  | sq : Symbol (real ⇒ₘ real)
  | factor : Symbol (real ⇒ₘ real ⇒ₘ real ⇒ₘ real)
  | dx : Symbol (real ⇒ₘ real ⇒ₘ real ⇒ₘ real ⇒ₘ prop)
  | dz : Symbol (real ⇒ₘ real ⇒ₘ real ⇒ₘ real ⇒ₘ prop)
  | minimum : Symbol (real ⇒ₘ real ⇒ₘ real)

noncomputable def model : Model Symbol where
  base _ := Unit
  symbol
    | .delta => deltaA
    | .phi => paperPhiA
    | .psi => paperPsiA
    | .sq => fun t => t^2
    | .factor => fun w x z => (6-2*w)*z-(3+2*w)*x+3-4*w
    | .dx => fun w x z d => HasDerivAt (fun t => deltaA w t z) d x
    | .dz => fun w x z d => HasDerivAt (fun t => deltaA w x t) d z
    | .minimum => min
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
  Assume \frac{1}{2} \le w \land w < 1;
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
    exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hw.2.le))
      (sub_nonneg.mpr hz.2)
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨⟨_,hw⟩,_⟩,_⟩,he⟩,hf⟩,hp⟩
    rw [he]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (hp.trans hf)) (by linarith [hw.1])

theorem first_rectangle_verified : firstRectangle.goal.eval model () :=
  firstRectangle.sound model _ first_rectangle_valid () trivial

-- This correspondence is proved by interpreting the displayed statement only.
theorem first_rectangle_correspondence : firstRectangle.goal.eval model () ↔
    ∀ w x z : ℝ, (1/2 ≤ w ∧ w < 1) → (1-w ≤ x ∧ x ≤ 1) →
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
  Assume \frac{1}{2} \le w \land w < 1;
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
    exact graph_second_factor w x z hw.1 hw.2.le hx.2 hz.1
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
    ∀ w x z : ℝ, (1/2 ≤ w ∧ w < 1) → (0 ≤ x ∧ x ≤ 1-w) →
      (w ≤ z ∧ z ≤ 1) → (deltaA w x z = 0 ↔ x+z=1) := by
  simp only [secondRectangle, Argument.goal, Expr.eval, Var.get, model, Ty.denote,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

def thirdRectangle : Argument Symbol [] := [proof|
  Fix w : real named "w";
  Fix x : real named "x";
  Fix z : real named "z";
  Assume \frac{1}{2} \le w \land w < 1;
  Assume 0 \le x \land x \le 1-w;
  Assume 0 \le z \land z \le w;
  Have Forall t : real. (0 < t \land t < 1-w) \implies
    \dx(w,t,z,\frac{(t+z-1)*((3-2*w)*z-(3+2*w)*t+3-2*w)}{2*w});
  Have Forall t : real. (0 \le t \land t \le 1-w) \implies
    \frac{(t+z-1)*((3-2*w)*z-(3+2*w)*t+3-2*w)}{2*w} \le 0;
  Have \delta(w,1-w,z) \le \delta(w,x,z);
  Have Forall t : real. (0 < t \land t < w) \implies
    \dz(w,1-w,t,\frac{(0-(1-w))*t*(3*t-2*w)}{w});
  Have \delta(w,1-w,0)=0 \land \delta(w,1-w,w)=0;
  Have \minimum(\delta(w,1-w,0),\delta(w,1-w,w)) \le \delta(w,1-w,z);
  Conclude 0 \le \delta(w,x,z)]

theorem third_rectangle_valid : thirdRectangle.Valid model (fun _ => True) := by
  simp only [thirdRectangle, Argument.Valid, Expr.eval, Var.get, model, Ty.denote,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, zero_sub]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨_,hw⟩,_⟩,_⟩ t ht
    exact graph_derivative_00 w t z (by linarith [hw.1]) ht.2
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨_,hw⟩,_⟩,hz⟩,_⟩ t ht
    exact graph_derivative_00_nonpos w t z hw.1 hw.2.le ht.2 hz.1 hz.2
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨_,hw⟩,hx⟩,hz⟩,_⟩,_⟩
    exact graph_third_comparison w x z hw.1 hw.2.le hx hz
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨⟨_,hw⟩,_⟩,_⟩,_⟩,_⟩,_⟩ t ht
    exact graph_edge_derivative_z w t (by linarith [hw.1]) ht.2
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨⟨⟨_,hw⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩
    exact graph_third_endpoints w hw.1
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨⟨⟨⟨_,hw⟩,_⟩,hz⟩,_⟩,_⟩,_⟩,_⟩,_⟩
    exact graph_third_edge_minimum w z hw.1 hw.2.le hz
  · rintro ⟨z,x,w,⟨⟩⟩ h
    have hmin := h.2
    rw [h.1.2.1,h.1.2.2,min_self] at hmin
    exact hmin.trans h.1.1.1.2

theorem third_rectangle_verified : thirdRectangle.goal.eval model () :=
  thirdRectangle.sound model _ third_rectangle_valid () trivial

theorem third_rectangle_correspondence : thirdRectangle.goal.eval model () ↔
    ∀ w x z : ℝ, (1/2 ≤ w ∧ w < 1) → (0 ≤ x ∧ x ≤ 1-w) →
      (0 ≤ z ∧ z ≤ w) → 0 ≤ deltaA w x z := by
  simp only [thirdRectangle, Argument.goal, Expr.eval, Var.get, model, Ty.denote,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

def fourthRectangle : Argument Symbol [] := [proof|
  Fix w : real named "w";
  Fix x : real named "x";
  Fix z : real named "z";
  Assume \frac{1}{2} \le w \land w < 1;
  Assume 1-w \le x \land x \le 1;
  Assume w \le z \land z \le 1;
  Have Forall t : real. (w < t \land t < 1) \implies
    \dz(w,x,t,\frac{(x+t-1)*((3-w)*t-w*x-w)}{w});
  Have Forall t : real. (w \le t \land t \le 1) \implies
    0 \le \frac{(x+t-1)*((3-w)*t-w*x-w)}{w};
  Have \delta(w,x,w) \le \delta(w,x,z);
  Have Forall t : real. (1-w < t \land t < 1) \implies
    \dx(w,t,w,\frac{(1-t)*(2*w-1)*(3-2*w-3*t)}{2*w});
  Have \delta(w,1-w,w)=0 \land \delta(w,1,w)=0;
  Have \minimum(\delta(w,1-w,w),\delta(w,1,w)) \le \delta(w,x,w);
  Conclude 0 \le \delta(w,x,z)]

theorem fourth_rectangle_valid : fourthRectangle.Valid model (fun _ => True) := by
  simp only [fourthRectangle, Argument.Valid, Expr.eval, Var.get, model, Ty.denote,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨_,hw⟩,_⟩,_⟩ t ht
    exact graph_derivative_11 w x t (by linarith [hw.1]) ht.1
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨_,hw⟩,hx⟩,_⟩,_⟩ t ht
    exact graph_derivative_11_nonneg w x t hw.1 hw.2.le hx.1 hx.2 ht.1
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨_,hw⟩,hx⟩,hz⟩,_⟩,_⟩
    exact graph_fourth_comparison w x z hw.1 hw.2.le hx hz
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨⟨_,hw⟩,_⟩,_⟩,_⟩,_⟩,_⟩ t ht
    exact graph_edge_derivative_x w t (by linarith [hw.1]) ht.1
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨⟨⟨_,hw⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩
    exact graph_fourth_endpoints w hw.1 hw.2.le
  · rintro ⟨z,x,w,⟨⟩⟩ ⟨⟨⟨⟨⟨⟨⟨⟨_,hw⟩,hx⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩
    exact graph_fourth_edge_minimum w x hw.1 hw.2.le hx
  · rintro ⟨z,x,w,⟨⟩⟩ h
    have hmin := h.2
    rw [h.1.2.1,h.1.2.2,min_self] at hmin
    exact hmin.trans h.1.1.1.2

theorem fourth_rectangle_verified : fourthRectangle.goal.eval model () :=
  fourthRectangle.sound model _ fourth_rectangle_valid () trivial

theorem fourth_rectangle_correspondence : fourthRectangle.goal.eval model () ↔
    ∀ w x z : ℝ, (1/2 ≤ w ∧ w < 1) → (1-w ≤ x ∧ x ≤ 1) →
      (w ≤ z ∧ z ≤ 1) → 0 ≤ deltaA w x z := by
  simp only [fourthRectangle, Argument.goal, Expr.eval, Var.get, model, Ty.denote,
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
    | .dx, [w,x,z,d] => "\\partial_x\\Delta_{"++w++"}("++x++","++z++")="++d
    | .dz, [w,x,z,d] => "\\partial_z\\Delta_{"++w++"}("++x++","++z++")="++d
    | .minimum, [x,y] => "\\min\\{"++x++","++y++"\\}"
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
  ]),
  (toString ``third_rectangle_valid, Json.mkObj [
    ("checked", checked_document% (vocabulary) third_rectangle_valid),
    ("title", .str "The third rectangle: decrease in x and the edge minimum"),
    ("correspondence", .str (toString ``third_rectangle_correspondence)),
    ("verified", .str (toString ``third_rectangle_verified)),
    ("definitionBridge", .str (toString ``delta_definition)),
    ("definition", .str ("\\Delta_w(x,z):=" ++ deltaDefinition.latex vocabulary ["z","x","w"] ++
      ".\\quad\\partial_x\\Delta_w(x,z)=d\\text{ means its derivative exists and equals }d"))
  ]),
  (toString ``fourth_rectangle_valid, Json.mkObj [
    ("checked", checked_document% (vocabulary) fourth_rectangle_valid),
    ("title", .str "The fourth rectangle: increase in z and the edge minimum"),
    ("correspondence", .str (toString ``fourth_rectangle_correspondence)),
    ("verified", .str (toString ``fourth_rectangle_verified)),
    ("definitionBridge", .str (toString ``delta_definition)),
    ("definition", .str ("\\Delta_w(x,z):=" ++ deltaDefinition.latex vocabulary ["z","x","w"] ++
      ".\\quad\\partial_z\\Delta_w(x,z)=d\\text{ means its derivative exists and equals }d"))
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
#assert_lean_mirror_axioms third_rectangle_valid
#assert_lean_mirror_axioms third_rectangle_verified
#assert_lean_mirror_axioms third_rectangle_correspondence
#assert_lean_mirror_axioms fourth_rectangle_valid
#assert_lean_mirror_axioms fourth_rectangle_verified
#assert_lean_mirror_axioms fourth_rectangle_correspondence
end Papers.Rockel2026ExactBlest.ArticleCalculations
