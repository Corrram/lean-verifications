import LeanMirror
import Papers.Rockel2026XiBlest.Main

namespace Papers.Rockel2026XiBlest.ArticleCalculations
open LeanMirror Ty Lean Verification

inductive Symbol : Ty → Type where
  | F : Symbol (real ⇒ₘ real ⇒ₘ real)
  | sq : Symbol (real ⇒ₘ real)
  | cube : Symbol (real ⇒ₘ real)
  | fourth : Symbol (real ⇒ₘ real)
  | fifth : Symbol (real ⇒ₘ real)

noncomputable def model : Model Symbol where
  base _ := Unit
  symbol
    | .F => quadraticF
    | .sq => fun x => x^2
    | .cube => fun x => x^3
    | .fourth => fun x => x^4
    | .fifth => fun x => x^5
open Symbol

-- The primitive used in the printed section integrals, independently encoded.
def primitiveDefinition : Expr Symbol [real,real] real :=
  [math| q,t |- \frac{\fifth(t)}{5}-\frac{2*q}{3}*\cube(t)+\sq(q)*t]

theorem primitive_definition (q t : ℝ) :
    primitiveDefinition.eval model (t,q,()) = quadraticF q t := rfl

-- This is explicitly the corrected calculation, not a certificate of the
-- false coefficient in arXiv v1. The original line is retained by the reader.
def lowerSquare : Argument Symbol [] := [proof|
  Fix r : real named "r";
  Have \F(\sq(r),1)=\frac{1}{5}-\frac{2*\sq(r)}{3}+\fourth(r);
  Have \F(\sq(r),r)=\frac{8*\fifth(r)}{15};
  Conclude \F(\sq(r),1)-\F(\sq(r),r)=
    \frac{1}{5}-\frac{2*\sq(r)}{3}+\fourth(r)-\frac{8*\fifth(r)}{15}]

theorem lower_square_valid : lowerSquare.Valid model (fun _ => True) := by
  simp only [lowerSquare, Argument.Valid, Expr.eval, Var.get, model, Ty.denote,
    Nat.cast_ofNat, Nat.cast_one]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨r,⟨⟩⟩ _
    unfold quadraticF
    ring
  · rintro ⟨r,⟨⟩⟩ _
    unfold quadraticF
    ring
  · rintro ⟨r,⟨⟩⟩ ⟨⟨_,h₁⟩,h₂⟩
    rw [h₁,h₂]

theorem lower_square_verified : lowerSquare.goal.eval model () :=
  lowerSquare.sound model _ lower_square_valid () trivial

theorem lower_square_correspondence : lowerSquare.goal.eval model () ↔
    ∀ r : ℝ, quadraticF (r^2) 1-quadraticF (r^2) r =
      1/5-2*r^2/3+r^4-8*r^5/15 := by
  simp only [lowerSquare, Argument.goal, Expr.eval, Var.get, model, Ty.denote,
    Nat.cast_ofNat, Nat.cast_one]

def vocabulary : Vocabulary Symbol where
  key _ := "section-primitive"
  typeLatex _ := "\\mathbb{R}"
  noun _ := ""
  application
    | .F, [q,t] => "F("++t++";"++q++")"
    | .sq, [x] => "\\left("++x++"\\right)^2"
    | .cube, [x] => "\\left("++x++"\\right)^3"
    | .fourth, [x] => "\\left("++x++"\\right)^4"
    | .fifth, [x] => "\\left("++x++"\\right)^5"
    | _, _ => "\\mathrm{unsupported}"

def documents : Json := Json.mkObj [
  (toString ``lower_square_valid, Json.mkObj [
    ("checked", checked_document% (vocabulary) lower_square_valid),
    ("title", .str "Corrected lower-clamped square moment: where the coefficient comes from"),
    ("correspondence", .str (toString ``lower_square_correspondence)),
    ("verified", .str (toString ``lower_square_verified)),
    ("definitionBridge", .str (toString ``primitive_definition)),
    ("definition", .str ("F(t;q):=" ++ primitiveDefinition.latex vocabulary ["t","q"]))
  ])
]

#assert_lean_mirror_axioms primitive_definition
#assert_lean_mirror_axioms lower_square_valid
#assert_lean_mirror_axioms lower_square_verified
#assert_lean_mirror_axioms lower_square_correspondence
end Papers.Rockel2026XiBlest.ArticleCalculations
