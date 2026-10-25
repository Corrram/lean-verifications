import Companion
import Papers.Rockel2026ExactBlest.ExactBlest

/-! # An article-facing certificate for the inequality in Corollary 3.2

Source: arXiv:2609.27634v1, equations (1), (2), and the bound in Corollary 3.2.
This prototype certifies the universal inequality, not the corollary's sharpness
or equality classification. Its input domain is all probability laws on the
unit square, restricted by a separately interpreted uniform-marginal definition.
The existing theorem instead quantifies over the bundled `Copula 2` type.
-/

namespace Papers.Rockel2026ExactBlest.ArticleBridge

open Companion MeasureTheory ProbabilityTheory
open scoped unitInterval

abbrev law : Ty := .base "Law"
abbrev measure : Ty := .base "Measure"
abbrev Law := ProbabilityMeasure (Fin 2 → I)

def base : String → Type
  | "Law" => Law
  | "Measure" => Measure I
  | _ => PUnit

/-! The foundation vocabulary consists of probability, coordinate projection,
uniform Lebesgue measure, and the mass of a closed lower rectangle. -/
inductive Foundation : Ty → Type where
  | first : Foundation (law ⇒ₘ measure)
  | second : Foundation (law ⇒ₘ measure)
  | uniform : Foundation measure
  | lowerMass : Foundation (law ⇒ₘ .unit ⇒ₘ .unit ⇒ₘ .real)

noncomputable def foundationModel : Model Foundation where
  base := base
  symbol
    | .first => fun C => C.toMeasure.map (fun x => x 0)
    | .second => fun C => C.toMeasure.map (fun x => x 1)
    | .uniform => volume
    | .lowerMass => fun C u v => C.toMeasure.real (Set.Iic ![u, v])

open Foundation in
def copulaDefinition : Expr Foundation [law] .prop :=
  [math| C |- \first(C) = \uniform \land \second(C) = \uniform]

open Foundation in
def cdfDefinition : Expr Foundation [.unit, .unit, law] .real :=
  [math| C, u, v |- \lowerMass(C, u, v)]

noncomputable def IsCopula (C : Law) : Prop :=
  copulaDefinition.eval foundationModel (C, ())

noncomputable def articleCDF (C : Law) (u v : I) : ℝ :=
  cdfDefinition.eval foundationModel (v, u, C, ())

/-- The printed rectangle really is the event used by the probability primitive. -/
theorem lower_rectangle_eq (u v : I) :
    Set.Iic ![u, v] = {x : Fin 2 → I | x 0 ≤ u ∧ x 1 ≤ v} := by
  ext x
  simp [Set.mem_Iic, Pi.le_def, Fin.forall_fin_two]

theorem cdf_rectangle_formula (C : Law) (u v : I) :
    articleCDF C u v = C.toMeasure.real {x : Fin 2 → I | x 0 ≤ u ∧ x 1 ≤ v} := by
  change C.toMeasure.real (Set.Iic ![u, v]) = _
  rw [lower_rectangle_eq]

/-- Every law admitted by the article definition gives an existing library copula. -/
def toLean (C : Law) (h : IsCopula C) : Copula 2 where
  measure := C
  marginal_eq i := by
    fin_cases i
    · exact h.1
    · exact h.2

theorem fromLean_valid (C : Copula 2) : IsCopula C.measure :=
  ⟨C.marginal_eq 0, C.marginal_eq 1⟩

theorem toLean_fromLean (C : Copula 2) : toLean C.measure (fromLean_valid C) = C := by
  apply Copula.ext
  rfl

theorem fromLean_toLean (C : Law) (h : IsCopula C) : (toLean C h).measure = C := rfl

/-- Object-definition equivalence, including coverage in both directions. -/
theorem copula_definition_equiv (C : Law) :
    IsCopula C ↔ ∃ D : Copula 2, D.measure = C := by
  constructor
  · intro h
    exact ⟨toLean C h, rfl⟩
  · rintro ⟨D, rfl⟩
    exact fromLean_valid D

theorem cdf_definition_eq (C : Law) (h : IsCopula C) (u v : I) :
    articleCDF C u v = (toLean C h).cdf ![u, v] := rfl

/-! Definition stages have different symbol types: coefficient definitions can
refer to the CDF, but cannot refer to themselves or to the theorem. -/
inductive CoefficientSymbol : Ty → Type where
  | cdf : CoefficientSymbol (law ⇒ₘ .unit ⇒ₘ .unit ⇒ₘ .real)

noncomputable def coefficientModel : Model CoefficientSymbol where
  base := base
  symbol | .cdf => articleCDF

open CoefficientSymbol in
def rhoDefinition : Expr CoefficientSymbol [law] .real :=
  [math| C |- 12 * \int_{0}^{1}{v}{\int_{0}^{1}{u}{\cdf(C, u, v)}} - 3]

open CoefficientSymbol in
def nuDefinition : Expr CoefficientSymbol [law] .real :=
  [math| C |- 24 * \int_{0}^{1}{v}{\int_{0}^{1}{u}{(1 - \real{u}) * \cdf(C, u, v)}} - 2]

noncomputable def articleRho (C : Law) : ℝ := rhoDefinition.eval coefficientModel (C, ())
noncomputable def articleNu (C : Law) : ℝ := nuDefinition.eval coefficientModel (C, ())

theorem rho_definition_eq (C : Law) (h : IsCopula C) :
    articleRho C = (toLean C h).spearmanRho := by
  let D := toLean C h
  change 12 * (∫ v : I, ∫ u : I, D.cdf ![u, v]) - 3 = D.spearmanRho
  rw [D.spearmanRho_eq_integral_cdf, Copula.toMeasure_independence]
  have hm := ((volume_preserving_finTwoArrow I).symm MeasurableEquiv.finTwoArrow).integral_comp
    MeasurableEquiv.finTwoArrow.symm.measurableEmbedding D.cdf
  have hi : Integrable (fun p : I × I => D.cdf ![p.1, p.2])
      ((volume : Measure I).prod volume) :=
    (D.continuous_cdf.comp (by fun_prop)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  congr 2
  change (∫ v : I, ∫ u : I, D.cdf ![u, v]) = ∫ x : Fin 2 → I, D.cdf x
  rw [← hm]
  exact (integral_prod_symm _ hi).symm

theorem nu_definition_eq (C : Law) (h : IsCopula C) :
    articleNu C = Papers.Rockel2026XiBlest.blestNu (toLean C h) := by
  simpa only [articleNu, nuDefinition, Expr.eval, coefficientModel, articleCDF,
    cdfDefinition, foundationModel, Var.get, Nat.cast_one, Nat.cast_ofNat, Copula.cdf, Copula.toMeasure,
    toLean] using (Papers.Rockel2026XiBlest.blest_integral_formula (toLean C h)).symm

inductive ClaimSymbol : Ty → Type where
  | copula : ClaimSymbol (law ⇒ₘ .prop)
  | rho : ClaimSymbol (law ⇒ₘ .real)
  | nu : ClaimSymbol (law ⇒ₘ .real)

noncomputable def articleModel : Model ClaimSymbol where
  base := base
  symbol
    | .copula => IsCopula
    | .rho => articleRho
    | .nu => articleNu

open ClaimSymbol in
def articleStatement : Expr ClaimSymbol [] .prop :=
  [math| |- Let C be copula. \abs{\nu(C) - \rho(C)} \le \frac{1}{4}]

/-- Extracted from the existing declaration, never maintained as a duplicate statement. -/
def LeanStatement : Prop := statement_of% Papers.Rockel2026ExactBlest.nu_rho_bound

/-- Stronger than an iff between established truths: this is a pointwise
correspondence derived entirely from the definition bridges. -/
theorem bound_correspondence (C : Law) (h : IsCopula C) (b : ℝ) :
    |articleNu C - articleRho C| ≤ b ↔
      |Papers.Rockel2026XiBlest.blestNu (toLean C h) - (toLean C h).spearmanRho| ≤ b := by
  rw [nu_definition_eq C h, rho_definition_eq C h]

/-- Neither direction uses the established inequality. -/
theorem statement_equivalence : articleStatement.eval articleModel () ↔ LeanStatement := by
  simp only [articleStatement, Expr.eval, articleModel, Var.get, Nat.cast_one]
  change (∀ C : Law, IsCopula C → |articleNu C - articleRho C| ≤ 1 / 4) ↔ _
  constructor
  · intro h C
    have he := (bound_correspondence C.measure (fromLean_valid C) (1 / 4)).mp
      (h C.measure (fromLean_valid C))
    simpa only [toLean_fromLean] using he
  · intro h C hC
    exact (bound_correspondence C hC (1 / 4)).mpr (h (toLean C hC))

theorem certificate : Certificate articleModel articleStatement LeanStatement :=
  ⟨statement_equivalence, Papers.Rockel2026ExactBlest.nu_rho_bound⟩

theorem article_verified : articleStatement.eval articleModel () := certificate.proved

#assert_companion_axioms copula_definition_equiv
#assert_companion_axioms lower_rectangle_eq
#assert_companion_axioms cdf_rectangle_formula
#assert_companion_axioms cdf_definition_eq
#assert_companion_axioms rho_definition_eq
#assert_companion_axioms nu_definition_eq
#assert_companion_axioms fromLean_toLean
#assert_companion_axioms toLean_fromLean
#assert_companion_axioms bound_correspondence
#assert_companion_axioms statement_equivalence
#assert_companion_axioms certificate
#assert_companion_axioms article_verified

end Papers.Rockel2026ExactBlest.ArticleBridge
