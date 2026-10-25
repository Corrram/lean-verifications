import Papers.Rockel2026ExactBlest.ArticleBridge

/-! Presentation of the checked syntax trees. No proof dependencies are rendered. -/

namespace Papers.Rockel2026ExactBlest.ArticleBridge
open Companion

private def applyNotation (name : String) (args : List String) : String :=
  if args.isEmpty then name else name ++ "\\left(" ++ String.intercalate "," args ++ "\\right)"

private def typeLatex : Ty → String
  | .real => "\\mathbb{R}"
  | .unit => "[0,1]"
  | .prop => "\\mathrm{Prop}"
  | .base "Law" => "\\mathcal{P}([0,1]^2)"
  | .base "Measure" => "\\mathcal{M}([0,1])"
  | .base s => "\\mathrm{" ++ s ++ "}"
  | .fn a b => typeLatex a ++ "\\to " ++ typeLatex b

def foundationVocabulary : Vocabulary Foundation where
  key _ := "probability"
  typeLatex := typeLatex
  application
    | .first, [c] => "(\\pi_1)_*\\mu_{" ++ c ++ "}"
    | .second, [c] => "(\\pi_2)_*\\mu_{" ++ c ++ "}"
    | .uniform, [] => "\\lambda"
    | .lowerMass, [c, u, v] => "\\mu_{" ++ c ++ "}([0," ++ u ++ "]\\times[0," ++ v ++ "])"
    | .first, args => applyNotation "\\operatorname{marginal}_1" args
    | .second, args => applyNotation "\\operatorname{marginal}_2" args
    | .uniform, args => applyNotation "\\lambda" args
    | .lowerMass, args => applyNotation "\\operatorname{lowerMass}" args
  noun s := nomatch s

def coefficientVocabulary : Vocabulary CoefficientSymbol where
  key | .cdf => "cdf"
  typeLatex := typeLatex
  application
    | .cdf, [c, u, v] => applyNotation c [u, v]
    | .cdf, args => applyNotation "\\operatorname{CDF}" args
  noun s := nomatch s

def claimVocabulary : Vocabulary ClaimSymbol where
  key
    | .copula => "copula"
    | .rho => "rho"
    | .nu => "nu"
  typeLatex := typeLatex
  application
    | .copula, args => applyNotation "\\operatorname{Copula}" args
    | .rho, args => applyNotation "\\rho" args
    | .nu, args => applyNotation "\\nu" args
  noun | .copula => "bivariate copula"

/-- Only the probability-theoretic primitives are a manually documented foundation.
The paper's four definitions below are rendered from their evaluated syntax. -/
def makeDefinitionCards (linked : Bool) : List DefinitionCard := Id.run do
  let foundationVocabulary := if linked then foundationVocabulary.withDefinitionLinks
    else foundationVocabulary
  let coefficientVocabulary := if linked then coefficientVocabulary.withDefinitionLinks
    else coefficientVocabulary
  return [
  { key := "probability", title := "Probability conventions",
    latex := "Put $I=[0,1]$. We identify a copula with its probability law $\\mu_C$ on $I^2$. " ++
      "Write $\\lambda$ for Lebesgue probability measure on $I$, " ++
      "$\\pi_1(u,v)=u$ and $\\pi_2(u,v)=v$ for the coordinate projections, and " ++
      "$f_*\\mu(A)=\\mu(f^{-1}(A))$ for the pushforward of a measure. " ++
      "All displayed integrals use Lebesgue measure.",
    dependencies := [], bridge := "Foundation: probability measures, pushforwards, Lebesgue measure" },
  { key := "copula", title := "Bivariate copula",
    latex := "A probability law $\\mu_C$ on $I^2$ is a bivariate copula precisely when\n\\[" ++
      copulaDefinition.latex foundationVocabulary ["C"] ++ ".\\]",
    dependencies := copulaDefinition.symbols foundationVocabulary.key,
    bridge := toString ``copula_definition_equiv },
  { key := "cdf", title := "Distribution function",
    latex := "For $u,v\\in I$, the distribution function associated with $\\mu_C$ is\n\\[C(u,v):=" ++
      cdfDefinition.latex foundationVocabulary ["v", "u", "C"] ++ ".\\]",
    dependencies := cdfDefinition.symbols foundationVocabulary.key,
    bridge := toString ``cdf_definition_eq },
  { key := "rho", title := "Spearman's rho",
    latex := "\\[\\rho(C):=" ++ rhoDefinition.latex coefficientVocabulary ["C"] ++ ".\\]",
    dependencies := rhoDefinition.symbols coefficientVocabulary.key,
    bridge := toString ``rho_definition_eq },
  { key := "nu", title := "Blest's coefficient",
    latex := "\\[\\nu(C):=" ++ nuDefinition.latex coefficientVocabulary ["C"] ++ ".\\]",
    dependencies := nuDefinition.symbols coefficientVocabulary.key,
    bridge := toString ``nu_definition_eq }
  ]

def definitionCards : List DefinitionCard := makeDefinitionCards false

def selectedDefinitions : Except String (List DefinitionCard) :=
  definitionClosure definitionCards (articleStatement.symbols claimVocabulary.key)

def latexDocument : Except String String := do
  let cards ← selectedDefinitions
  let definitions := String.intercalate "\n\n" <| cards.map fun card =>
    "\\paragraph{" ++ card.title ++ ".} " ++ card.latex
  return "\\documentclass[11pt]{article}\n" ++
    "\\usepackage[a4paper,margin=24mm]{geometry}\n" ++
    "\\usepackage{amsmath,amssymb,amsthm}\n" ++
    "\\usepackage[T1]{fontenc}\n\\usepackage{lmodern}\n" ++
    "\\usepackage{xcolor}\n\\usepackage[colorlinks=true,urlcolor=blue]{hyperref}\n" ++
    "\\setlength{\\parindent}{0pt}\n\\setlength{\\parskip}{5pt}\n" ++
    "\\newtheorem*{checkedtheorem}{Theorem}\n\\begin{document}\n" ++
    "{\\Large\\bfseries A readable theorem with a Lean certificate}\\par\n" ++
    "{\\color{gray}Companion prototype $\\cdot$ Blest--Spearman bound}\\par\n\n" ++
    "\\begin{checkedtheorem}\n" ++ articleStatement.theoremLatex claimVocabulary ++
    "\\end{checkedtheorem}\n" ++
    "This is the universal inequality from Corollary~3.2 of " ++
    "\\href{https://arxiv.org/abs/2609.27634v1}{Rockel, arXiv:2609.27634v1}. " ++
    "The prototype covers the inequality; sharpness and equality cases are outside this certificate.\n\n" ++
    definitions ++ "\n\n\\medskip\\hrule\\medskip\n" ++
    "\\textbf{What is checked.} Lean checks the copula and coefficient correspondences, " ++
    "the equivalence of this statement with the existing theorem, and the resulting proof. " ++
    "The existing proof is \\texttt{nu\\_rho\\_bound}; the bridge is " ++
    "\\texttt{ArticleBridge.statement\\_equivalence}. " ++
    "The displayed formulas and interpreted propositions come from the same typed syntax trees.\n\n" ++
    "{\\small\\textbf{Presentation boundary.} The controlled-language parser, symbol notation, " ++
    "and LaTeX renderer are inspectable software, not themselves formally verified. " ++
    "The probability conventions above are the explicitly documented foundation vocabulary.}\n" ++
    "\\end{document}\n"

def certificateReport : Except String String := do
  let cards ← selectedDefinitions
  return String.intercalate "\n" <| [
    "Companion: Blest--Spearman inequality",
    "Source: arXiv:2609.27634v1, Corollary 3.2 (inequality only)",
    "Target: " ++ toString ``Papers.Rockel2026ExactBlest.nu_rho_bound,
    "Equivalence: " ++ toString ``statement_equivalence,
    "Final theorem: " ++ toString ``article_verified,
    "Foundational axioms allowed: propext, Classical.choice, Quot.sound",
    "Definition closure:"] ++ cards.map (fun card => "  " ++ card.key ++ ": " ++ card.bridge)

/-- Exported only after the module containing the checked certificate has compiled. -/
def companionJson : Except String Lean.Json := do
  let cards ← definitionClosure (makeDefinitionCards true)
    (articleStatement.symbols claimVocabulary.key)
  return Lean.Json.mkObj [
    ("schemaVersion", Lean.toJson (1 : Nat)),
    ("id", .str "blest-spearman"),
    ("title", .str "The Blest–Spearman bound"),
    ("source", .str "arXiv:2609.27634v1, Corollary 3.2 (universal inequality)"),
    ("sourceUrl", .str "https://arxiv.org/abs/2609.27634v1"),
    ("paperId", .str "Rockel2026ExactBlest"),
    ("statement", articleStatement.theoremJson claimVocabulary),
    ("definitions", .arr (cards.map DefinitionCard.toJson).toArray),
    ("target", .str (toString ``Papers.Rockel2026ExactBlest.nu_rho_bound)),
    ("targetModule", .str "Papers.Rockel2026ExactBlest.ExactBlest"),
    ("bridgeModule", .str "Papers.Rockel2026ExactBlest.ArticleBridge"),
    ("equivalence", .str (toString ``statement_equivalence)),
    ("verified", .str (toString ``article_verified)),
    ("allowedAxioms", Lean.toJson ["propext", "Classical.choice", "Quot.sound"]),
    ("scope", .str "The universal inequality for every bivariate copula, including singular copulas. Sharpness and equality cases are outside this certificate.")]

end Papers.Rockel2026ExactBlest.ArticleBridge
