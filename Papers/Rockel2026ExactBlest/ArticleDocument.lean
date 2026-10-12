import Papers.Rockel2026ExactBlest.ArticleProof
import Papers.Rockel2026ExactBlest.ArticlePresentation

namespace Papers.Rockel2026ExactBlest.ArticleProof
open Lean LeanMirror

private def call (name : String) (args : List String) :=
  if args.isEmpty then name else name ++ "(" ++ String.intercalate "," args ++ ")"

def vocabulary : Vocabulary Symbol where
  key
    | .rho => "rho" | .nu => "nu" | .Phi => "phi"
    | .negBranch => "left-branch" | .posBranch => "right-branch"
    | .power | .minimum | .derivative | .increasing | .decreasing => "calculus"
    | .D => "extremizer" | .survival => "survival"
    | .tentMap => "tent" | .veeMap => "vee" | .graph => "graph"
    | .cdf => "cdf" | .reflectUnit => "probability"
  typeLatex
    | .real => "\\mathbb{R}"
    | .unit => "[0,1]"
    | .base "Copula" => "\\mathcal{C}"
    | _ => "\\mathrm{Object}"
  application
    | .rho, args => call "\\rho" args
    | .nu, args => call "\\nu" args
    | .Phi, args => call "\\Phi" args
    | .negBranch, args => call "g_-" args
    | .posBranch, args => call "g_+" args
    | .D, _ => "D_{1/2}"
    | .survival, [c] => "\\widehat{" ++ c ++ "}"
    | .power, [x,y] => "\\left(" ++ x ++ "\\right)^{" ++ y ++ "}"
    | .minimum, [x,y] => "\\min\\{" ++ x ++ "," ++ y ++ "\\}"
    | .derivative, [f,r,d] => f ++ "'(" ++ r ++ ")=" ++ d
    | .increasing, [f,a,b] => f ++ "\\text{ is strictly increasing on }[" ++ a ++ "," ++ b ++ "]"
    | .decreasing, [f,a,b] => f ++ "\\text{ is strictly decreasing on }[" ++ a ++ "," ++ b ++ "]"
    | .tentMap, args => call "T" args
    | .veeMap, args => call "V" args
    | .graph, [c,f] => "\\mu_{" ++ c ++ "}(\\{(u,v):v=" ++ f ++ "(u)\\})=1"
    | .cdf, [c,u,v] => call c [u,v]
    | .reflectUnit, [u] => "(1-" ++ u ++ ")"
    | _, _ => "\\mathrm{unsupported}"
  noun _ := ""

def proofDefinitionCards (linked : Bool) : List DefinitionCard := Id.run do
  let v := if linked then vocabulary.withDefinitionLinks else vocabulary
  return [
    {key := "calculus", title := "Real powers and derivatives",
     latex := "Real powers have their usual nonnegative-base meaning in this proof. " ++
       "$f'(r)=d$ asserts that the derivative exists and equals $d$. Strict increase on $[a,b]$ " ++
       "means $f(x)<f(y)$ whenever $a\\le x<y\\le b$; strict decrease reverses that inequality.",
     dependencies := [], bridge := "Foundation: Real.rpow, HasDerivAt, StrictMonoOn, StrictAntiOn, min"},
    {key := "left-branch", title := "The negative branch of the deviation",
     latex := "For $r\\in[-1,0]$,\\[g_-(r):=" ++ leftDefinition.latex v ["r"] ++ ".\\]",
     dependencies := ["calculus"], bridge := toString ``left_definition},
    {key := "right-branch", title := "The positive branch of the deviation",
     latex := "For $r\\in[0,1]$,\\[g_+(r):=" ++ rightDefinition.latex v ["r"] ++ ".\\]",
     dependencies := ["calculus"], bridge := toString ``right_definition},
    {key := "phi", title := "The upper boundary (equation 4)",
     latex := "For $r\\in[-1,1]$,\\[\\Phi(r)-r=\\begin{cases}g_-(r),&-1\\le r\\le0,\\\\g_+(r),&0\\le r\\le1.\\end{cases}\\] " ++
       "The two branches agree at zero. These are the two expressions used in the original proof.",
     dependencies := ["left-branch", "right-branch"], bridge := toString ``phi_definition},
    {key := "tent", title := "The tent map",
     latex := "For $u\\in[0,1]$,\\[T(u):=" ++ tentDefinition.latex v ["u"] ++ ".\\]",
     dependencies := ["calculus"], bridge := toString ``tent_definition},
    {key := "vee", title := "The reflected tent map",
     latex := "For $u\\in[0,1]$,\\[V(u):=" ++ veeDefinition.latex v ["u"] ++ ".\\]",
     dependencies := [], bridge := toString ``vee_definition},
    {key := "graph", title := "Supported on a graph",
     latex := "The statement that a copula is supported on the graph of $f$ means " ++
       "$v=f(u)$ for $\\mu_C$-almost every $(u,v)$, equivalently " ++
       "$\\mu_C(\\{(u,v):v=f(u)\\})=1$. Both maps here are continuous.",
     dependencies := ["copula", "probability"], bridge := "Foundation: ArticleProof.OnGraph, almost-everywhere equality"},
    {key := "extremizer", title := "The extremal copula",
     latex := "$D_{1/2}$ is the law of $(U,T(U))$ for $U$ uniform on $[0,1]$. " ++
       "The checked law identity identifies it with the paper's $D_c$ at $c=1/2$.",
     dependencies := ["tent", "copula"], bridge := toString ``extremizer_definition},
    {key := "survival", title := "The survival copula (equation 8)",
     latex := "The survival copula of $C$ is the law of $(1-U,1-V)$ when $(U,V)$ has law $C$. " ++
       "Its distribution function is\\[\\widehat C(u,v)=" ++
       survivalDefinition.latex v ["v","u","C"] ++ ".\\]",
     dependencies := ["copula", "cdf", "probability"], bridge := toString ``survival_definition}
  ]

def documentJson : Json := Json.mkObj [
  ("schemaVersion", toJson (1 : Nat)),
  ("results", toJson ([Json.mkObj [
    ("id", .str "corollary-3-2"),
    ("title", .str "Corollary 3.2. Sharp deviation between nu and rho"),
    ("certificate", .str (toString ``corollary_valid)),
    ("correspondence", .str (toString ``full_correspondence)),
    ("verified", .str (toString ``corollary_verified)),
    ("target", .str "nu_rho_bound; paper_nu_rho_max_unique; paper_nu_rho_min_unique; rho_midpoint_original_graph; rho_midpoint_reflected_graph"),
    ("checked", checked_document% (vocabulary.withDefinitionLinks) corollary_valid)
  ]] : List Json))]

/-- Extends the existing statement companion with an audited proof document. -/
def fullCompanionJson : Except String Json := do
  let .obj old ← ArticleBridge.companionJson | throw "expected a companion object"
  let cards := ArticleBridge.makeDefinitionCards true ++ proofDefinitionCards true
  let ordered ← definitionClosure cards (cards.map (·.key))
  return .obj <| (old.insert "document" documentJson).insert "definitions"
    (toJson (ordered.map DefinitionCard.toJson)) |>.insert "scope"
      (.str "Corollary 3.2 in full: universal bound, both unique extremizers, attainment, and support graphs, with a checked version of its printed proof. Earlier results used in the proof are checked library dependencies; the rest of the article is not reproduced as a LeanMirror document.")
    |>.insert "source" (.str "arXiv:2609.27634v1, Corollary 3.2 and its proof")

end Papers.Rockel2026ExactBlest.ArticleProof
