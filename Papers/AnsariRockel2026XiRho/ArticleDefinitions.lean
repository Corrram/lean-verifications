import LeanMirror
import Papers.AnsariRockel2026XiRho.Main

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
namespace Papers.AnsariRockel2026XiRho.ArticleDefinitions
open LeanMirror Ty Lean
abbrev copula : Ty := .base "copula"
abbrev curve : Ty := .base "curve"

noncomputable def quarter : I := ⟨1/4,by norm_num⟩

-- A decreasing function that differs from the constant 1/2 only at zero.
noncomputable def endpointSample (t : I) : ℝ := if t=0 then 1 else 1/2

theorem sample_antitone : Antitone endpointSample := by
  intro a b hab
  by_cases ha : a=0
  · subst a
    simp only [endpointSample]
    split_ifs <;> norm_num
  · have hb : b≠0 := by
      intro hb
      exact ha (le_antisymm (hb ▸ hab) (by exact bot_le))
    simp [endpointSample,ha,hb]

theorem sample_bounded (t : I) : endpointSample t ∈ Icc 0 1 := by
  unfold endpointSample
  split_ifs <;> norm_num

theorem sample_ae_constant : endpointSample =ᵐ[volume] (fun _ => (1/2:ℝ)) := by
  filter_upwards [volume.ae_ne (0:I)] with t ht
  simp [endpointSample,ht]

theorem sample_mean : (∫ t : I, endpointSample t) = 1/2 := by
  rw [integral_congr_ae sample_ae_constant]
  simp

theorem sample_functional : decreasingFunctional endpointSample = 1/4 := by
  unfold decreasingFunctional
  have he : (fun t : I => 2*((1-(t:ℝ))*endpointSample t)-endpointSample t^2)
      =ᵐ[volume] (fun t => (3/4:ℝ)-(t:ℝ)) := by
    filter_upwards [sample_ae_constant] with t ht
    rw [ht]
    ring
  rw [integral_congr_ae he,integral_sub (integrable_const _)
    (Copula.integrable_continuous_unit volume continuous_subtype_val),
    integral_const,Copula.integral_unit_id]
  norm_num

theorem sample_values : endpointSample 0 ≠ (1/2:ℝ) ∧ endpointSample quarter ≠ 1 := by
  have hq : quarter ≠ 0 := by
    intro h
    have := congrArg (fun t : I => (t:ℝ)) h
    norm_num [quarter] at this
  norm_num [endpointSample,hq]

theorem pointwise_counterexample : ∃ h : I → ℝ,
    Antitone h ∧ (∀ t : I,0 ≤ h t ∧ h t ≤ 1) ∧
    (∫ t : I,h t)=1/2 ∧ decreasingFunctional h=1/4 ∧
    h 0 ≠ 1/2 ∧ h quarter ≠ 1 :=
  ⟨endpointSample,sample_antitone,sample_bounded,sample_mean,sample_functional,sample_values⟩

inductive Symbol : Ty → Type where
  | xi : Symbol (copula ⇒ₘ real)
  | rho : Symbol (copula ⇒ₘ real)
  | cdf : Symbol (copula ⇒ₘ unit ⇒ₘ unit ⇒ₘ real)
  | partialCDF : Symbol (copula ⇒ₘ unit ⇒ₘ unit ⇒ₘ real)
  | si : Symbol (copula ⇒ₘ prop)
  | sd : Symbol (copula ⇒ₘ prop)
  | wCopula : Symbol copula
  | piCopula : Symbol copula
  | mCopula : Symbol copula
  | square : Symbol (real ⇒ₘ real)
  | minimum : Symbol (real ⇒ₘ real ⇒ₘ real)
  | maximum : Symbol (real ⇒ₘ real ⇒ₘ real)
  | value : Symbol (curve ⇒ₘ unit ⇒ₘ real)
  | decreasing : Symbol (curve ⇒ₘ prop)
  | functional : Symbol (curve ⇒ₘ real)
  | sample : Symbol curve
  | zero : Symbol unit
  | quarterPoint : Symbol unit
  | half : Symbol unit
  | indicator : Symbol (unit ⇒ₘ unit ⇒ₘ real)
  | different : Symbol (real ⇒ₘ real ⇒ₘ prop)

noncomputable def model : Model Symbol where
  base
    | "copula" => Copula 2
    | "curve" => I → ℝ
    | _ => Unit
  symbol
    | .xi => Copula.chatterjeeXi
    | .rho => Copula.spearmanRho
    | .cdf => fun C u v => C.cdf ![u,v]
    | .partialCDF => fun C u v => deriv (C.cdfSection v) (u:ℝ)
    | .si => Copula.IsSI
    | .sd => Copula.IsSD
    | .wCopula => Copula.countermonotonic
    | .piCopula => Copula.independence 2
    | .mCopula => Copula.comonotonic 2
    | .square => fun x => x^2
    | .minimum => min
    | .maximum => max
    | .value => fun h t => h t
    | .decreasing => Antitone
    | .functional => decreasingFunctional
    | .sample => endpointSample
    | .zero => 0
    | .quarterPoint => quarter
    | .half => Copula.unitHalf
    | .indicator => fun v t => (Iic v).indicator (fun _ => (1:ℝ)) t
    | .different => fun x y => x≠y
open Symbol

def xiDefinition : Expr Symbol [copula] real :=
  [math| C |- 6*\int_{0}^{1}{v}{\int_{0}^{1}{t}{\square(\partialCDF(C,t,v))}}-2]
theorem xi_definition (C : Copula 2) : xiDefinition.eval model (C,())=C.chatterjeeXi := by
  simpa only [xiDefinition,Expr.eval,Var.get,model,Ty.denote,Nat.cast_ofNat] using
    (xi_derivative_formula C).symm

def rhoDefinition : Expr Symbol [copula] real :=
  [math| C |- 12*\int_{0}^{1}{v}{\int_{0}^{1}{u}{\cdf(C,u,v)}}-3]
theorem rho_definition (C : Copula 2) : rhoDefinition.eval model (C,())=C.spearmanRho := by
  simpa only [rhoDefinition,Expr.eval,Var.get,model,Ty.denote,Nat.cast_ofNat] using
    (Verification.spearmanRho_eq_iterated_cdf C).symm

def siDefinition : Expr Symbol [copula] prop :=
  [math| C |- Forall a : unit. Forall b : unit. Forall c : unit. Forall v : unit.
    (\real{a} \le \real{b} \land \real{b} \le \real{c}) \implies
      (\real{b}-\real{a})*\cdf(C,c,v)+(\real{c}-\real{b})*\cdf(C,a,v)
        \le (\real{c}-\real{a})*\cdf(C,b,v)]
theorem si_definition (C : Copula 2) : siDefinition.eval model (C,()) ↔ C.IsSI := by
  simp only [siDefinition,Expr.eval,Var.get,model,Ty.denote,Copula.IsSI,
    and_imp]
  rfl

def sdDefinition : Expr Symbol [copula] prop :=
  [math| C |- Forall a : unit. Forall b : unit. Forall c : unit. Forall v : unit.
    (\real{a} \le \real{b} \land \real{b} \le \real{c}) \implies
      (\real{c}-\real{a})*\cdf(C,b,v) \le
        (\real{b}-\real{a})*\cdf(C,c,v)+(\real{c}-\real{b})*\cdf(C,a,v)]
theorem sd_definition (C : Copula 2) : sdDefinition.eval model (C,()) ↔ C.IsSD := by
  simp only [sdDefinition,Expr.eval,Var.get,model,Ty.denote,Copula.IsSD,
    and_imp]
  rfl

def benchmarkDefinitions : Expr Symbol [] prop :=
  [math| |- Forall u : unit. Forall v : unit.
    \cdf(\piCopula,u,v)=\real{u}*\real{v} \land
    \cdf(\mCopula,u,v)=\minimum(\real{u},\real{v}) \land
    \cdf(\wCopula,u,v)=\maximum(0,\real{u}+\real{v}-1)]
theorem benchmark_definitions : benchmarkDefinitions.eval model () := by
  simp only [benchmarkDefinitions,Expr.eval,Var.get,model,Ty.denote,Nat.cast_zero,Nat.cast_one]
  intro u v
  refine ⟨?_,?_,?_⟩
  · simp [Copula.cdf_independence,Fin.prod_univ_two]
  · simpa only [Matrix.cons_val_zero,Matrix.cons_val_one] using
      (Copula.cdf_comonotonic_two ![u,v])
  · simp [Copula.cdf_countermonotonic]

def monotoneStatement : Argument Symbol [] := [proof|
  Fix C : copula named "C";
  Assume \si(C) \lor \sd(C);
  Conclude \xi(C) \le \abs{\rho(C)} \land
    (\xi(C)=\abs{\rho(C)} \iff C=\wCopula \lor C=\piCopula \lor C=\mCopula)]

-- This is statement reuse, not a certificate for the source maximum-principle proof.
theorem monotone_statement_valid : monotoneStatement.Valid model (fun _ => True) := by
  simp only [monotoneStatement,Argument.Valid,Expr.eval,Var.get,model,Ty.denote]
  exact fun ⟨C,⟨⟩⟩ h => ⟨stochastic_xi_le_abs_rho C h.2,stochastic_xi_eq_abs_rho_iff C h.2⟩
theorem monotone_statement_verified : monotoneStatement.goal.eval model () :=
  monotoneStatement.sound model _ monotone_statement_valid () trivial
def existingMonotone : Prop :=
  statement_of% stochastic_xi_le_abs_rho ∧ statement_of% stochastic_xi_eq_abs_rho_iff
theorem monotone_statement_correspondence : monotoneStatement.goal.eval model () ↔ existingMonotone := by
  simp only [monotoneStatement,Argument.goal,Expr.eval,Var.get,model,Ty.denote,existingMonotone]
  constructor
  · intro h
    exact ⟨fun C hc => (h C hc).1, fun C hc => (h C hc).2⟩
  · rintro ⟨h₁,h₂⟩ C hc
    exact ⟨h₁ C hc,h₂ C hc⟩

def functionalDefinition : Expr Symbol [curve] real :=
  [math| h |- \int_{0}^{1}{t}{2*(1-\real{t})*\value(h,t)-\square(\value(h,t))}]
theorem functional_definition (h : I → ℝ) : functionalDefinition.eval model (h,())=decreasingFunctional h := by
  simp only [functionalDefinition,Expr.eval,Var.get,model,Ty.denote,Nat.cast_ofNat,Nat.cast_one]
  unfold decreasingFunctional
  congr 1
  funext t
  ring

def literalPointwiseLemma : Expr Symbol [] prop :=
  [math| |- Forall v : unit. Forall h : curve.
    (\decreasing(h) \land (Forall t : unit. 0 \le \value(h,t) \land \value(h,t) \le 1) \land
      \int_{0}^{1}{t}{\value(h,t)}=\real{v}) \implies
    (\functional(h)=\real{v}*(1-\real{v}) \iff
      (Forall t : unit. \value(h,t)=\indicator(v,t)) \lor
      (Forall t : unit. \value(h,t)=\real{v}))]

def endpointCounterexample : Argument Symbol [] := [proof|
  Have \decreasing(\sample);
  Have Forall t : unit. 0 \le \value(\sample,t) \land \value(\sample,t) \le 1;
  Have \int_{0}^{1}{t}{\value(\sample,t)}=\frac{1}{2};
  Have \functional(\sample)=\frac{1}{4};
  Have \different(\value(\sample,\zero),\frac{1}{2}) \land
    \different(\value(\sample,\quarterPoint),1);
  Conclude Exists h : curve. \decreasing(h) \land
    (Forall t : unit. 0 \le \value(h,t) \land \value(h,t) \le 1) \land
    \int_{0}^{1}{t}{\value(h,t)}=\frac{1}{2} \land \functional(h)=\frac{1}{4} \land
    \different(\value(h,\zero),\frac{1}{2}) \land \different(\value(h,\quarterPoint),1)]

theorem endpoint_counterexample_valid : endpointCounterexample.Valid model (fun _ => True) := by
  simp only [endpointCounterexample,Argument.Valid,Expr.eval,Var.get,model,Ty.denote,
    Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact fun _ _ => sample_antitone
  · exact fun _ _ => sample_bounded
  · exact fun _ _ => sample_mean
  · exact fun _ _ => sample_functional
  · exact fun _ _ => sample_values
  · exact fun _ h => ⟨endpointSample,h.1.1.1.1.2,h.1.1.1.2,h.1.1.2,h.1.2,h.2⟩
theorem endpoint_counterexample_verified : endpointCounterexample.goal.eval model () :=
  endpointCounterexample.sound model _ endpoint_counterexample_valid () trivial
def existingCounterexample : Prop := statement_of% pointwise_counterexample
theorem endpoint_counterexample_correspondence : endpointCounterexample.goal.eval model () ↔ existingCounterexample := by
  simp only [endpointCounterexample,Argument.goal,Expr.eval,Var.get,model,Ty.denote,
    Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,existingCounterexample]
  rfl

theorem literal_lemma_refuted : ¬ literalPointwiseLemma.eval model () := by
  simp only [literalPointwiseLemma,Expr.eval,Var.get,model,Ty.denote,Nat.cast_zero,Nat.cast_one]
  intro h
  have hc := h Copula.unitHalf endpointSample ⟨sample_antitone,sample_bounded,
    by simpa [Copula.unitHalf] using sample_mean⟩
  have hf : decreasingFunctional endpointSample =
      (Copula.unitHalf:ℝ)*(1-(Copula.unitHalf:ℝ)) := by
    rw [sample_functional]
    norm_num [Copula.unitHalf]
  rcases hc.mp hf with hi|hi
  · have hx := hi quarter
    have hq : quarter ≠ 0 := by
      intro he
      have := congrArg (fun t : I => (t:ℝ)) he
      norm_num [quarter] at this
    norm_num [endpointSample,hq,quarter,Copula.unitHalf,Set.indicator,Set.mem_Iic] at hx
    exact hq hx
  · have hx := hi 0
    norm_num [endpointSample,Copula.unitHalf] at hx

def vocabulary : Vocabulary Symbol where
  key _ := "copula-definitions"
  typeLatex
    | .base "copula" => "\\mathcal{C}"
    | .base "curve" => "\\mathbb{R}^{[0,1]}"
    | .unit => "[0,1]"
    | .real => "\\mathbb{R}"
    | _ => ""
  noun _ := ""
  application
    | .xi,[C] => "\\xi("++C++")"
    | .rho,[C] => "\\rho("++C++")"
    | .cdf,[C,u,v] => C++"("++u++","++v++")"
    | .partialCDF,[C,u,v] => "\\partialCDF_1 "++C++"("++u++","++v++")"
    | .si,[C] => C++"\\text{ is SI}"
    | .sd,[C] => C++"\\text{ is SD}"
    | .wCopula,[] => "W"
    | .piCopula,[] => "\\Pi"
    | .mCopula,[] => "M"
    | .square,[x] => "\\left("++x++"\\right)^2"
    | .minimum,[x,y] => "\\min\\{"++x++","++y++"\\}"
    | .maximum,[x,y] => "\\max\\{"++x++","++y++"\\}"
    | .value,[h,t] => h++"("++t++")"
    | .decreasing,[h] => h++"\\text{ is decreasing}"
    | .functional,[h] => "F("++h++")"
    | .sample,[] => "h_*"
    | .zero,[] => "0"
    | .quarterPoint,[] => "\\tfrac14"
    | .half,[] => "\\tfrac12"
    | .indicator,[v,t] => "\\mathbf{1}_{\\{"++t++"\\le "++v++"\\}}"
    | .different,[x,y] => x++"\\ne "++y
    | _,_ => "\\mathrm{unsupported}"

def documents : Json := Json.mkObj [
  (toString ``monotone_statement_valid,Json.mkObj [
    ("checked",checked_document% (vocabulary) monotone_statement_valid),
    ("presentation",.str "statement"),
    ("title",.str "Theorem 2: the inequality and all equality cases"),
    ("note",.str "This independently parsed statement reuses the native SI/SD inequality and equality classification. It does not certify the printed maximum-principle proof. SI and SD are interpreted via the displayed concavity and convexity chord conditions."),
    ("correspondence",.str (toString ``monotone_statement_correspondence)),
    ("verified",.str (toString ``monotone_statement_verified)),
    ("definitionBridge",.str (toString ``si_definition)),
    ("definition",.str ("C\\text{ is SI}\\quad\\Longleftrightarrow\\quad"++siDefinition.latex vocabulary ["C"]++
      ".\\quad C\\text{ is SD}\\quad\\Longleftrightarrow\\quad"++sdDefinition.latex vocabulary ["C"]))
  ]),
  (toString ``endpoint_counterexample_valid,Json.mkObj [
    ("checked",checked_document% (vocabulary) endpoint_counterexample_valid),
    ("title",.str "Why the equality alternatives in Lemma 8 must hold almost everywhere"),
    ("note",.str "Take h_*(0)=1 and h_*(t)=1/2 for t>0. The change at a single endpoint preserves the mean and F=1/4. At t=0 the function differs from the constant 1/2; at t=1/4 it differs from the indicator of [0,1/2]. This refutes the literal pointwise equality classification. The native lemma verifies the corrected almost-everywhere classification."),
    ("correspondence",.str (toString ``endpoint_counterexample_correspondence)),
    ("verified",.str (toString ``endpoint_counterexample_verified)),
    ("definitionBridge",.str (toString ``functional_definition)),
    ("definition",.str ("F(h):="++functionalDefinition.latex vocabulary ["h"]++
      ".\\quad h_*(t):=\\begin{cases}1&t=0\\\\\\tfrac12&t>0\\end{cases}"))
  ])
]

#assert_lean_mirror_axioms xi_definition
#assert_lean_mirror_axioms rho_definition
#assert_lean_mirror_axioms si_definition
#assert_lean_mirror_axioms sd_definition
#assert_lean_mirror_axioms benchmark_definitions
#assert_lean_mirror_axioms monotone_statement_valid
#assert_lean_mirror_axioms monotone_statement_correspondence
#assert_lean_mirror_axioms endpoint_counterexample_valid
#assert_lean_mirror_axioms endpoint_counterexample_correspondence
#assert_lean_mirror_axioms literal_lemma_refuted
end Papers.AnsariRockel2026XiRho.ArticleDefinitions
