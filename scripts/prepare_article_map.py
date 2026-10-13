"""One-time authoring helper for the source-preserving Blest article map.

The resulting JSON is reviewed data. The exporter independently recompiles all
the cited evidence; this authoring helper never sets a verified status.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
NS = 'Papers.Rockel2026ExactBlest.'
bindings = []

def declarations(names):
    return [n if n.startswith(('Papers.', 'ProbabilityTheory.')) else NS+n for n in names.split()]

def bind(label, names, title=None):
    bindings.append({'label':label, 'declarations':declarations(names),
                     **({'title':title} if title else {})})

bind('thm:rho-nu','rho_nu_region rho_upper_exists_unique rho_lower_exists_unique rho_lower_eq_survival_upper')
bind('thm:eta-nu','eta_nu_region eta_upper_exists_unique eta_lower_exists_unique eta_lower_eq_transpose_upper')
bind('lem:coupling','ArticleOriginalProof.coupling_nu_moment ArticleOriginalProof.coupling_rho_moment ArticleOriginalProof.coupling_transpose_moment ArticleOriginalProof.coupling_eta_moment eta_mix ProbabilityTheory.Copula.spearmanRho_mix Papers.Rockel2026XiBlest.blest_mix')
bind('lem:symmetries','nu_survival eta_survival nu_reflect_first ProbabilityTheory.Copula.spearmanRho_survivalCopula ProbabilityTheory.Copula.spearmanRho_reflect_second Papers.Rockel2026XiBlest.blest_reflect_second')
bind('lem:rearrangement','rearrangement')
bind('lem:rho-nu-values','paperD_values paperD_strictMono paperD_parameter_range paperD_parameter_exists_unique paperD_on_boundary')
bind('cor:nu-rho','ArticleProof.corollary_valid ArticleProof.full_correspondence ArticleProof.corollary_verified')
bind('lem:eta-nu-values','eta_paperA nu_paperA eta_paperB nu_paperB paperA_gap paperB_gap eta_paperA_strictMono paperEtaB_strictMonoOn paperEtaB_endpoints')
bind('lem:dual-certificate','dual_certificate dual_certificate_graph dual_certificate_reverse_graph')
bind('prop:dual-A','paper_dualA paper_contactA')
bind('prop:dual-B','paper_dualB paper_contactB')
bind('cor:asymmetry','nu_eta_bound nu_transpose_bound paper_asymmetry_eq_iff paper_transposition_eq_iff paperA_threeQuarter_values')
bind('cor:nu-transpose','nu_transpose_region_gap nu_transpose_region nu_transpose_max_exists_unique nu_transpose_min_exists_unique paper_nu_transpose_max_A paper_nu_transpose_max_B paper_nu_transpose_extremizer_cases nu_transpose_extremizer_neg_one')
bind('rem:randomization','paperA_not_extremal paperB_conditional_formula familyB_not_first_graph reflection_byproduct rho_eta_bound paper_rho_eta_extremizers')

for label,names in {
    'eq:nu-def':'ArticleBridge.nu_definition_eq nu_normalization',
    'eq:rho-def':'ArticleBridge.rho_definition_eq',
    'eq:eta-def':'ArticleOriginalProof.eta_cdf_integral eta_transpose nu_transpose',
    'eq:Phi-def':'ArticleProof.phi_definition rhoBoundary_reflect',
    'eq:Upsilon-def':'etaGap_of_ge etaGap_mem etaGap_bottom etaGap_continuousAt_join',
    'eq:Upsilon-param':'etaGap_paperEtaB paperEtaB_strictMonoOn paperEtaB_endpoints',
    'eq:coupling-moments':'ArticleOriginalProof.coupling_nu_moment ArticleOriginalProof.coupling_rho_moment ArticleOriginalProof.coupling_transpose_moment ArticleOriginalProof.coupling_eta_moment',
    'eq:survival-transform':'nu_survival eta_survival ProbabilityTheory.Copula.spearmanRho_survivalCopula',
    'eq:reflection-transform':'ProbabilityTheory.Copula.spearmanRho_reflect_second Papers.Rockel2026XiBlest.blest_reflect_second',
    'eq:eta-reflection':'eta_reflect_second',
    'eq:rho-nu-support':'ArticleOriginalProof.rho_support_moment',
    'eq:Zc-def':'paperZeta_formula quadratic_cdf_at_score quadraticRank_uniform paperD_graph_law',
    'eq:rho-nu-values':'paperD_values',
    'eq:eta-nu-support':'support_identity support_moment_survival',
    'eq:Tw-def':'paperT_formula paperA_graph_law paperA_zero paperA_one',
    'eq:Ba-branches':'paperB_conditional_formula paperB_half',
    'eq:Aw-values':'eta_paperA nu_paperA',
    'eq:Ba-values':'eta_paperB nu_paperB',
    'eq:potential-A':'hasDerivAt_paperPhiA hasDerivAt_paperPsiA paperPotentialsA_normalized',
    'eq:dual-A-inequality':'paper_dualA',
    'eq:potential-B':'hasDerivAt_paperPhiB hasDerivAt_paperPsiB paperPotentialsB_normalized',
    'eq:branch-sum':'ArticleOriginalProof.branch_sum ArticleOriginalProof.branch_derivatives',
    'eq:eta-nu-support-line':'ArticleOriginalProof.paper_graph_support',
    'eq:Lambda-def':'Lambda_closed_branch Lambda_bijOn',
    'eq:Lambda-param':'Lambda_paperNB paperNB_bijOn paper_Lambda_junction',
    'fig:regions':'nu_rho_bound nu_eta_bound',
    'fig:rho-extremizers':'rho_figure_values paperD_graph_law',
    'fig:eta-extremizers':'paper_figure_panel_values paperB_conditional_formula',
    'fig:nu-transpose':'eta_nu_region_linear_image upper_boundary_curve lower_boundary_curve',
}.items(): bind(label,names)

def passage(quote,names,kind='paragraph'):
    bindings.append({'quote':quote,'kind':kind,'declarations':declarations(names)})

passage('The starting point is the identity','nu_moment')
passage('The third identity follows','ArticleOriginalProof.coupling_transpose_moment')
passage('Averaging the two formulas','ArticleOriginalProof.coupling_eta_moment')
passage('For the measure of concordance','nu_reflect_first nu_survival eta_survival')
passage('Fix $t\\in(0,1)$ and set','cdfRank_threshold')
passage('Now choose $H=','weighted_tail_layercake threshold_rearrangement')
passage('Equality holds precisely when','rearrangement')
passage('Formula \\eqref{eq:rho-nu-values} follows','paperD_values paperD_on_boundary')
passage('Fix $C\\in\\CC$ with $\\rho(C)=','paperD_parameter_exists_unique continuous_quadratic_cdf quadraticRank_uniform')
passage('and equality holds if and only if $Z=','rearrangement paper_rho_upper_unique')
passage('The survival copula $\\widehat C$ satisfies','nu_survival rho_lower_eq_survival_upper rho_fibre_complete')
passage('On $[-1,0]$, \\eqref{eq:Phi-def} gives','ArticleProof.gap_maximum')
passage('Direct integration over the linear pieces','eta_paperA nu_paperA eta_paperB nu_paperB')
passage('That $\\eta(A_w)$ increases','eta_paperA_strictMono hasDerivAt_paperEtaB deriv_paperEtaB_pos')
passage('In addition, $\\eta(B_{1/2})','paperEtaB_endpoints')
passage('Part~(a) is the elementary direction','dual_certificate')
passage('For~(b), the sets','dual_certificate_graph dual_certificate_reverse_graph')
passage('\\Delta(x,z)&=\\frac{(x+w-1-z)^2','ArticleOriginalProof.graph_rectangle_10 ArticleOriginalProof.graph_first_factor ArticleCalculations.first_rectangle_valid ArticleCalculations.first_rectangle_correspondence ArticleCalculations.first_rectangle_verified ArticleCalculations.delta_definition',kind='math')
passage('F(x,z)&\\coloneqq(6-2w)','ArticleOriginalProof.graph_rectangle_01 ArticleOriginalProof.graph_second_factor ArticleCalculations.second_rectangle_valid ArticleCalculations.second_rectangle_correspondence ArticleCalculations.second_rectangle_verified ArticleCalculations.factor_definition',kind='math')
passage('\\partial_x\\Delta(x,z)=\\frac{(x+z-1)','ArticleOriginalProof.graph_derivative_00 ArticleOriginalProof.graph_derivative_00_nonpos',kind='math')
passage('\\partial_z\\Delta(1-w,z)=-','ArticleOriginalProof.graph_edge_derivative_z',kind='math')
passage('\\partial_z\\Delta(x,z)=\\frac{(x+z-1)','ArticleOriginalProof.graph_derivative_11 ArticleOriginalProof.graph_derivative_11_nonneg ArticleOriginalProof.graph_edge_derivative_x',kind='math')
passage('\\ell_+^2\\,F_+','ArticleOriginalProof.random_rectangle_10 ArticleOriginalProof.random_rectangle_11',kind='math')
passage('\\Delta(x,z)=\\frac{(x+z-1)^2\\,\\bigl\\{(4-3b)','ArticleOriginalProof.random_rectangle_02',kind='math')
passage('\\partial_x\\Delta(x,z)=-\\frac{2(1-x-z)','ArticleOriginalProof.random_derivative_low_x ArticleOriginalProof.random_derivative_low_x_nonpos',kind='math')
passage('\\partial_z\\Delta(1-b,z)=-\\frac{4(1-b)^2z','ArticleOriginalProof.random_edge_derivative_0 ArticleOriginalProof.random_edge_derivative_1 ArticleOriginalProof.random_edge_derivative_1_nonpos',kind='math')
passage('The first of these expressions changes sign','ArticleOriginalProof.random_middle_factor_pos ArticleOriginalProof.random_middle_anchor')
passage('\\partial_x\\Delta(x,z)=-\\frac{\\ell_-','ArticleOriginalProof.random_derivative_high_x ArticleOriginalProof.random_edge_derivative_2 ArticleOriginalProof.random_derivative_high_x_nonneg ArticleOriginalProof.random_edge_derivative_2_nonneg',kind='math')
passage('For the first derivative, note that','ArticleOriginalProof.random_last_linear_factors ArticleOriginalProof.random_last_edge_factor')
passage('Differentiating \\eqref{eq:Upsilon-def} on','hasDerivAt_graphGap graphGap_deriv_bounds')
passage('\\partial_b\\Upsilon(e_b)','hasDerivAt_paperUps paperUps_deriv_pos',kind='math')
passage('Consider the linear bijection $L','eta_nu_region_linear_image nu_transpose_region_gap')
passage('Both coordinates of these curves increase','lowerCurve_strictMonoOn upperCurve_strictMonoOn param_slope_bounds')
passage('The quantity $n_b=e_b-','paperNB_bijOn Lambda_bijOn')

data={'schemaVersion':1,'paperId':'Rockel2026ExactBlest','source':'source/article.tex',
      'bibliography':'source/exact-blest-regions.bbl','bindings':bindings,
      'definitions':{
          '\\nu':{'label':'eq:nu-def'},'\\rho':{'label':'eq:rho-def'},
          '\\eta':{'label':'eq:eta-def'},'\\Phi':{'label':'eq:Phi-def'},
          '\\Upsilon':{'label':'eq:Upsilon-def'},'\\Lambda':{'label':'eq:Lambda-def'},
          '\\zeta':{'label':'eq:Zc-def'},'T_w':{'label':'eq:Tw-def'},
      },
      'verificationScope':'All original article content is reproduced. Compiled counterparts are attached to every labeled result; verification of every literal proof step is in progress.'}
(ROOT/'examples/paper-bridge/article-map.json').write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
print('Authored',len(bindings),'source bindings.')
