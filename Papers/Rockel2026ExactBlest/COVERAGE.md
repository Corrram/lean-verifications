# Mathematical audit and formal coverage

Source: [arXiv:2609.27634v1](https://arxiv.org/abs/2609.27634v1), 23 September 2026.

**Status: complete for stated scope.** The labeled mathematical results and quantitative claims mapped below are the declared scope.
This revision determines two exact regions, `(rho,nu)` and `(eta,nu)`, and
derives the exact region of `(nu(C), nu(C^T))` as a corollary. The
`(beta,nu)`-region of the previous version is no longer part of the
manuscript. No results from other manuscripts are in scope.

## Notation: the manuscript's parametrization

The manuscript parametrizes its three extremal families so that every
parameter increases with dependence. `D_c` runs from `D_0 = W` to `D_1 = M`,
and its support has its kink at `u = c`. `A_w` pairs the leading fraction `w`
of the first variable comonotonically and runs from `A_0 = W` to `A_1 = M`.
`B_b`, for `b` in `(0,1/2]`, splits the leading fraction `b` between two
branches, with `B_(1/2) = A_(1/2)`.

`ExactBlestPaperParams.lean` defines these families exactly as printed
(`paperD`, `paperA`, `paperB`, with `paperEtaB = e_b`, `paperNuB = nu(B_b)`,
`paperNB = n_b`, `paperUpsB = Upsilon(e_b)`, and `paperR = R_b`) and restates
every family-dependent claim in this notation. The table below cites these
restatements first, so the manuscript and the Lean statements can be read side
by side without translation.

The underlying constructions in the other modules predate the current
parametrization and use the reflected parameters: `familyA w` is `A_(1-w)`,
`familyB a` is `B_(1-a)`, and `rhoFullFamily c` is `D_(1-c)`. The bridging
theorems `Papers.Rockel2026ExactBlest.paperA_symm`, `Papers.Rockel2026ExactBlest.paperB_symm`, and the definition of `paperD` make this
explicit, and the paper-form theorems are derived from the internal ones.

## Overall finding

No discrepancy was found in the formulas, constants, parameter ranges, or
proof arguments of the revised manuscript. No mathematical correction was
needed. Every labeled result has a formally checked counterpart, and so do
the quantitative claims added in the revision:

- both set equalities of `cor:nu-transpose`, the boundary function `Lambda`
  with its two displayed branches, and unique attainment of the largest and
  smallest `nu(C^T)` at every value of `nu(C)`, with the extremizers
  identified as `A_w^T`, `B_b^T`, `W`, and the upper extremizers themselves;
- the closed-form bound for `nu(C) >= -7/8` stated in the introduction;
- the derivative facts used in the proof of the corollary,
  `Upsilon'(e) in [-1/3,1/3]` on `[-3/4,1)` and `Upsilon'(e_b) = (2-3b)/(2-b)`;
- continuity of `Upsilon`, in particular at the regime change `-3/4`;
- the bound `1/2` obtained from Theorem 1.1 alone, and the statement that
  `nu(C)-rho(C)` and `nu(C^T)-rho(C)` cannot be extreme in opposite directions;
- central symmetry of the `(rho,nu)`-region and its failure for `(eta,nu)`;
- the non-extremality of `A_w` for `w < 1/2` and the shuffle description of the
  `rho-eta` extremizers in the final remark;
- the values quoted in the figure captions and printed above the figure panels;
- the dual-certificate lemma `lem:dual-certificate` for a general continuous cost.

This does not mean that every intermediate step in the printed proofs was
translated literally. The formalization sometimes uses a different proof of
the same statement, as recorded below.

The strict Lean check compiles all 592 local theorems and their transitive
axiom audits. The separate SymPy script passes all 82 exact identity checks,
stated in the manuscript's parametrization. Neither count should be read
as a count of fully formalized paper results.

## Claim-by-claim coverage

| Source result | Lean declaration and evidence | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Abstract and introduction: normalization and the two sharp constants | `Papers.Rockel2026ExactBlest.nu_normalization` gives `nu(M)=1`, `nu(W)=-1`, `nu(Pi)=0`. `Papers.Rockel2026ExactBlest.nu_rho_bound` and `Papers.Rockel2026ExactBlest.nu_transpose_bound` give `1/4` and `27/64`. `Papers.Rockel2026ExactBlest.nu_transpose_half_bound` proves the weaker bound `1/2` from Theorem 1.1 applied to `C` and `C^T`; `Papers.Rockel2026ExactBlest.no_opposite_extremes` proves that the two deviations from `rho` cannot be extreme in opposite directions. `Papers.Rockel2026ExactBlest.eta_nu_region_linear_image` proves that the `(eta,nu)`-region is the linear image of the `(nu,nu^T)`-region, and `Papers.Rockel2026ExactBlest.eta_fibre_max_asymmetry` that the fibre above `eta=e` has length `2*Upsilon(e)`, the largest asymmetry at that `eta`. | verified | None. |
| Abstract: extremal copulas and their supports | Every extremizer is identified with an explicit graph law: `Papers.Rockel2026ExactBlest.paperD_graph_law` with `Papers.Rockel2026ExactBlest.paperZeta_formula`, `Papers.Rockel2026ExactBlest.paperA_graph_law` with `Papers.Rockel2026ExactBlest.paperT_formula`, `Papers.Rockel2026ExactBlest.paperB_graph_law` with `Papers.Rockel2026ExactBlest.paperR_formula`, and transposes or survival copulas of these. The maps are piecewise linear with explicitly displayed pieces. `Papers.Rockel2026ExactBlest.paperB_conditional_formula` and `Papers.Rockel2026ExactBlest.familyB_not_first_graph` give the two-atom conditional law and exclude a first-coordinate graph. | verified | "Finitely many line segments" is read off the explicit piecewise-linear maps; it is not a separate Lean statement about supports. |
| `thm:rho-nu` (Theorem 1.1) and the identity `2r-Phi(r)=-Phi(-r)` | `Papers.Rockel2026ExactBlest.rho_nu_region` is the full set equality with the displayed Phi formula. `Papers.Rockel2026ExactBlest.rho_upper_exists_unique` and `Papers.Rockel2026ExactBlest.rho_lower_exists_unique` prove unique attainment at every rho, including endpoints; `Papers.Rockel2026ExactBlest.paper_rho_upper_unique` and `Papers.Rockel2026ExactBlest.paper_rho_lower_unique` identify the extremizers as `D_c` and its survival copula. `Papers.Rockel2026ExactBlest.rho_lower_eq_survival_upper` shows that the lower extremizer is the survival copula of the upper one. `Papers.Rockel2026ExactBlest.rhoBoundary_reflect` proves the identity. | verified | None. The set equality uses a transport certificate; the rearrangement lemma is also proved independently. |
| `thm:eta-nu` (Theorem 1.2) and the definition of Upsilon | `Papers.Rockel2026ExactBlest.eta_nu_region` and `Papers.Rockel2026ExactBlest.eta_fibre_displayed` prove the set equality with the displayed Upsilon formulas; `Papers.Rockel2026ExactBlest.etaGap_paperEtaB` checks the parametric formula (6) for `Upsilon(e_b)`. `Papers.Rockel2026ExactBlest.eta_upper_exists_unique`, `Papers.Rockel2026ExactBlest.eta_lower_exists_unique`, and `Papers.Rockel2026ExactBlest.eta_lower_eq_transpose_upper` give unique attainment and the transposition relation. `Papers.Rockel2026ExactBlest.paper_eta_graph_extremizers` identifies the unique extremizers for `eta` in `[-3/4,1]` as `A_w` and `A_w^T` with `w = ((1+eta)/2)^(1/3)`, and `Papers.Rockel2026ExactBlest.paper_eta_random_extremizers` those for `eta` in `(-1,-3/4)` as `B_b` and `B_b^T` with `e_b = eta`. `Papers.Rockel2026ExactBlest.etaGap_mem` proves that Upsilon maps `[-1,1]` into `[0,27/128]`. `Papers.Rockel2026ExactBlest.etaGap_join` and `Papers.Rockel2026ExactBlest.randomGap_endpoints` check the value `1/8` of both formulas at `-3/4`; `Papers.Rockel2026ExactBlest.etaGap_continuousOn` and `Papers.Rockel2026ExactBlest.etaGap_continuousAt_join` prove continuity on `[-1,1]` and at `-3/4`. | verified | None. |
| `lem:coupling` (Lemma 2.1) | `Papers.Rockel2026ExactBlest.nu_moment`, `Papers.Rockel2026ExactBlest.nu_transpose_moment`, `Papers.Rockel2026ExactBlest.eta_moment`, `Papers.Rockel2026ExactBlest.nu_rho_moment`, `Papers.Rockel2026ExactBlest.support_moment_survival`; the CDF integral is related to the actual copula measure by Fubini. `Papers.Rockel2026ExactBlest.eta_mix` gives affinity. | verified | None. |
| `lem:symmetries` (Lemma 2.2) and the remarks after it | `Papers.Rockel2026ExactBlest.nu_survival`, `Papers.Rockel2026ExactBlest.eta_survival`, `Papers.Rockel2026ExactBlest.nu_reflect_first`, `blest_reflect_second`, `Copula.spearmanRho_reflect_second`, and `Papers.Rockel2026ExactBlest.eta_reflect_second`. `Papers.Rockel2026ExactBlest.rho_nu_region_neg` proves the central symmetry of the `(rho,nu)`-region and `Papers.Rockel2026ExactBlest.rho_nu_fibre_reflect` the diagonal symmetry of its fibres. `Papers.Rockel2026ExactBlest.eta_nu_region_not_symmetric` shows that `(-5/32, 7/128)` lies in the `(eta,nu)`-region while `(5/32, -7/128)` does not. `Papers.Rockel2026ExactBlest.eta_nu_fibre_reflect` checks the diagonal symmetry of the `(eta,nu)`-fibres. | verified | None. |
| `lem:rearrangement` (Lemma 2.3) | `Papers.Rockel2026ExactBlest.rearrangement`, `Papers.Rockel2026ExactBlest.threshold_rearrangement`, and `Papers.Rockel2026ExactBlest.weighted_tail_layercake` prove the inequality and the almost-sure equality case for an integrable variable with continuous CDF. The pinned copula library supplies the probability integral transform. | verified | None. |
| The maps `zeta_c`, `lem:rho-nu-values` (Lemma 3.1), and Figure 2 | `Papers.Rockel2026ExactBlest.paperZeta_formula` gives the rank map (11) centred at `1-c`, and `Papers.Rockel2026ExactBlest.quadraticRank_uniform` its measure preservation. `Papers.Rockel2026ExactBlest.paperD_graph_law` and `Papers.Rockel2026ExactBlest.paperD_values` give the graph law and both displayed coefficient formulas (12) for all `c` in `[0,1]`. `Papers.Rockel2026ExactBlest.paperD_strictMono`, `Papers.Rockel2026ExactBlest.paperD_parameter_exists_unique`, and `Papers.Rockel2026ExactBlest.paperD_parameter_range` prove the increasing bijection onto `[-1,1]`; `Papers.Rockel2026ExactBlest.paperD_on_boundary` gives `nu = Phi(rho)`. `Papers.Rockel2026ExactBlest.paperD_zero` and `Papers.Rockel2026ExactBlest.paperD_one` identify `D_0 = W` and `D_1 = M`. `Papers.Rockel2026ExactBlest.paper_figure_panel_values` checks the values of `rho` and `nu` printed above all six panels of Figure 2. | verified | None. |
| `cor:nu-rho` (Corollary 3.2) | The bound, attainment, and uniqueness theorems identify both extremizers; `Papers.Rockel2026ExactBlest.paper_nu_rho_max_unique` and `Papers.Rockel2026ExactBlest.paper_nu_rho_min_unique` state them as `D_(1/2)` and its survival copula. `Papers.Rockel2026ExactBlest.paperD_half`, `Papers.Rockel2026ExactBlest.quadraticRank_half`, `Papers.Rockel2026ExactBlest.rho_midpoint_reflected_graph`, and `Papers.Rockel2026ExactBlest.rho_midpoint_original_graph` give the absolute-value and tent maps; survival exchanges them. | verified | None. |
| `A_w`, `B_b`, `lem:eta-nu-values` (Lemma 4.1), and Figure 3 | `paperA` and `paperB` with `Papers.Rockel2026ExactBlest.eta_paperA`, `Papers.Rockel2026ExactBlest.nu_paperA`, `Papers.Rockel2026ExactBlest.nu_transpose_paperA`, `Papers.Rockel2026ExactBlest.eta_paperB`, `Papers.Rockel2026ExactBlest.nu_paperB`, and `Papers.Rockel2026ExactBlest.nu_transpose_paperB` give the displayed formulas (16) and (17). `Papers.Rockel2026ExactBlest.paperA_gap` gives `nu(A_w)-eta(A_w)=2(1-w)w^3` and `Papers.Rockel2026ExactBlest.paperB_gap` gives `nu(B_b)-eta(B_b)=Upsilon(e_b)`. `Papers.Rockel2026ExactBlest.eta_paperA_strictMono`, `Papers.Rockel2026ExactBlest.paperEtaB_strictMonoOn`, `Papers.Rockel2026ExactBlest.hasDerivAt_paperEtaB`, and `Papers.Rockel2026ExactBlest.deriv_paperEtaB_pos` give the increasing parameter maps and the displayed derivative; `Papers.Rockel2026ExactBlest.paperA_eta_range` and `Papers.Rockel2026ExactBlest.paperEtaB_range` the ranges; `Papers.Rockel2026ExactBlest.paperEtaB_endpoints` the values `-3/4` and `-1` and the limit as `b -> 0`. `Papers.Rockel2026ExactBlest.paperA_zero`, `Papers.Rockel2026ExactBlest.paperA_one`, `Papers.Rockel2026ExactBlest.paperB_half`, and `Papers.Rockel2026ExactBlest.paperB_zero` identify `A_0 = W`, `A_1 = M`, `B_(1/2)=A_(1/2)`, and the endpoint `W`. `Papers.Rockel2026ExactBlest.paperB_conditional_formula` gives the two atoms (15) and their probabilities `1/(2(1-b))` and `(1-2b)/(2(1-b))`. `Papers.Rockel2026ExactBlest.paper_figure_panel_values` checks the values of `eta` and `nu` printed above all six panels of Figure 3 and the probabilities `2/3` and `1/3` for `B_(1/4)` (exact fractions, of which the printed decimals for `B_(1/4)` and `A_(7/8)` are roundings). | verified | None. |
| `lem:dual-certificate` (Lemma 4.2) | `Papers.Rockel2026ExactBlest.dual_certificate` proves part (a) for the law of an arbitrary copula, an arbitrary continuous cost, and continuous potentials: the bound by `∫φ+∫ψ` and equality exactly when the coupling is concentrated on the contact set. `Papers.Rockel2026ExactBlest.dual_certificate_graph` and `Papers.Rockel2026ExactBlest.dual_certificate_reverse_graph` prove part (b) with finitely many exceptional vertical and horizontal lines, using `Papers.Rockel2026ExactBlest.ae_coord_ne` for the null lines. The applications in the proof of Theorem 1.2 are also checked directly by `Papers.Rockel2026ExactBlest.graph_support_graph` and `Papers.Rockel2026ExactBlest.randomized_support_graph` with `Papers.Rockel2026ExactBlest.copula_eq_of_graph` and `Papers.Rockel2026ExactBlest.copula_eq_of_reverse_graph`. | verified | None. |
| `prop:dual-A` (Proposition 4.3) | `Papers.Rockel2026ExactBlest.paper_dualA` proves the inequality for `w` in `[1/2,1]` with `kappa_w = (3-2w)/(2w)` (`Papers.Rockel2026ExactBlest.kA_paper`), and `Papers.Rockel2026ExactBlest.paper_contactA` the full equality set `S_w`, including the segment `[1/2,1] x {1/2}` at `w = 1/2`. `Papers.Rockel2026ExactBlest.paperPotentialsA_normalized`, `Papers.Rockel2026ExactBlest.hasDerivAt_paperPhiA`, and `Papers.Rockel2026ExactBlest.hasDerivAt_paperPsiA` identify the potentials by the normalization and derivatives (18). The underlying slack factorizations are in `ExactBlest.lean`. | verified | None. |
| `prop:dual-B` (Proposition 4.4) | `Papers.Rockel2026ExactBlest.paper_dualB` proves the inequality for `b` in `(0,1/2)` with `kappa_b = 2(1-b)/b` (`Papers.Rockel2026ExactBlest.kB_paper`), and `Papers.Rockel2026ExactBlest.paper_contactB` the exact contact set `x = R_b(z)`. `Papers.Rockel2026ExactBlest.paperPotentialsB_normalized`, `Papers.Rockel2026ExactBlest.hasDerivAt_paperPhiB`, and `Papers.Rockel2026ExactBlest.hasDerivAt_paperPsiB` identify the potentials by (20); `Papers.Rockel2026ExactBlest.cutB_paper` gives `z_b = b/(2(1-b))`, and `Papers.Rockel2026ExactBlest.random_branches_same_derivative` verifies branch consistency. | verified | None. |
| Proof of Theorem 1.2 | Lemma 4.2 is applied through its checked instances. `Papers.Rockel2026ExactBlest.graph_support`, `Papers.Rockel2026ExactBlest.randomized_support`, `Papers.Rockel2026ExactBlest.graph_fibre`, `Papers.Rockel2026ExactBlest.randomized_fibre`, and `Papers.Rockel2026ExactBlest.eta_bottom_fibre` cover all eta values; `Papers.Rockel2026ExactBlest.graph_upper_unique`, `Papers.Rockel2026ExactBlest.randomized_upper_unique`, and `Papers.Rockel2026ExactBlest.eta_bottom_unique` give the uniqueness steps, restated for `A_w` and `B_b` in `Papers.Rockel2026ExactBlest.paper_eta_graph_extremizers` and `Papers.Rockel2026ExactBlest.paper_eta_random_extremizers`. | verified | None. |
| `cor:asymmetry` (Corollary 4.5) | `Papers.Rockel2026ExactBlest.nu_eta_bound`, `Papers.Rockel2026ExactBlest.nu_transpose_bound`, the attainment theorems, `Papers.Rockel2026ExactBlest.paper_asymmetry_eq_iff`, and `Papers.Rockel2026ExactBlest.paper_transposition_eq_iff` identify all equality cases with `A_(3/4)` and its transpose; `Papers.Rockel2026ExactBlest.paperA_threeQuarter_values` checks `(eta,nu) = (-5/32, 7/128)`. `Papers.Rockel2026ExactBlest.hasDerivAt_paperUps` and `Papers.Rockel2026ExactBlest.paperUps_deriv_pos` check the displayed derivative of `Upsilon(e_b)` and its sign; `Papers.Rockel2026ExactBlest.randomGap_strictAnti`, `Papers.Rockel2026ExactBlest.etaGap_randomized_bounds`, and `Papers.Rockel2026ExactBlest.etaGap_join` check the parametric part. | verified | None. The graph-branch maximum is proved by the supporting certificate rather than by strict concavity. |
| `Lambda`: `eq:Lambda-def` and `eq:Lambda-param` | `Lambda` is defined by the two displayed branches. `Papers.Rockel2026ExactBlest.Lambda_paperNB` checks `Lambda(n_b) = nu(B_b)` with the displayed formulas (22), and `Papers.Rockel2026ExactBlest.nu_transpose_paperB` identifies `n_b = nu(B_b^T)`. `Papers.Rockel2026ExactBlest.paperNB_bijOn` proves that `b -> n_b` increases bijectively from `(0,1/2)` onto `(-1,-7/8)`. `Papers.Rockel2026ExactBlest.paper_Lambda_junction` and `Papers.Rockel2026ExactBlest.Lambda_junction` check `Lambda(-7/8) = -5/8` for both formulas. `Papers.Rockel2026ExactBlest.Lambda_strictMonoOn` and `Papers.Rockel2026ExactBlest.Lambda_bijOn` prove that `Lambda` is a strictly increasing bijection of `[-1,1]`; `Papers.Rockel2026ExactBlest.LambdaInv_bijOn` and `Papers.Rockel2026ExactBlest.LambdaInv_strictMonoOn` do the same for its inverse. | verified | None. |
| `cor:nu-transpose` (Corollary 4.6) | `Papers.Rockel2026ExactBlest.nu_transpose_region_gap` and `Papers.Rockel2026ExactBlest.nu_transpose_region` prove both set equalities; `Papers.Rockel2026ExactBlest.nu_transpose_fibre_eq` gives each fibre as `[Lambda^{-1}(n), Lambda(n)]`. `Papers.Rockel2026ExactBlest.nu_transpose_isGreatest`, `Papers.Rockel2026ExactBlest.nu_transpose_isLeast`, `Papers.Rockel2026ExactBlest.nu_transpose_max_exists_unique`, and `Papers.Rockel2026ExactBlest.nu_transpose_min_exists_unique` give the extreme values and their unique attainment. `Papers.Rockel2026ExactBlest.nu_transpose_extremizer_neg_one` and `Papers.Rockel2026ExactBlest.nu_transpose_neg_one_values` treat `n=-1`. `Papers.Rockel2026ExactBlest.paper_nu_transpose_max_A` identifies the maximizer `A_w^T` with `w = ((1+n)/2)^(1/4)` for `n >= -7/8`, and `Papers.Rockel2026ExactBlest.paper_nu_transpose_max_B` the maximizer `B_b^T` with `n_b = n` for `n < -7/8`. `Papers.Rockel2026ExactBlest.paper_nu_transpose_extremizer_cases` shows that the minimizer is an upper extremizer `A_w` or `B_b` and the maximizer its transpose. `Papers.Rockel2026ExactBlest.nu_transpose_closed_bound` and `Papers.Rockel2026ExactBlest.nu_transpose_closed_bound_unique` prove the closed-form statement of the introduction. Proof steps: `Papers.Rockel2026ExactBlest.Lambda_curve` and `Papers.Rockel2026ExactBlest.upper_boundary_curve` identify `K_+` with the graph of `Lambda`, `Papers.Rockel2026ExactBlest.lower_boundary_curve` identifies `K_-` with the graph of the inverse, and `Papers.Rockel2026ExactBlest.lowerCurve_strictMonoOn` and `Papers.Rockel2026ExactBlest.upperCurve_strictMonoOn` prove that both coordinates of the curves increase. `Papers.Rockel2026ExactBlest.hasDerivAt_graphGap`, `Papers.Rockel2026ExactBlest.hasDerivAt_etaGap_graph`, `Papers.Rockel2026ExactBlest.hasDerivWithinAt_etaGap_graph`, and `Papers.Rockel2026ExactBlest.graphGap_deriv_bounds` check `Upsilon'(e) = 1-(4/3)2^(-1/3)(1+e)^(1/3)` in `[-1/3,1/3]`. `Papers.Rockel2026ExactBlest.hasDerivAt_etaGap_paper` checks `Upsilon'(e_b) = (2-3b)/(2-b)` in `(1/3,1)`, and `Papers.Rockel2026ExactBlest.hasDerivAt_etaGap_param` with `Papers.Rockel2026ExactBlest.param_slope_bounds` includes differentiability of the inverse parameter. | verified | None. The Lean proof reaches the fibre description through `Papers.Rockel2026ExactBlest.gap_band_iff` and the monotonicity of `Lambda` instead of the printed convexity-and-boundary argument; the derivative claims are checked separately. |
| `rem:randomization` (Remark 4.7) | (a) `Papers.Rockel2026ExactBlest.paperA_gap` and `Papers.Rockel2026ExactBlest.paperA_not_extremal`: for `w` in `(0,1/2)`, `eta(A_w)` lies in `(-1,-3/4)` and `A_w` lies strictly below the upper boundary, because `A_w` is a first-coordinate graph law and `B_b` is not. `Papers.Rockel2026ExactBlest.familyB_joint_law`, `Papers.Rockel2026ExactBlest.familyB_disintegration`, `Papers.Rockel2026ExactBlest.paperB_conditional_formula`, `Papers.Rockel2026ExactBlest.familyB_not_first_graph`, and `Papers.Rockel2026ExactBlest.randomized_optimizer_not_first_graph` cover the two atoms and the non-graph optimizer; the root-sum and first-order identities are also checked. (b) `Papers.Rockel2026ExactBlest.reflection_byproduct`, `Papers.Rockel2026ExactBlest.rho_eta_bound`, and `Papers.Rockel2026ExactBlest.paper_rho_eta_extremizers`, which identifies the unique maximizer `A_(3/4)^perp` with the ordinal sum of `W` on `[0,3/4]` and `M` on `[3/4,1]` and the unique minimizer `(A_(3/4)^T)^perp` with its survival copula. | verified | None. The historical remark about Genest and Plante's example is not a Lean statement. |

## Retained checks for the removed discussion section

The previous version ended with a discussion section, which the manuscript no
longer contains. Its numerical claims remain checked: `Papers.Rockel2026ExactBlest.rho_zero_fibre` proves
that `rho(C)=0` confines `nu(C)` exactly to `[-1/4,1/4]`, `Papers.Rockel2026ExactBlest.nu_zero_fibre`
identifies the `nu^T`-fibre at `nu=0` as `[Lambda^{-1}(0), Lambda(0)]`,
`Papers.Rockel2026ExactBlest.Lambda_zero_bounds` and `Papers.Rockel2026ExactBlest.LambdaInv_zero_bounds` give
`0.375 < Lambda(0) < 0.385` and `-0.425 < Lambda^{-1}(0) < -0.415`, and
`Papers.Rockel2026ExactBlest.transposition_fibre_longer` checks that this fibre is longer than `1/2`.

## Retained checks for the removed `(beta,nu)`-region

The previous version of the manuscript also determined the `(beta,nu)`-region.
Its modules stay in the build because other modules import them, and they still
check the earlier results: `Papers.Rockel2026ExactBlest.local_frechet_bounds`, `Papers.Rockel2026ExactBlest.beta_upper_cdf`,
`Papers.Rockel2026ExactBlest.beta_lower_cdf`, `Papers.Rockel2026ExactBlest.beta_nu_region`, `Papers.Rockel2026ExactBlest.beta_upper_exists_unique`,
`Papers.Rockel2026ExactBlest.beta_lower_exists_unique`, `Papers.Rockel2026ExactBlest.nu_beta_bound`, `Papers.Rockel2026ExactBlest.nu_beta_eq_iff`, `Papers.Rockel2026ExactBlest.beta_width`,
and `Papers.Rockel2026ExactBlest.beta_rho_region`. None of these statements appears in the current
manuscript.

## Proof route for the `(nu,nu^T)`-corollary

The map `L(e,n) = (n, 2e-n)` turns the `(eta,nu)`-region into the
`(nu,nu^T)`-region, which gives the first set equality directly
(`Papers.Rockel2026ExactBlest.nu_transpose_fibre_gap`). For the second, Lean first proves that `Lambda`
is a strictly increasing bijection of `[-1,1]`. On the closed branch it writes
`n = 2s^4-1` with `s = ((1+n)/2)^(1/4)`, so that `Lambda(n) = 4s^3-2s^4-1`,
and uses the factorization
`(t-s)(4ts+2(t^2+s^2)(2-t-s))` of the difference. On the parametric branch it
uses strict monotonicity of `n_b` and `nu(B_b)` in the parameter, and it joins
the branches at `-7/8`. Then `Lambda(e-Upsilon(e)) = e+Upsilon(e)` for every `e`
(`Papers.Rockel2026ExactBlest.Lambda_curve`), checked separately on the graph regime, the randomized
regime, and at `e=-1`. With `e = (n+m)/2`, monotonicity of `Lambda` alone shows
that `|n-m| <= 2*Upsilon(e)` holds exactly when
`Lambda^{-1}(n) <= m <= Lambda(n)` (`Papers.Rockel2026ExactBlest.gap_band_iff`). This replaces the
convexity-and-boundary argument of the printed proof and needs no continuity of
Upsilon.

The same identity also gives the printed monotonicity claim: if
`e-Upsilon(e)` failed to increase, applying `Lambda` and adding would
contradict `2e < 2e'`. A copula attaining `m = Lambda(n)` must lie on the lower
`(eta,nu)`-boundary, so uniqueness follows from `Papers.Rockel2026ExactBlest.eta_lower_unique`, and
`Papers.Rockel2026ExactBlest.upper_extremizer_cases` classifies the upper extremizers as `A_w`, `B_b`, or `W`.
Continuity of Upsilon then follows from continuity of the monotone bijection
`e -> e-Upsilon(e)` inside `(-1,1)`, and from the squeeze
`0 <= Upsilon(e) <= min(1+e, 1-e)` at the endpoints.

For the derivative on the randomized branch, the inverse parameter
`e -> b` is monotone with an interval image, hence continuous. The inverse
function theorem for one-dimensional derivatives then differentiates it, and
the chain rule gives `Upsilon'(e_b) = (2-3b)/(2-b)`.

## Proof routes for the two regions

For rho, the internal parameter is `t = 2(1-c)` on the nonnegative-rho half.
The dual potentials are piecewise cubic (one piece uses an absolute value).
Their four rectangle slacks are nonnegative, and their integrals give
`nu-t*rho <= 1-t+t^4/4`. An ordinal sum built from the half-width
two-strip copula has `rho=1-t^3` and `nu=1-3*t^4/4`.
Reflection supplies the negative-rho half; survival supplies the lower
boundary. The real-power identity is checked in Lean, not assumed.

For equality, the integrated nonnegative slack must vanish almost
everywhere. The checked contact identity forces the rank map `zeta_c`, and
`Papers.Rockel2026ExactBlest.copula_eq_of_graph` proves that the uniform first marginal determines
the resulting law. Reflection and survival extend uniqueness to every
rho and both boundaries.

For eta, `stripCopula` glues two probability measures into adjacent
horizontal strips and proves both marginals uniform. The `B_b`
construction uses this law inside an ordinal sum and then reflects it.
The pointwise B-certificate is integrated exactly; its moments, unique
parameter, attainment, and mixtures fill the entire randomized regime. The
endpoint fibre is treated separately. A final module connects both
parameterizations to the displayed Upsilon formulas.

The eta equality proofs integrate the nonnegative slack and use its
almost-everywhere vanishing. In the A regime, four rectangle factorizations
force `Z=T_w(X)` away from two coordinate lines. Uniform marginals make those
lines null, even when `w=1/2` creates an additional horizontal contact segment.
In the B regime, six factorizations instead force `X=R_b(Z)` off null cut
lines; the uniform second marginal fixes the whole law. These arguments
identify the actual ordinal-sum/glued constructions with the manuscript's
graph measures, not just with their coefficient pairs. Transposition gives
the lower boundary. The eta `-1` endpoint follows from Blest-minimum
uniqueness, itself obtained by reflection from the rho support certificate
at parameter zero. At `w=3/4`, the supporting functional is proportional to
`nu-eta`, so the same uniqueness proof gives the full sharp asymmetry cases.

## Points checked carefully in the manual audit

- All moment computations use the reflected variables `X=1-U`, `Z=1-V`.
  The direction of the quadratic weight matters. The Lean moment bridge fixes
  this convention rather than assuming it.
- For `B_b`, the map is read as `X=R_b(Z)`. Its two inverse branches have
  probabilities `1/(2(1-b))` and `(1-2b)/(2(1-b))`. Their densities add to one
  on `(1-b,1]`, while the final branch covers `[0,1-b)` with unit density.
- At `b=1/2`, the middle interval is empty, so its displayed denominator
  `1-2b` is never used. The remaining map and coefficients match `A_(1/2)`.
- At `w=1/2`, the graph-regime dual acquires an extra horizontal contact
  segment. Uniform marginals rule out mass on that segment and on the
  breakpoint's vertical line. This is essential to the paper's uniqueness
  argument, and is not implied by nonnegativity alone.
- In the two-branch certificate, the factors at `z=z_b` reduce to
  `(1-2b)(1-x)`. Their additional zero is the branch junction `(1,z_b)`,
  not an additional positive-mass support component.
- The paper handles the eta endpoints by a strict positive-weight CDF
  argument. The formal proof also supplies them: the A certificate covers
  `+1`, and the rho-certificate/reflection argument above handles `-1`.
- The maximum graph-regime gap is `27/128` at `w=3/4`; the two-branch gap
  increases to `1/8` as `b -> 1/2`. The transition, figure value
  `-2257/2304` for `B_(1/4)`, and all stated sharp constants agree with
  independent exact integration.
- In `cor:nu-transpose`, the parameter of the maximizer is
  `w = ((1+n)/2)^(1/4)` in terms of `n = nu(C)`, while the proof uses
  `w = ((1+e)/2)^(1/3)` in terms of `e = eta`. Both are consistent:
  `nu(A_w^T) = 2w^4-1` and `eta(A_w) = 2w^3-1`.
- The two formulas for `Lambda` agree at `-7/8` with value `-5/8`, and the
  interval `(-1,-7/8)` of the parametric branch is exactly the image of
  `b` in `(0,1/2)`, so `Lambda` is well defined on `[-1,1]`.
- The shuffle in the final remark is the ordinal sum of `W` on `[0,3/4]` and
  `M` on `[3/4,1]`. It is symmetric, has `rho = 5/32` and
  `nu = eta = -7/128`, and so attains `rho-eta = 27/128`.

## Completion and scope

All labeled results of the revised manuscript and the quantitative claims
listed above are proved. The four modules added in the revision are:

- `ExactBlestTranspose.lean`: the parameter `n_b` (internally in the reflected
  parameter), the two branches of `Lambda`, their junction, and the monotone
  bijection.
- `ExactBlestTransposeRegion.lean`: both descriptions of the
  `(nu,nu^T)`-region, the boundary curves, unique extremizers and their
  identification, the closed-form bound, and continuity of Upsilon.
- `ExactBlestClaims.lean`: the dual-certificate lemma, derivative facts,
  symmetries, the bound `1/2`, numerical fibres, and the final remark.
- `ExactBlestPaperParams.lean`: the families `D_c`, `A_w`, and `B_b` in the
  manuscript's parametrization, with every family-dependent statement and all
  figure values restated in that notation.

Historical motivation, references, and literal proof prose are not Lean
statements. Some printed intermediate steps are replaced by the alternative
proof routes documented above. There are no proof placeholders, custom
axioms, or hypotheses equal to unproved paper conclusions. The integrated supplement uses the root Lake project and its pinned dependencies; see README.md for reproduction.
