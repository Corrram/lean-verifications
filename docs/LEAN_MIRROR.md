# LeanMirror mathematical companions

> The LaTeX-compiled sources (`Papers/*/Source`) now use
> [Proofread](https://github.com/Corrram/proofread), the successor of the
> LeanMirror TeX pipeline, pinned in `lakefile.toml` and `lake-manifest.json`.
> The companion engine described below (typed controlled language, proof
> documents and article evidence) lives in this repository as the `Companion`
> library.

The companion engine supplies a language for precise mathematical statements,
their interpretation in Lean, and their readable presentation.

The main reader reproduces the **complete original article** from
[arXiv:2609.27634v1](https://arxiv.org/abs/2609.27634v1), preserving its order,
wording, numbered formulas, result environments, proofs, figures, captions, and
bibliography. Coefficients link to their original definitions. Every labeled
result has links to compiled mathematical counterparts; drawers show their
actual Lean types and lead to the generated API. This is a source-preserving
reader with evidence overlays. It does **not** yet certify every literal passage
of the original proofs; its visible coverage count records that distinction.

The detailed checked proof document covers **all of Corollary 3.2 and its proof** from
[arXiv:2609.27634v1](https://arxiv.org/abs/2609.27634v1): the inequality
`|ν(C) − ρ(C)| ≤ 1/4`, both unique extremizers, their coefficient values and support
graphs. The displayed proof follows the published derivative argument. The
comparison column preserves the published wording, including its references.
This is a complete result from the article; it is not yet a proof document for
the entire article. The earlier results it cites remain compiled dependencies.

## Sources and reproduction

- [ArticleBridge.lean](../Papers/Rockel2026ExactBlest/ArticleBridge.lean): precise
  definitions, theorem, definition correspondences, statement equivalence,
  certificate, and transitive axiom audits.
- [ArticlePresentation.lean](../Papers/Rockel2026ExactBlest/ArticlePresentation.lean):
  the original definition vocabulary and inequality bridge.
- [ArticleCalculus.lean](../Papers/Rockel2026ExactBlest/ArticleCalculus.lean):
  the printed derivative signs, strict monotonicity and unique scalar maximum.
- [ArticleProof.lean](../Papers/Rockel2026ExactBlest/ArticleProof.lean): the scoped
  proof tree and its audited `Argument.Valid` certificate.
- [ArticleDocument.lean](../Papers/Rockel2026ExactBlest/ArticleDocument.lean):
  checked definition notation and export through `checked_document%`.
- [ArticleOriginalProof.lean](../Papers/Rockel2026ExactBlest/ArticleOriginalProof.lean):
  additional checks of the exact displayed moments, parameter conventions,
  rectangle factorizations, derivatives and signs in the original proofs.
- [ArticleIndex.lean](../Papers/Rockel2026ExactBlest/ArticleIndex.lean): generated
  registry that extracts real theorem types and audits their transitive axioms.
- [Article map](../examples/paper-bridge/article-map.json): exact label/quotation
  bindings. A missing or ambiguous passage fails the reader build.
- [Generated LaTeX](../examples/paper-bridge/blest-bound.tex) and
  [website data](../examples/paper-bridge/blest-bound.json).

```sh
lake exe cache get
python scripts/lean_mirror.py
python scripts/lean_mirror.py --check
python scripts/lean_mirror_article.py --check
python scripts/test_lean_mirror.py
python scripts/test_paper_source.py
```

The exporter first builds the certificate. `--check` compares both saved outputs
with a fresh export and rejects any stale or manually altered presentation. The
rejection tests include changed formulas, invalid scope, extra axioms, and `sorry`.
They also reject a false intermediate assertion despite a true final conclusion,
changed extremizer values and altered source excerpts. The original source and
line-selected excerpt are pinned by SHA-256 in `examples/paper-bridge/source.json`.

## Website

The site has a LeanMirror entry and a companion at `/lean-mirror/blest-spearman/`.
Its full-article text comes from the exact pinned original LaTeX. The detailed
Corollary 3.2 document is at `/lean-mirror/blest-spearman/corollary-3-2/`;
its theorem and definition formulas come from the generated JSON. Clickable
symbols lead to definitions; correspondence links lead to generated Lean API
declarations. Both publication CI and Lean CI recompile and check freshness.
The reader imports its proof rendering from the pinned LeanMirror dependency;
subject-specific mathematics stays in this repository. A downloadable source
bundle contains the pinned Lake project and all sources needed to check it.

To build a local content preview:

```sh
npm ci --prefix .lake/packages/lean-mirror
npm ci --prefix website
node website/build.mjs --handbook-only
node website/check.mjs --handbook-only
```

## Trust and scope

The mathematical interpretation and equivalence proofs are checked by Lean's
kernel. The statement correspondence is derived from the definition bridges
and applies pointwise at every real bound before being specialized to `1/4`.
That original bridge remains available. The new proof document is checked
independently: `Argument.sound` derives its conclusion from the validity of
every node. `ExistingCorollary` extracts the types of the existing bound,
uniqueness, family-value and graph theorems with `statement_of%`.
`full_correspondence` connects these to the complete proof document by unfolding
definitions, normalizing the parameter and using the survival identities; it
does not appeal to a proof of the corollary. The readable law defining the tent-map copula
also has a checked identity with `paperD unitHalf`.

Recognizing the intended mathematics in the displayed statement and definitions
is a human judgment. The parser, notation, foundational glossary, and rendering
software have not themselves been formally verified. They are documented in
the [LeanMirror repository](https://github.com/Corrram/lean-mirror).

Extend the general language and compiler in LeanMirror. Keep subject-specific
models, vocabulary, definitions, and equivalence proofs in downstream projects
such as this one. Update the pinned dependency only after checking the companions.

## Additional full-article readers

The Chatterjee–Blest companion is at `/lean-mirror/xi-blest/`. It preserves
arXiv:2603.09768v1 in full, including its numerical table and all figure panels.
The two known false printed claims have visible notices and compiled
counterexamples alongside the checked corrections. Its result and calculation
links are compiled counterparts, not a claim that every literal proof step
has been verified.

The corrected lower-clamped square moment now has a scoped, readable proof
document. It evaluates the primitive at `1` and `r` in two separate checked
steps, then subtracts them to obtain the coefficient `-8/15`. Its independently
encoded primitive definition and pointwise statement correspondence are also
checked. This document accompanies an explicit refutation of the printed
`-1/5` coefficient; it does not certify that erroneous original line.

The Blest–Spearman reader embeds four rectangle calculations from Proposition
4.3 as scoped proof documents. The first two check the factorizations and sign
estimates, including the second rectangle's exact equality set. The last two
check the partial derivatives, their signs, comparison with the relevant edge,
vanishing endpoint values, the edge minimum and final nonnegativity. The edge
minimum is proved using monotonicity from the displayed derivatives, as in the
article. Each displayed conclusion has its own interpretation and correspondence
proof. All four documents retain the article's range `1/2 ≤ w < 1`; their
underlying nonnegativity lemmas also cover `w=1`. This does not yet certify the
entire proposition's literal proof or all its equality cases.

A fifth document composes the four rectangle calculations to cover the whole
unit square. Its four intermediate claims use the checked rectangle documents;
its final obligation splits at `x=1-w` and `z=w`. Its validity certificate does
not call the native dual inequality. The second rectangle document now concludes
both nonnegativity and its equality criterion, so the composition can use the
former while preserving the original contact calculation. A pure interpretation
bridge rearranges the slack inequality to the native dual inequality restricted
to the article's range `1/2 ≤ w < 1`. The full contact-set proof is still a
separate outstanding obligation.

All nine other manuscripts have been imported into `examples/articles/` with
versioned arXiv provenance and hashes for every unchanged source file. An import
does not make a manuscript a certified companion. Only directories with an
explicit `article-map.json` are built as article readers.

```sh
python scripts/check_article_sources.py
python scripts/test_article_sources.py
python scripts/lean_mirror_article.py --check
# Recompile one authored map while extending it:
python scripts/lean_mirror_article.py --paper Rockel2026XiBlest
```

Source-to-theorem bindings identify an exact label or a unique literal passage;
there is no fuzzy matching. Each generated registry extracts the actual Lean
theorem type with `checked_native%` and audits its transitive axioms. Full proof
documents additionally use `checked_document%` on a closed validity certificate.
An authored map may name a `proofDocumentNamespace` in the same paper module;
the exporter compiles and extracts that namespace's proof documents alongside
the theorem registry. This lets downstream articles add typed proof passages
without adding subject-specific code to LeanMirror itself.

The Chatterjee–Blomqvist reader at `/lean-mirror/xi-beta/` preserves
arXiv:2606.30033v2, including the original wide title block, section equation
numbers, bibliography and figures. Its date is pinned to the source version;
rendering `\today` never silently substitutes the build date. All thirteen
labeled results have compiled counterparts. The beta and attainable-region
definitions, the exact-region statement and universal cubic inequality have
independent typed encodings and checked correspondence. The region equivalence
uses only interpreted definitions and set extensionality, without invoking the
proved region theorem. The accompanying one-step statement documents reuse
the native theorems; they do not certify the printed proof of Proposition 4.1.
In particular, a full
bridge from the convex-function hypotheses in Lemma 5.2 to the slope-data
encoding remains outstanding. These limits are stated in the reader itself.

An optional `evidenceModule` names a module in the current paper namespace
containing additional definition or statement bridges. It is compiled before
the registry is exported. The subject-specific model stays downstream; the
generic parser and renderer stay in the LeanMirror package.

Article exports sort JSON keys and the axiom/dependency collections so field
ordering cannot invalidate a cross-platform rebuild. Source hashes, theorem
types and ordered proof steps remain exact. A freshness failure reports the
first differing data field rather than just a generic stale-export message.

The Chatterjee–Spearman footrule reader at `/lean-mirror/xi-footrule/` preserves
arXiv:2509.07232v1, including all fourteen definition and result blocks, two
tables, three figures with nine panels, and twenty-seven references. The six
checkerboard panels retain the original two rows of three. Eleven result blocks
have compiled counterparts; the external copula characterization and two KKT
lemmas in the appendix are not covered by these bindings.

The definitions of both coefficients and the Fréchet family have independent
typed encodings and checked correspondence. The complete maximum statement
includes attainment, uniqueness and both endpoints. Its statement certificate
reuses the native theorem; it does not certify the original KKT proof. The
reader also shows two refuted source claims, with the original text intact:
the printed checkerboard matrix is not LTD, and the inverse cubic does not have
a unique unrestricted real root. A separate checked proof document evaluates
the cubic at two distinct roots when `y=-1/2`. The corrected inverse theorem
restricts the root to `[0,2]`. Numerical optimization experiments remain
visible but are not presented as formal proofs.

The joint Kendall–footrule–Blomqvist reader at `/lean-mirror/tau-footrule-beta/`
preserves arXiv:2607.12841v1. All nine result blocks, six proof environments,
three published figures and nineteen references are retained. The original
comment environment excludes two further source figures; the reader respects
that choice and the executable bundle retains those assets.

Its three coefficient definitions, concordance integral and four boundary
functions have checked bridges. The integral defining the concordance function
uses the article's argument order, with its correspondence justified by symmetry
of the native function. The entire joint-region statement has an independent
typed encoding; its interpretation bridge does not invoke the region theorem.
The final mixture paragraph of the main proof also has a ten-node proof
document: five fixed quantities, the endpoint hypotheses, three intermediate
claims and a conclusion. It checks affine footrule and beta, quadratic tau,
the intermediate-value step and the attaining copula. Both endpoints must
already have the same footrule and beta. This scoped argument does not certify
their earlier construction or every other printed proof step.


The Chatterjee–Spearman reader at `/lean-mirror/xi-rho/` preserves
arXiv:2506.15897v3. Its twenty-two result blocks, fifteen proof environments,
five figures containing eleven panels, three rank-calculation headings and
fifty-one references retain their source order. Fifteen result blocks have
compiled counterparts; some links cover only explicitly identified clauses.

The copula formulas for xi and rho and the complete SI/SD statement of
Theorem 2 have independently parsed encodings and checked correspondence.
SI and SD use the concavity/convexity chord definitions. The statement
certificate reuses the native theorem and does not certify the printed
maximum-principle proof. Optimization links cover actual copulas, without
claiming a checked correspondence with all preceding measurable-family
constraints.

Lemma 8's literal pointwise equality classification is refuted by a checked
five-step counterexample: h(0)=1 and h(t)=1/2 for t>0. Its mean is 1/2 and its
functional is 1/4, although it equals neither displayed alternative everywhere.
The unchanged printed statement appears beside this counterexample and its
corrected almost-everywhere counterpart. The arXiv v3 CDF already contains
the boundary term omitted by the separate journal formula; this reader does
not incorrectly flag that corrected arXiv formula as false. Exhaustive
verification of the original proof steps remains in progress.

The rho–footrule reader at `/lean-mirror/rho-footrule/` preserves
arXiv:2608.20176v1: forty result blocks, twenty-three proof environments,
seven figures containing eight panels, author affiliations and thirty-seven
references. Sixteen result blocks have compiled counterparts with explicit
scope notes. The repeated source label for equations (7) and (41) has distinct
anchors and evidence links; ordinary cross-references explicitly select the
second occurrence. The original source remains unchanged.

Rho and footrule have independently parsed integral definitions. Corollary
1.2 has an independent typed statement using the printed real power `3/2`.
Its lower boundary is proved equal to the native cubed-square-root formula
on `[-1/2,1]`; the interpretation bridge does not invoke the region theorem.
The upper boundary retains the native scalar function, with separate links
to its arithmetic arc formulas, attainment and uniqueness.

An eight-node proof document checks Corollary 1.2's final mixture argument:
four fixed quantities, the supplied endpoint hypotheses, coefficient
affineness, the intermediate-value step and the final copula witness. Its
validity proof does not invoke the existing interpolation or exact-region
theorem. This does not certify the preceding endpoint construction, the
later `x=1` paragraph, the abstract pair-measure and Kantorovich duality
arguments, or every other printed proof step. Random-variable statements
with only copula-law counterparts carry that limitation explicitly.

The rho–Gini gamma reader at `/lean-mirror/rho-gamma/` preserves
arXiv:2609.19890v1, including all seventeen result blocks, fourteen references,
the three authors and their shared affiliation, and the two original PDF
figures (seven panels). All seventeen result blocks have compiled counterparts.

The coefficient integrals, splitting parameters and composite boundary
coordinates have independent typed encodings. The gamma bridge justifies
splitting the printed integral of a sum into the two native integrals. The
upper boundary is characterized as an attained maximum. The exact-region
clause has a typed statement and an interpretation bridge that does not invoke
the native region theorem. Other clauses retain explicitly scoped counterparts.

A ten-node proof document checks the printed strict-monotonicity paragraph:
choose an optimizer at `g1`, show its rho is below one, choose
`eta=(g2-g1)/(1-g1)`, and mix it with `M`. The prescribed gamma, affine rho,
strict increase and comparison with the upper boundary are checked separately.
The validity proof does not invoke the existing strict-monotonicity theorem.
It does reuse the preceding boundary attainment and global bound. This does
not certify every earlier proof paragraph or the auxiliary piecewise formulas.

The introduction reverses the endpoint convention relative to Definition 3.8
and the later formulas. The reader preserves the text and flags the conflict.
Lean proves `G(0)=-1` and `G(0) != gamma(M)`, whereas `gamma(M)=1`.

PDF figures remain unchanged in the executable bundle. An explicit figure map
records the source PDF, inspected browser rendering, both SHA-256 hashes,
renderer version, page and resolution. Publication checks both files against
the compiled asset manifest. These provenance checks detect changed assets;
they do not certify numerical plots or the rendering software itself.


The approximation reader at `/lean-mirror/copula-approximation/` preserves
arXiv:2505.08045v2, including all eleven result blocks, nine figures with fifteen
panels, the simulation table, appendix and thirty-two references. Ten result
blocks have compiled counterparts. The numerical grid-choice example remains
source exposition. Appendix page references retain the published PDF's page
numbers and link to the corresponding proofs; their inspected provenance is
recorded as presentation metadata in the source map.

Spearman rho, Chatterjee xi and the estimator arithmetic have independent typed
encodings and checked interpretation bridges. The rectangular MTP2 inequality
has a typed statement certificate. The averaging/range argument, finite trace
correction bound and permutation-sum proof have separate checked proof documents.
The permutation document follows the printed first/second moment reindexing and
algebraic expansions, explicitly converting native zero-based indices to the
source labels `1,...,n`. Matrix traces and finite sums use actual Lean operations;
their arithmetic is parsed, but there is not yet a general independent matrix
or summation syntax. The trace certificate does not invoke the native correction
bound, and the range certificate does not invoke the native estimator-range result.

The native consistency theorem covers actual iid rank samples with continuous
marginal CDFs and `0<kappa<=1/3`; the work bound covers a specified unit-cost
comparison/arithmetic schedule. These are scoped compiled counterparts, distinct
from exhaustive checking of every printed proof step. Plots, experiments,
historical claims and the remaining proof passages retain their original text
without a claim of complete formal verification.

## Dependence properties of bivariate copula families

The reader at `/lean-mirror/copula-families/` preserves the complete arXiv v3
article: eighteen numbered results, six tables, six figures with forty-four
panels, the appendix proofs and sixty references. The printed date is 9 April
2024; the arXiv version stamp is 6 April. Source files and figures remain
byte-for-byte pinned. Third-level headings, table checkmarks and crosses, and
separate captions within one figure float retain their source organization.

The rho, xi, survival CDF and lower-orthant definitions have independent typed
encodings and compiled bridges. Proposition 3.2(i) has a checked proof document
following the survival identity, reindexing by 1-u and 1-v, and cancellation of
the common affine term. It does not use the existing survival-order equivalence.
The later CIS and Schur clauses have compiled counterparts but their printed
proofs are not yet certified step by step.

Table links collect the audited native family results. These are an index of
compiled counterparts, not an independent encoding of every cell. Incorrect
printed cells remain visible with the source discrepancy notices and checked
corrections; the Nelsen 7 intermediate xi equality also has an explicit
refutation. Four numbered results remain unbound, including the general
elliptical proposition and the arbitrary-margin conditional-distribution
definition. Numerical plots and all remaining literal proof passages are not
certified.
