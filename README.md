# lean-verifications

Lean 4 formalizations accompanying research articles by Marcus Rockel and
collaborators. Each article has a permanent folder under [`Papers/`](Papers/README.md)
with its bibliography, proof sources, and an explicit record of which results
have been formalized.

**Current status:** five supplements are **complete for their stated scopes**:
xi-beta, tau-footrule-beta, rho-gamma, corrected xi-rho, and copula approximation.
The other four remain **in progress**. Coverage includes the exact
xi-beta region and several subclasses; the exact SI xi-footrule region and full equality classification, universal
upper and explicit Jensen lower bounds, admissible cubic inversion, and entire bottom boundary; the full SI/SD xi-rho theorem and sharp rho-minus-xi maximum 2/5 with unique attainment;
the full xi=1 slices for footrule, rho and Blest, and convexity of all three xi regions; the exact joint tau/footrule/beta region, signed shuffles, geometry and volume; rho-footrule contact
points; sign-magnitude and transport certificates for rho-gamma; and rank/tail
formulas for every straight permutation shuffle and all equal diagonal grids. Each coverage map specifies its exact scope
and pending work. CI checks the maps and rejects nonstandard axioms behind every
declaration advertised as verified.

## Handbook and Lean reference

Read the [mathematical handbook](https://corrram.github.io/lean-verifications/)
for definitions, conventions, and article coverage maps. The
[Lean API reference](https://corrram.github.io/lean-verifications/api/) is generated
with a pinned version of [doc-gen4](https://github.com/leanprover/doc-gen4).
[Search](https://corrram.github.io/lean-verifications/search/) covers the handbook,
papers, and generated declarations. Each paper also has a stable web address:
`https://corrram.github.io/lean-verifications/papers/<PaperId>/`.

GitHub Pages rebuilds both parts after a successful proof and documentation
build on `main`. The website reflects the latest deployed source; cite a full
commit permalink when identifying a publication's exact supplement.
See [website authoring and reproduction](docs/WEBSITE.md).

## Articles

| Article | Supplement | Status |
| --- | --- | --- |
| Ansari & Rockel (2024), *Dependence properties of bivariate copula families* | [AnsariRockel2024](Papers/AnsariRockel2024/README.md) | In progress; selected family formulas and tails, exact Frechet/Mardia dependence and Nelsen 7 xi/Schur classifications and parameter orders |
| ξ–ρ region and inequality (2026) | [AnsariRockel2026XiRho](Papers/AnsariRockel2026XiRho/README.md) | Complete for corrected scope; full region, SI/SD theorem, sharp gap, density/support/MTP2, all ranks, asymmetry, and formal journal correction |
| ξ–footrule region (2026) | [Rockel2026XiFootrule](Papers/Rockel2026XiFootrule/README.md) | In progress; exact SI region, Jensen bound, closed full region and boundary attainment, and two-parameter density with endpoints |
| Association measures for approximating copulas (2025) | [Rockel2025Approximation](Papers/Rockel2025Approximation/README.md) | Complete for stated scope; arbitrary-partition ranks, MTP2 monotonicity, counterexamples, population and iid estimator consistency, and unit-cost complexity |
| ξ–Blest region (2026) | [Rockel2026XiBlest](Papers/Rockel2026XiBlest/README.md) | In progress; normalization, symmetries, xi=1 boundary, full-region convexity/compactness and attained slice extrema |
| ξ–β region (2026) | [OrendayLaresRockel2026XiBeta](Papers/OrendayLaresRockel2026XiBeta/README.md) | Complete for stated scope; exact regions, tent properties and SI/SD rigidity |
| τ–footrule–β region (2026) | [OrendayLaresRockel2026TauFootruleBeta](Papers/OrendayLaresRockel2026TauFootruleBeta/README.md) | Complete for stated scope; exact joint region, signed shuffles, geometry and volume |
| ρ–footrule region and applications (2026) | [AnsariRockel2026RhoFootrule](Papers/AnsariRockel2026RhoFootrule/README.md) | In progress; exact regions, finite-ranking, mixability and xi/correlation-ratio bounds |
| ρ–γ region (2026) | [AnsariRockelSteinmassl2026RhoGamma](Papers/AnsariRockelSteinmassl2026RhoGamma/README.md) | Complete for stated scope; original theta family, exact region, shuffle laws, endpoint asymptotics and attained duality |

## Reproduce the build

Install [Lean's elan toolchain manager](https://lean-lang.org/install/), then:

```sh
git clone https://github.com/Corrram/lean-verifications.git
cd lean-verifications
lake exe cache get
lake build
python scripts/check_verification.py
```

Lean is pinned to **4.34.0**. The `copula` dependency is pinned to the commit
`5926399c46f83d307127fd34b3aa2e416c940786`, and `lake-manifest.json` records all transitive revisions,
including mathlib. The Git dependency works before and after Reservoir indexing;
indexing is not required for this build. Do not run `lake update` when reproducing
a published supplement.

Build just the first article's entry point with:

```sh
lake build Papers.AnsariRockel2024.Main
```

Run the full `lake build` before publication: it includes **every** Lean file
under `Papers/` and `Verification/`, even files omitted from an entry point.
This uses [Lake's module globs](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).
Warnings are errors, including warnings for unfinished proofs. GitHub Actions
runs the same full build on pushes and pull requests.

## Layout

```text
Papers/
  AnsariRockel2024/       Article-specific supplement and stable link target
    README.md            Publication, scope, reproduction and citation
    paper.toml           Bibliographic metadata and verification status
    references.bib       Source article citation
    COVERAGE.md          Article result -> Lean declaration, with assumptions
    Definitions.lean     Article-specific definitions and notation
    Main.lean            Public entry point for the article's results
    Axioms.lean          Axiom reports for the final theorem declarations
  AnsariRockel2026XiRho/  Same layout for the xi-rho article
  ...                    Additional article folders listed above
Verification/            Shared infrastructure and cross-paper helper lemmas
templates/paper/         Starter files for the next article
scripts/new_paper.py     Creates a paper folder without changing the build config
docs/                    Authoring and publication instructions
lakefile.toml            One shared, pinned dependency environment
lake-manifest.json       Exact dependency revisions
lean-toolchain           Exact Lean release
```

Keep generally useful copula mathematics in
[`copula`](https://github.com/Corrram/copula). This repository records how those
results establish particular statements in particular versions of articles.
Keep each paper independent of other paper folders; put genuinely shared helpers
in `Verification/` or upstream them. All folders use the root Lake project, so
readers should clone the whole repository rather than download one folder.

## Add an article

With Python 3.11 or newer:

```sh
python scripts/new_paper.py Author2026ShortTitle
```

Choose the identifier once and keep it stable, including if the title, journal,
or publication year later changes. Fill in the generated metadata and coverage
map, then add the article to the tables here and in `Papers/README.md`.
See [the authoring guide](docs/ADDING_A_PAPER.md).

## Link from an article

Use `Papers/<PaperId>/` as the reader-facing supplement. For a submitted or
published article, cite a **full commit permalink**, not the changing `main`
branch. The commit also fixes the shared dependencies used by that supplement.
See [the publication and citation guide](docs/PUBLISHING.md) for the URL format,
release conventions, and suggested manuscript wording.

Repository software metadata is in [CITATION.cff](CITATION.cff). Each article
folder separately records the publication it accompanies; the article DOI and
any future software archive DOI identify different objects.

Code and original repository documentation are licensed under
[Apache 2.0](LICENSE), matching `copula`. Linked articles retain their own licenses.
