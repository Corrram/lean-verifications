# Handbook and generated Lean documentation

Public site: <https://corrram.github.io/lean-verifications/>.

The website combines four mathematical handbook chapters, metadata-driven
article supplements, and the actual doc-gen4 output under `/api/`. The shared
search reads the generated doc-gen4 declaration index; the original doc-gen4
search remains available too. Handbook equations are rendered at build time
with KaTeX and use locally served styles and fonts.

## Edit the content

- Write handbook chapters in `website/content/*.md`. Use `$...$` and `$$...$$`
  for mathematics. A link beginning `site:` is relative to the deployed site
  root, for example `[Copulas](site:handbook/copulas/)`.
- Edit `Papers/<PaperId>/paper.toml`, `COVERAGE.md`, and `references.bib` to update
  a paper page. Pages are generated from these files; do not edit output HTML.
- New folders created by `scripts/new_paper.py` enter the site automatically
  once their metadata is filled in. `scripts/prepare_docs.py` imports every
  Lean file under `Papers/` and `Verification/`, including modules not imported
  by `Main.lean`.
- A handbook explanation or a generated module page is not a verified article
  result. Update verification status only under the coverage rules in
  [ADDING_A_PAPER.md](ADDING_A_PAPER.md).

## Full build

Use Linux (as in CI), Python 3.11+, Node.js 22+, elan, and a system C compiler
(`cc`, typically installed with `build-essential` on Ubuntu). The doc-gen4
dependencies build C bindings for SQLite and Unicode. The project's Lean-only
build works on Windows; a native documentation build additionally needs a
compatible C toolchain. WSL is an alternative for Windows users.

From the repository root:

```sh
lake exe cache get
lake build
python scripts/prepare_docs.py
cd docbuild
lake build Handbook:docs
cd ../website
npm ci
npm run build
npm run check
```

The site is emitted to `dist/`. Both Lake projects and the npm build have
committed dependency manifests. No dependency update is needed for reproduction.
The doc-gen4 Lake project shares `.lake/packages` with the proof project, while
its own build artifacts remain under `docbuild/.lake`.

CI caches compiled tools and reference data under the dependency pins. The
preparation script refreshes HTML and this project's declarations and source
links. Retiring a project module also clears the reference database, so removed
modules do not survive in cached navigation, search, or tactic indexes.

The default URL prefix is `/lean-verifications/`. For an HTTP preview at `/`,
set `SITE_BASE=/` for both build and check, then serve `dist`:

```sh
SITE_BASE=/ npm run build
SITE_BASE=/ npm run check
python -m http.server 8000 --directory ../dist
```

In PowerShell, set the environment variable with `$env:SITE_BASE = '/'`.
Use HTTP rather than opening HTML files directly: browser search needs fetch.
For a quick handbook-only preview, append `-- --handbook-only` to both npm
commands. This intentionally permits absent API files and is never used in
the publication workflow.

## Publication and provenance

`.github/workflows/website.yml` builds proofs, doc-gen4, and the handbook on
pushes to `main`, pull requests, and manual dispatch. Only branch builds can
deploy. GitHub Pages must use **GitHub Actions** as its source.

The deploy job receives only the Pages and OIDC permissions it needs; pull
requests build without publishing. A failed build or a missing generated
declaration prevents deployment. The checks also reject broken internal
handbook links and missing paper API modules.

The footer and `build-info.json` record the exact source commit. Paper pages
link to immutable source folders and include reproduction commands for that
commit. `docbuild/Handbook.lean` is a generated import index, not an article
proof module.

To update Lean, update the proof and documentation toolchains together and
select the matching doc-gen4 release. Review both Lake manifests. Do not use
doc-gen4's moving `main` branch for a pinned research supplement.
