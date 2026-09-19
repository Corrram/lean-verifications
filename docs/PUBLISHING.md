# Publishing and citing a supplement

The permanent folder identifies the article. A repository commit identifies
the exact code, coverage statement, and shared build environment used for a
particular submission or publication.

## Prepare a snapshot

1. Specify the covered results and omissions in the paper's `COVERAGE.md`.
   Check source numbering against the selected journal or arXiv version.
2. Fill in the bibliography and metadata. Mark `complete-for-scope` only when
   every result in that scope has a checked declaration and reviewed hypotheses.
3. Run `lake build` and inspect the article's axiom reports. Confirm that a
   fresh checkout can run `lake exe cache get` and `lake build` using the
   committed manifest. Do not update dependencies during this reproduction.
4. Commit the source and metadata and let CI pass for that exact commit. Obtain
   its full SHA with `git rev-parse HEAD`.
5. For a release, use an article-specific tag such as
   `AnsariRockel2024-v1.0.0`. Do not move a published tag; issue a new version
   for corrections. A GitHub release may describe which article folder it
   covers even though the snapshot contains the whole repository.

No release, archive, or software DOI is created by the project scaffold. If
you later archive a release with a DOI provider, cite that software DOI along
with the paper identifier and source commit. Never reuse the article DOI as
the software DOI.

## Link format

For readers browsing the latest development work:

```text
https://github.com/Corrram/lean-verifications/tree/main/Papers/<PaperId>
```

For an article, replace `<commit-sha>` with the full SHA of its checked snapshot:

```text
https://github.com/Corrram/lean-verifications/tree/<commit-sha>/Papers/<PaperId>
```

Do not paste placeholder URLs into a manuscript. A commit permalink is
available publicly only after that commit has been pushed.

Suggested wording, adapted to the actual coverage:

> Lean 4 formalizations of the results listed in the accompanying coverage map
> are available in the `Papers/<PaperId>` folder of `lean-verifications`, at
> commit `<commit-sha>` [permalink]. The supplement records the hypotheses,
> scope, and pinned dependencies used for verification.

Refer to the coverage map rather than claiming verification of the whole
article when only selected results are formalized. Cite the original article
separately from the software. The repository's `CITATION.cff` identifies the
software author; each folder's `references.bib` identifies the article authors.

## Reproduce a published snapshot

```sh
git clone https://github.com/Corrram/lean-verifications.git
cd lean-verifications
git checkout --detach <commit-sha>
lake exe cache get
lake build
```

The paper folder is the landing page, but reproduction uses the whole checkout
because its toolchain and dependency lock are at the repository root.
