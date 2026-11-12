# Verification record

## Exact consolidated source, 2026-11-12

- Isabelle2026, distribution source ID `096842708b28`.
- Official Linux distribution SHA256:
  `858c995b32216b3876bf395c3be843147d1f1eee404bc6c958d7534ee335e48d`.
- Formal/document source-set SHA256: `3b406539212fa7901f2a545f40a55e16a54194abdaa718378fe9beafc32b722e`.
  The entry's `SOURCE_MANIFEST.json` records the encoding and all 31 constituent digests.
- 28 theories, 7,076 theory-source lines and 490 named lemma/theorem/corollary
  commands, including helper results. Counts do not measure mathematical novelty.
  The in-session oracle-dependency audit retains all 97 selected headline references.
- Full proof, 162-page document, 101-page outline and browser build: **exit 0**.
  Command wall time 1:23, CPU 1:12. The verified official parent heap was cached;
  the entire changed dependent session was reprocessed.
- Official mandatory lint: **28 theories, zero findings, exit 0**.
  Default lint: **28 theories, 8 reviewed advisories, zero errors, exit 0**
  with failure threshold `error`. No rules disabled or suppressions added.

Current sanitized receipts are `validation/isabelle2026-consolidated-build.txt`
and `validation/isabelle2026-lint.json` in the standalone public package.
Earlier build receipts are explicitly historical; they do not verify this
changed source set. No repository CI success is claimed.

## External dependency and reproduction

The new entry inherits the already-published `HoTT_HIT_Metatheory` session
from a separate official AFP checkout. The project ROOTS lists only the new
entry; no parent sources or archive are vendored. `AFP_DEPENDENCY.md` and
`AFP_DEPENDENCY_SHA256SUMS` at the public package root pin the tested official
`afp-2026-11-12` snapshot, archive SHA256
`7d1c36b42ce9ba65a0b38f576324038a2d682a44f36f3a8e53ce8a2dc3d97583`.
The parent's 17 file checksums passed. No parent-entry source was modified.

Set `AFP` to that separate checkout and run from the public source package:

```sh
isabelle build -d "$AFP/thys" -D . -o threads=2 -o document_build=pdflatex \
  -o document=pdf -o browser_info=true \
  -o "document_variants=document:outline=/proof,/ML" HoTT_HIT_Dependent
```

The preceding release freshly rebuilt the official parent and original
30-theory entry in an isolated user configuration. This cleanup uses that
verified parent and rebuilds the new 28-theory entry. The formal/document
sources published in the standalone repository and monorepo draft are identical.
The current verification target is the external official AFP dependency; older
monorepo-parent builds are historical evidence, not a new check of this revision
against a different parent.

## Independent review and cleanup

`CONSOLIDATION.md` records the two coherent module merges, generic dependency
separation and seven proof-script improvements. Independent exact-diff review
confirmed the same multiset of named declarations, unchanged definitions,
statements and hypotheses, and byte-identical lists of all 97 audit references.
The intentionally affected theory-qualified global names are documented there.
Mathematical review retains explicit fiber, grammar and coherence hypotheses.
Earlier independent reviews covered the folds, substitution, quotients,
interchange, endpoint functoriality, serialization, local/global theorem and
models. These are automated independent reviews, not external human peer review.

`DHIT_Audit` rejects oracle dependencies in its selected headline references;
it is not an all-theorem oracle enumeration. Static/manual inspection found no
admitted proof, new axiomatization, unsafe theorem-producing ML, skipped-proof
mechanism, quick-and-dirty setting or code-printing override. The sole ML block
performs the audit. Locale assumptions, chosen representatives and out-of-domain
HOL `undefined` are described in `TRUST_AND_SCOPE.md`.

Two bounded Mirabelle/Sledgehammer passes were inspected. The touched generic
path-image proofs yielded two timeouts and no suggestion. The final equivalence
assembly yielded one timeout and two successful suggestions using `simp` in
place of direct named `rule` applications. Those are not clearer or shorter;
the existing explicit dependency references were retained. Both exploratory
commands exited zero; their outcomes are not substitutes for the proof checks.
Generated Mirabelle directories were removed after preserving private logs.

The full and outline PDFs have embedded fonts and passed all-page text-boundary
checks and representative visual inspection of the changed abstract, contents,
merged sections and bibliography. All nine bibliography entries are cited;
there are no missing citation keys. The printed DOI references were inspected.

## Minimal AFP candidate archive

A separately staged archive contains exactly one `HoTT_HIT_Dependent/` top-level
directory and 32 files: ROOT, 28 theories, two document sources and the license.
Every archived byte was compared with the checked source. A separate full
proof/document build of this minimal stage against external AFP also exited
zero (1:12 wall, 1:17 CPU). No validation records, generated files, hidden files
or parent sources are included. The archive is prepared for author review;
it has not been uploaded to AFP.

## Scope and readiness

The central equivalence retains the same explicit sufficient all-fiber
interchange interface on both sides. Elementary naturality covers contextual
edges, every valid outer shell and every source-fiber value. Fold descent also
requires the uniform displayed-method laws and starts within its constructor
grammar, not at an arbitrary raw term. Set-valued fibers and indexed hom-set
quotients do not establish a new dependent object calculus, full typed HIT
universal property, higher groupoid motives, quotient-level substitution,
normalization or decidable quotient equality.

Technical checks support an author-review candidate, not guaranteed AFP
acceptance. Author/maintainer metadata and commitment, explicit final readiness
approval, and authorization to submit remain separate gates. The existing PR
remains a draft; this cleanup does not change its review status. No AFP upload,
editor contact, journal or registry submission has occurred.
