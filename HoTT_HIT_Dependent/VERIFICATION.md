# Verification record

## Exact reviewed source, 2026-11-12

- Isabelle2026, distribution source ID `096842708b28`.
- Official Linux distribution SHA256:
  `858c995b32216b3876bf395c3be843147d1f1eee404bc6c958d7534ee335e48d`.
- Formal/document source-set SHA256: `6142e1b991c51ecab3387f3fe99328e1914c02a8e5f1a5c8cd4a6209913b10df`.
  The entry's `SOURCE_MANIFEST.json` records the encoding and all 32 constituent digests.
- 29 theories, 7,297 theory-source lines and 509 named lemma/theorem/corollary
  commands, including helper results. Counts do not measure mathematical novelty.
  The in-session oracle-dependency audit retains 111 selected headline references.
- Full proof, 169-page document, 107-page outline and browser build: **exit 0**.
  Command wall time 1:22, CPU 1:10. The verified official parent heap was cached;
  the entire changed dependent session was reprocessed.
- Official mandatory lint: **29 theories, zero findings, exit 0**.
  Default lint: **29 theories, 8 reviewed advisories, zero errors, exit 0**
  with failure threshold `error`. No rules disabled or suppressions added.

Current sanitized receipts are `validation/isabelle2026-review-build.txt`
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

An earlier release freshly rebuilt the official parent and original
30-theory entry in an isolated user configuration. This revision uses that
verified parent and rebuilds the new 29-theory entry. The formal/document
sources published in the standalone repository and monorepo draft are identical.
The current verification target is the external official AFP dependency; older
monorepo-parent builds are historical evidence, not a new check of this revision
against a different parent.

## Independent review and cleanup

`CONSOLIDATION.md` records the preceding organization/proof cleanup. This review
response leaves its existing mathematical definitions, statements and hypotheses
unchanged and adds one focused 196-line path-sensitive example with 19 named
lemma commands. The main theorem introduction defines elementary and tuple
naturality, their common interchange hypotheses, practical use and exact fold
descent premises. `DEPENDENCY_AUDIT.md` names the principal checked results and
explains the transitive oracle check and its limits. Three existing quotient
transport results and eleven model references extend the selected list from
97 to 111; the list remains an explicit selection, not an all-theorem scan.

Independent source review approved the exact example digest
`30e1b736113ae9dbe77089adc6fd41088b1b1cabc459a944654fc71b499f67ee`, its constant-fiber
and involution scope, the nontrivial valid loop, recursive naturality and distinct
binary paths. Independent review also checked the principal equivalence outside
a locale, the additional constructed-fold premises, the audit's ML operation,
and the informal theorem explanation. Earlier reviews covered the underlying
folds, substitution, quotients, interchange, endpoint functoriality and serialization.
These are automated independent reviews, not external human peer review.

`DHIT_Audit` rejects oracle dependencies in its selected headline references;
it is not an all-theorem oracle enumeration. Static/manual inspection found no
admitted proof, new axiomatization, unsafe theorem-producing ML, skipped-proof
mechanism, quick-and-dirty setting or code-printing override. The sole ML block
performs the audit. Locale assumptions, chosen representatives and out-of-domain
HOL `undefined` are described in `TRUST_AND_SCOPE.md`.

A bounded Mirabelle/Sledgehammer pass over the new elementary-naturality proof
made three calls, all timed out, and supplied no shorter proof. The exact test
including the added example exited zero; the existing readable proof was retained.
Generated proof-search directories were removed after preserving private logs.
Earlier cleanup proof-search results are historical and do not replace this run.

The full and outline PDFs have embedded fonts and passed all-page text-boundary
checks and representative visual inspection of the changed abstract, contents,
new model, audit explanation and bibliography. All nine bibliography entries are cited;
there are no missing citation keys. The printed DOI references were inspected.

## Minimal AFP candidate archive

A separately staged archive contains exactly one `HoTT_HIT_Dependent/` top-level
directory and 33 files: ROOT, 29 theories, two document sources and the license.
Every archived byte was compared with the checked source. A separate full
proof/document build of this minimal stage against external AFP also exited
zero (1:03 wall, 0:58 CPU). No validation records, generated files, hidden files
or parent sources are included. The archive is prepared for author review;
it has not been uploaded to AFP.

The new model uses constant integer fibers. Its nullary loop acts by negation
and is proved distinct from the empty path in the combined presentation. The
same model realizes recursive-collapse naturality and binary interchange. Both
slot actions are the same involution and their composite is identity. No
faithfulness or displayed-fold interpretation of this particular model is claimed.

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
