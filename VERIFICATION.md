# Verification record

## Current packaging: external official AFP checkout

The public repository and source ZIP no longer vendor the parent entry.
Project `ROOTS` lists only `HoTT_HIT_Dependent`; the unchanged session inherits
`HoTT_HIT_Metatheory` from a separately supplied official AFP checkout.
`AFP_DEPENDENCY.md` and `AFP_DEPENDENCY_SHA256SUMS` at the public source package root pin
and verify the dated official `afp-2026-11-12` snapshot. Its complete archive
SHA256 is `7d1c36b42ce9ba65a0b38f576324038a2d682a44f36f3a8e53ce8a2dc3d97583`.

A fresh isolated Isabelle2026 user configuration rebuilt the official parent
and all 30 new theories, including the 97-reference oracle audit, both PDFs
and browser documentation. The full command exited 0. The current sanitized
receipt is `validation/isabelle2026-external-afp-build.txt` in the public
source package.
Mandatory and default linter bundles were rerun against this external-checkout
configuration: respectively zero findings and 19 reviewed advisory warnings,
with no errors and exit 0 in both runs. No rules were disabled.

This is packaging and documentation cleanup only: the 33 formal/document files
and source-set digest below are unchanged. The rebuilt full/outline PDFs retain
162/102 pages and have identical extracted text, word geometry and font names
to the previously reviewed documents. Existing PDF deliverables remain valid.
Prior commits and artifact versions preserve the earlier bundled package;
its historical build evidence remains below, clearly separated from the
current external-checkout verification. No previous-entry source was modified.

## Exact final source, 2026-11-12

- Isabelle2026, distribution source ID `096842708b28`.
- Official Linux distribution SHA256:
  `858c995b32216b3876bf395c3be843147d1f1eee404bc6c958d7534ee335e48d`.
- Formal/document source-set SHA256:
  `bbe74d0f6c3d17973d7e9913309989c39e42c082f4d330cfb3271f11f2a6ee20`.
  `SOURCE_MANIFEST.json` specifies the encoding and all 33 constituent digests.
- 30 theories, 7,063 theory-source lines and 490 named lemma/theorem/corollary
  commands, including helper results. These counts do not measure mathematical
  novelty. The in-session audit checks 97 selected headline fact references.
- Full proof and PDF builds passed with exit status zero against both parents:
  1. Exact monorepo parent sources at commit
     `19e0a78dd218264540a7bc8c3f96fbddc730ffc2`.
  2. The pinned public AFP dependency now documented in `AFP_DEPENDENCY.md`
     at the public source package root. Earlier runs bundled these exact parent bytes;
     the current package instead imports them from an external AFP checkout.
- The initial builds used independently initialized Isabelle user-state
  directories and rebuilt the parent metatheory and the new entry. No prior
  custom session heap supplied the new proofs. PDF inspection then prompted
  two whitespace-only line wraps in proof text. A later official-linter pass
  motivated two proof-structure/scoping corrections, without changing any
  mathematical statement or assumption. The exact final entry was rebuilt
  with proofs, oracle audit and PDF output against each cached parent.
- The entry's formal/document sources are byte-identical in both configurations.
  All 17 monorepo parent formal/document files were compared with their remote
  Git blob hashes. The public dependency's recorded SHA256 hashes also passed.

## Reproduction

Set `AFP` to the root of the separate official AFP checkout described in
`AFP_DEPENDENCY.md`. From the public source package root, run:

```sh
isabelle build -d "$AFP/thys" -D . -o threads=2 -o document_build=pdflatex \
  -o document=pdf -o browser_info=true \
  -o "document_variants=document:outline=/proof,/ML" HoTT_HIT_Dependent
```

This produces both the full document and the AFP-style outline. In the
monorepo configuration, add the parent metatheory directory with `-d` and use
`-D` on this entry. The two configurations share the same session and theory
sources. The sanitized build summaries in the standalone `validation/`
directory distinguish fresh-parent runs, formatting rechecks and the final
post-lint full builds. Those earlier summaries are historical evidence. The
current external-AFP build has its own clearly labeled validation record.

## Independent review and trust

Separate automated read-only mathematical reviews covered the construction of
folds from point methods, arbitrary displayed recursive hypotheses, original
endpoint interpretation, whole displayed-algebra substitution, contextual
paths, indexed quotient actions and all-fiber descent. The expanded review
also covered signed interchange derived from positive squares, n-ary
constructor and endpoint functoriality, elementary serialization and coordinate
recovery, local/global naturality equivalence, coherent constructed elimination,
and the successful and counterexample models. Final scope documentation was
independently reviewed. This is not external human peer review or AFP acceptance.

`DHIT_Audit` rejects oracle dependencies in the 97 selected headline fact
references; it is not an all-theorem oracle enumeration. Static/manual
inspection found no admitted proof, new axiomatization, unsafe theorem-producing
ML, skipped-proof mechanism, quick-and-dirty setting or code-printing override
in the new entry. The sole ML block performs the audit. Explicit locale
hypotheses, chosen representatives and out-of-domain HOL `undefined` are
documented in `TRUST_AND_SCOPE.md`, not treated as discharged assumptions.

A bounded Mirabelle/Sledgehammer pass after the lint corrections examined the
touched interchange proof range: three calls, two timeouts and one suggestion
of the existing `by simp` proof. No source changes resulted. An earlier pass
over the local/global assembly had one timeout. These exploratory outcomes are
separate from the successful checked Isabelle proofs.

The final 162-page full PDF and 102-page outline have embedded fonts and passed
all-page text-boundary checks and representative visual inspection, including
the scope, examples, coherent-elimination result and references. An initial
clipped proof line was corrected and both configurations rechecked.

## Scope and remaining readiness gates

The central equivalence is within the same explicit sufficient interchange
interface on both sides. Elementary naturality ranges over contextual edges,
all valid outer constructor shells and every source-fiber value. It is not a
claim that bare generator squares alone suffice. Coherent elimination also
requires the uniform displayed-method laws on the same signature and actions,
and begins on the admitted constructor grammar, not arbitrary raw terms.

The development uses set-valued fibers and indexed hom-set quotients. It does
not establish a new dependent object calculus, a full typed HIT universal
property, higher groupoid-valued motives, quotient-level substitution,
normalization or a decision procedure for quotient equality. Imported
object-language typing needs its stated external-carrier hypotheses.

The official Isabelle2026-v1.0.0 linter processed all 30 theories. Its
`afp_mandatory` bundle passed with zero findings and exit 0; the `default`
bundle reported 19 independently reviewed advisory warnings and no errors.
No lint rules were disabled. `LINT.md` pins the tool, source and exact scope;
a mandatory pass does not certify every AFP guideline. AFP editorial
suitability, author/maintainer metadata, final readiness approval and submission
remain separate gates. No AFP, journal or registry submission, external editor contact
or repository CI success is claimed by this record.
