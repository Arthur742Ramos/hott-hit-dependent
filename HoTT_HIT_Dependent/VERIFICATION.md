# Verification record

## Exact final source, 2026-11-12

- Isabelle2026, distribution source ID `096842708b28`.
- Official Linux distribution SHA256:
  `858c995b32216b3876bf395c3be843147d1f1eee404bc6c958d7534ee335e48d`.
- Formal/document source-set SHA256:
  `20e62f36eb48ee3df081e219e1b19d2b835dd3889c013638886b5ccdbe7a045a`.
  `SOURCE_MANIFEST.json` specifies the encoding and all 33 constituent digests.
- 30 theories, 7,059 theory-source lines and 490 named lemma/theorem/corollary
  commands, including helper results. These counts do not measure mathematical
  novelty. The in-session audit checks 97 selected headline fact references.
- Full proof and PDF builds passed with exit status zero against both parents:
  1. Exact monorepo parent sources at commit
     `19e0a78dd218264540a7bc8c3f96fbddc730ffc2`.
  2. The pinned public AFP dependency documented in `vendor/PROVENANCE.md`
     of the standalone package.
- The initial builds used independently initialized Isabelle user-state
  directories and rebuilt the parent metatheory and the new entry. No prior
  custom session heap supplied the new proofs. PDF inspection then prompted
  two whitespace-only line wraps in proof text. The exact final entry was
  rebuilt with proofs, oracle audit and PDF output against each cached parent.
- The entry's formal/document sources are byte-identical in both configurations.
  All 17 monorepo parent formal/document files were compared with their remote
  Git blob hashes. The public dependency's recorded SHA256 hashes also passed.

## Reproduction

From the standalone repository root, run:

```sh
isabelle build -D . -o threads=2 -o document_build=pdflatex \
  -o document=pdf -o browser_info=true \
  -o "document_variants=document:outline=/proof,/ML" HoTT_HIT_Dependent
```

This produces both the full document and the AFP-style outline. In the
monorepo configuration, add the parent metatheory directory with `-d` and use
`-D` on this entry. The two configurations share the same session and theory
sources. The sanitized build summaries in the standalone `validation/`
directory distinguish fresh-parent runs from final formatting rechecks.

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

A final bounded Mirabelle/Sledgehammer pass over selected local/global locale
assembly proof ranges made one nontrivial call, which timed out. It supplied no
replacement proof and no source changes. This is separate from, and does not
invalidate, the successful checked Isabelle proofs. Earlier development passes
are not counted as extra evidence for this final source snapshot.

The final 161-page full PDF and 101-page outline have embedded fonts and passed
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

The official AFP linter has not been installed or run. AFP editorial suitability,
author/maintainer metadata, final readiness approval and submission remain
separate gates. No AFP, journal or registry submission, external editor contact
or repository CI success is claimed by this record.
