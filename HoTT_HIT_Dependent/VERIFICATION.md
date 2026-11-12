# Verification record

## Exact final source, 2026-11-12

- Isabelle2026, distribution source ID `096842708b28`.
- Official Linux distribution SHA256:
  `858c995b32216b3876bf395c3be843147d1f1eee404bc6c958d7534ee335e48d`.
- Formal/document source-set SHA256:
  `00f8cb856ed4ee8cc2212a8561bd0ba0de33debf3053b99dc32d4c8e5b7e3c59`.
  `SOURCE_MANIFEST.json` identifies every constituent source digest.
- 14 new theories; 252 proof statements including helper lemmas.
- Fresh full proof and PDF builds passed with exit status zero in two
  independently initialized Isabelle user-state directories:
  1. The exact monorepo parent sources from commit
     `19e0a78dd218264540a7bc8c3f96fbddc730ffc2`.
  2. A standalone source-only package using the exact pinned public AFP
     dependency documented in `vendor/PROVENANCE.md` of that package.
- Both runs rebuilt the parent metatheory and the new entry, including both
  PDF documents. No prior custom session heap supplied the new proofs.
- The new entry's formal/document sources are byte-identical in both builds.
  All 17 monorepo parent source files were checked against their remote Git
  blob hashes. The public dependency's source hashes were separately checked.

## Review and trust

Separate automated read-only mathematical and trust reviews covered the
transport indices, uniform displayed-method assumptions, recursive and mixed
fold constructions, endpoint interpretation, substitution, admitted and
contextual path equations, examples, and scope documentation. Final
substitution-example typing corollaries were additionally inspected and built.
This is not a claim of external human peer review or AFP acceptance.

The in-session `DHIT_Audit` rejects oracle dependencies in selected headline
results. Static inspection of the new and imported metatheory source found
no admitted proofs, new axiomatization, unsafe oracle declarations, skipped
proof mechanism, quick-and-dirty setting, or code-printing override.
`TRUST_AND_SCOPE.md` explains explicit locale assumptions and intentional
out-of-domain uses of HOL `undefined`.

A bounded Mirabelle/Sledgehammer pass over the section-classification assembly
made five calls: two succeeded and three timed out. The existing structured
proofs were retained because the suggested variants were not clearer. A
prover timeout is not a failure of the Isabelle proofs, which passed the full
builds above.

A final bounded pass over the mixed contextual-eliminator assembly made two
calls and both succeeded. The existing short structured proof was retained.
The final 73-page PDF has embedded fonts and passed an all-page text-boundary
check and representative visual inspection, including the scope and references.

## Scope of the verification

This verifies the stated semantic dependent layer and its explicit hypotheses.
It does not establish a general syntactic dependent calculus, arbitrary HIT
semantics, higher interchange, or transferred normalization. No AFP, journal,
registry submission or repository CI run is claimed by this record.
