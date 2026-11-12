# AFP-oriented preparation, not submission

## Status and candid suitability

This is a candidate mathematical entry built on `HoTT_HIT_Metatheory`, not an
accepted or submitted AFP entry. Its substance includes constructed displayed
sections, whole-algebra substitution, actual path quotients, all-fiber descent,
interchange and original signature integration, with separating examples.
These results give a concrete basis for editorial consideration, but neither
size nor a successful Isabelle build guarantees AFP suitability or acceptance.
The general mathematics is established; claims should concern the scoped
formalization and integration, not invention of dependent elimination.

The exact source manifest, proof/document commands and review record are in
`VERIFICATION.md`. The remaining submission gates are listed below; a source
release and reproducibility package are not an AFP submission.

## Dependency and related-library assessment

The actual parent is the published `HoTT_HIT_Metatheory`; imports must use that
entry rather than duplicate its source inside this entry. Preserve the pinned
dependency provenance in any separate reproducibility package.

A bounded read-only interface assessment examined the official browser theories
[Category3/FreeCategory](https://isa-afp.org/browser_info/current/AFP/Category3/FreeCategory.html)
and [Catoids/Catoid](https://isa-afp.org/browser_info/current/AFP/Catoids/Catoid.html).
This was not an exhaustive search of either entry.

Category3's graph interface has explicit object/arrow sets and endpoint maps.
Its free category packages paths into endpoint-tagged arrows through
`concrete_category`; this is directly relevant infrastructure, not merely a
similar name. Our raw signed paths could be translated to it, but inverse
cancellation, the selected generating equations and all-fiber dependent action
descent would still require proofs. The current endpoint-indexed quotient
classes are not that tagged arrow representation. A future wrapper using
`concrete_category` is a plausible reuse route; no mathematical incompatibility
has been found, and no such wrapper has been verified. Retaining the current
small path interface avoids an unproved representation migration in this
package, not because Category3 is incapable of expressing its result.

Catoid's inspected interface uses set-valued composition on a single carrier,
with source and target also in that carrier, then associative source/target
algebraic laws. Reusing it would require a suitable carrier of endpoint-tagged
valid quotient arrows and an interpretation of these operations. Our hom-class
sets can overlap across endpoint pairs, so they cannot simply be used as that
carrier without additional representation work. The inspected interface does
not itself discharge the signature-specific uniform displayed-method or
all-fiber equation hypotheses.

Neither library is imported or reused. The bounded comparison supports the
current interface choice, but does not certify absence of a useful quotient or
action interface elsewhere in these libraries. Before claiming broad category
interoperability, build and verify the wrapper rather than merely cite it.

## Official guideline checklist

Reference: https://isa-afp.org/submission/ . The following requirements guide this preparation;
manual review is not an official linter pass.

- No `sorry`, `back`, live `sledgehammer` proof command or `smt_oracle`.
- No unstable generated-name instantiations; inspect proofs, not just tokens.
- Respect prescribed `apply`-script indentation and named-attribute conventions.
- Session timeout must be divisible by 300. The final `1800` timeout satisfies
  that arithmetic requirement.
- One intended AFP session and its PDF, with correct ROOT/document layout.
- Appropriate primary citations and complete, correctly rendered references.
- Official `afp_mandatory` lint now passes all 29 theories with zero findings.
  The default bundle reports 8 independently reviewed advisories, not errors.
  See `LINT.md` for the pinned official release, rules and exact source scope.
  This does not certify every guideline or editorial requirement.

A keyword scan should distinguish actual proof commands from discussion in
comments or documentation. It cannot validate generated instantiations,
attribute discipline, indentation, mathematical scope or proof robustness.
The exact tool and rule sets are recorded in `LINT.md`.

## Review response completed

- The proof document now introduces the informal principal theorem, elementary
  and tuple naturality, shared sufficient interchange laws, and practical use.
- `DEPENDENCY_AUDIT.md` identifies the exact principal equivalence, quotient
  descent, representative-independence and example facts. The sole ML block
  inspects transitive proof-oracle dependencies; it does not produce proofs or
  enumerate all logical axioms.
- A focused combined sign-flip example supplies genuine path-sensitive recursive
  naturality and binary interchange, with a valid nonidentity loop. Constant
  fibers, identical involutive slot actions, and the absence of faithfulness or
  a displayed-fold instance are explicit.
- Full Isabelle2026 proof/document/browser and minimal archive builds pass
  against the external official AFP snapshot. Mandatory lint remains clean;
  the eight previously reviewed default advisories are unchanged.
- Weakening total-function independence, full universal properties and
  normalization are not prerequisites imposed on this accurately scoped entry.

## Remaining submission gates

The official mandatory lint gate is complete for this candidate; rerun it
after future source changes. Remaining gates are:

1. Review the candidate's mathematical scope, organization, related-library
   assessment, bibliographic metadata and maintainer commitment with the
   authors. Automated independent source review is not external human peer
   review or a prediction of acceptance.
2. Obtain explicit authorization before uploading or submitting to AFP or
   contacting editors. The repository draft's readiness/merge decision remains
   separate from this preparation work.

The reproducibility ZIP does not contain the parent entry. It imports the
already-published dependency from a separate official AFP checkout; the
repository-level dependency note and checksum list pin the tested snapshot.
An eventual AFP upload should still contain only the new entry's allowed
source files in one `HoTT_HIT_Dependent/` top-level directory, not repository
validation records or a copy of AFP.

No AFP upload, draft creation, editor notification, journal submission or
registry submission has been performed.
