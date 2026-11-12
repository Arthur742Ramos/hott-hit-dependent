# Official Isabelle linter record

## Tool and exact scope

The [linter linked by the AFP submission guidelines](https://github.com/isabelle-prover/isabelle-linter)
was installed as the standalone CLI component in an isolated Isabelle user
configuration. The shared Isabelle installation and its global settings were
not changed. Version: **Isabelle2026-v1.0.0**, commit
`146d9fc0bbd304dd6f15fdb607331f7d81e92723`.
Every downloaded source blob was checked against that official Git tree.

Isabelle2026 was used throughout. The exact final formal/document source-set
SHA256 is `bbe74d0f6c3d17973d7e9913309989c39e42c082f4d330cfb3271f11f2a6ee20`. Both runs processed all **30 proper theories** of
`HoTT_HIT_Dependent`; no missing-theory diagnostic was present. The parent
metatheory was built as a dependency, not included in these lint counts.
No rules were disabled and no source suppressions were added.

## Results

- **`afp_mandatory`: 0 errors, 0 warnings, exit 0.**
- **`default`: 0 errors, 19 advisory warnings, exit 0** with the failure
  threshold set to `error`. This is not a warning-free default-bundle result.
- Remaining advisories: `complex_method` 7, `tactic_proofs` 7,
  `auto_structural_composition` 5.

The mandatory bundle enabled `bad_style_command`, `counter_example_finder`,
`global_attribute_on_unnamed_lemma`, `proof_finder`,
`simplifier_isar_initial_method`, `smt_oracle` and `unfinished_proof`.
The standalone package's `validation/isabelle2026-lint.json` records the
remaining advisory locations and the before/after totals.

## Corrections and advisory review

The initial mandatory run found one violation in `lift_path_composition`:
a simplifier was used in the initial method of a structured proof. Its explicit
normalization now belongs to the preceding `unfolding`; the proof begins with
`rule map_cong`. The same goals and pointwise argument are retained.

A default advisory also identified the temporary global simplifier-rule change
in `DHIT_Endpoint_Functor`. It is now confined to a lemma-local note and an
anonymous proof context inside the existing locale. Context exit restores the
imported simplifier state without a global change-and-restore pattern.
No mathematical definition, theorem statement or hypothesis was changed.

Every remaining advisory site was independently reviewed. The seven flagged
tactic uses operate on explicit source-bound or explicitly renamed variables,
not unstable Isabelle-generated names. The complex-method warnings concern
short map/list proofs, a length-guarded tuple decomposition and two focused
locale assemblies. The five auto-composition warnings are terminal
metis/linear-arithmetic closers with explicit fiber, typing or coordinate
hypotheses. These short checked proofs were retained rather than rewritten
solely to achieve zero nonmandatory warnings. This is an automated independent
review, not external human peer review.

## Reproduce

Register the official release's `linter_base` component in an isolated user
configuration, then run from the standalone repository root:

```sh
isabelle lint -d . -o threads=2 -o document_build=pdflatex \
  -o lint_bundles=afp_mandatory -f error -r json -O mandatory.json \
  HoTT_HIT_Dependent
isabelle lint -d . -o threads=2 -o document_build=pdflatex \
  -o lint_bundles=default -f error -r json -O advisory.json \
  HoTT_HIT_Dependent
```

A mandatory-bundle pass covers the implemented rules, not every AFP guideline,
mathematical suitability or acceptance. Author readiness, metadata/maintainer
commitments and final submission authorization remain separate. No AFP upload,
editor contact or registry submission was performed.
