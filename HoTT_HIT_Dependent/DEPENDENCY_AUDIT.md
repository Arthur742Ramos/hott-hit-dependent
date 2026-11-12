# What the proof-dependency audit checks

`DHIT_Audit.thy` is included in the session ROOT. Its only ML block looks up
existing theorems through Isabelle theorem antiquotations, collects the selected
results, calls `Thm_Deps.all_oracles`, and raises an error if that collection is
nonempty. It does not produce a theorem, add an axiom, register an oracle, or
replace the ordinary Isabelle proof checker.

## Principal results explicitly selected

| Claim | Checked theorem |
| --- | --- |
| Main elementary/tuple equivalence | `local_global_signature_coherence` |
| Constructed fold on the combined quotient | `locally_natural_signature_family.constructed_coherent_elimination` |
| Constructed fold on a supplied compatible quotient | `contextual_parameter_algebra.constructed_section_quotient_descent` |
| All-fiber transport on the combined presentation | `coherent_signature_family.all_fiber_coherent_descent` |
| Equal presented paths act equally on every typed value | `quotient_family.presented_transport` |
| Quotient action agrees with the chosen typed path class | `quotient_family.quotient_transport_class` |
| Quotient action agrees with any member of the same hom class | `quotient_family.quotient_transport_member` |

The principal equivalence is exported outside a locale. Its two locale predicates
both contain the signature and sufficient interchange hypotheses. The equivalence
changes elementary naturality into tuple naturality; it does not discharge the
shared hypotheses. Constructed descent additionally assumes the uniform contextual
displayed algebra, membership in a genuine endpoint-indexed quotient hom set,
and a source term in the admitted `parameter_tree` grammar. In that final
contextual interface, `base_boundary` asserts coherence of the already recursively
defined fold on base generators, whereas `point_naturality` ranges over arbitrary
typed recursive values. The earlier displayed-HIT interface's arbitrary-IH
endpoint boundary methods are a sufficient route to the base condition, not an
additional premise silently present in the final theorem.

## Examples and separating results explicitly selected

- `recursive_generator_naturality_presented` and
  `recursive_naturality_all_residuals`: the actual recursive collapse signature's
  naturality square, in the count-affine family. Its action is endpoint-determined.
- `vector_binary_square_all_values` and `vector_constructed_section_and_square`:
  the two-coordinate model's all-fiber interchange and constructed-section result.
- `binary_square_not_cancellation_equal` and `bad_context_not_relation_compatible`:
  cancellation alone does not identify the interchange square, and coherence of
  a selected section does not imply the required all-fiber compatibility.
- The combined sign-flip example is selected through `twist_coherent_model`,
  `twist_loop_typed`, `twist_loop_action`, `twist_loop_not_trivial`,
  `twist_recursive_naturality_cell`, both `twist_recursive_naturality_action`
  conclusions, `twist_binary_interchange_cell`, both
  `twist_binary_interchange_action` conclusions and
  `twist_binary_distinct_nonidentity`. These certify a valid nonidentity loop
  and distinct two-slot orderings in one coherent model, not faithfulness or
  a displayed-fold interpretation of that model.
- The list also includes `twisted_loop_has_no_section`, the connected-section
  classification, constructed induction and substitution, endpoint functoriality,
  serialization and the quotient's bijection/composition/inverse laws.

The complete authoritative list is the ML value `dependent_headlines` in
`DHIT_Audit.thy`, currently containing 111 selected theorem references. The three
representative-independence facts above were added explicitly during review;
they are existing proved results, not new assumptions.

## Transitive coverage and its limits

In the pinned Isabelle2026 source, `src/Pure/thm_deps.ML` implements
`all_oracles` by visiting the selected proof bodies and their referenced theorem
nodes, joining pending proof bodies, tracking visited theorem identifiers, and
collecting recorded oracle dependencies. Thus the check is transitive through
the proof dependencies of the selected facts, not just a scan of their final
proof commands. The library's skipped-proof detection uses the same oracle
information.

An empty result does **not** enumerate all theorems in the entry, enumerate its
logical axioms, remove locale assumptions, or prove the mathematical suitability
of a definition. Ordinary Isabelle/HOL foundations, classical reasoning and HOL
choice remain in use. Choice of a quotient representative is justified only on
proved nonempty classes; out-of-domain total operations retain their documented
meaning. See `TRUST_AND_SCOPE.md`.

The complementary checks are the complete session proof/document build, the
mandatory linter, inspection for unfinished or prohibited proof mechanisms and
new axiomatizations, and independent review of the theorem statements and sole
ML block. Their exact source hashes and outcomes belong in `VERIFICATION.md`.
No individual check is presented as a substitute for the others.
