# Theory organization and cleanup

This pre-submission cleanup follows the monorepo `AGENTS.md` principles:
maintainable mathematical arguments, explicit reuse of published dependencies,
focused simplification, and preservation of definitions and theorem hypotheses.
It is not a rewrite of the previously accepted parent entry.

## Coherent modules, not a minimum file count

The consolidation reduced the entry from 30 theories to 28:

- `DHIT_Dependent_Transport` is consolidated into `DHIT_Type_Formers`.
  Transport in the second-indexed family belongs with the dependent sum and
  product constructions in the same `dependent_graph_family` locale.
- `DHIT_Argument_Projection` is consolidated into `DHIT_Argument_Graph`.
  Exact coordinate recovery belongs with the elementary serialization it
  analyzes. A separate section marks the projection interface.

A later focused review response adds the substantive combined path-sensitive
example as one separate theory, bringing the current total to 29. It is not an
auxiliary fragment split out merely for proof-task convenience.

Import the destination theory in place of either removed theory. Locale-qualified
facts such as `dependent_graph_family.dependent_transport_type` retain their
names. Unqualified projection API names are unchanged; theory-qualified global
names formerly prefixed by `DHIT_Argument_Projection` now use
`DHIT_Argument_Graph`. No compatibility wrapper theories are retained solely to
preserve the earlier development-stage file split.

`DHIT_Generator_Naturality` now imports only `DHIT_Admissible_Paths`.
`DHIT_Quotient_Functor` depends only on generic path, quotient and reindexing
interfaces. Its constructor-grammar specialization
`contextual_parameter_algebra.constructed_section_quotient_descent` has moved
to `DHIT_Coherence_From_Local`, retaining its locale-qualified name. HIT-specific
endpoint theories import their syntax/algebra requirements explicitly.
The audit imports six leaf modules that cover the complete dependency graph,
rather than repeating seventeen transitive dependencies. All 97 selected
headline references remain in the audit.

The recursive/mixed algebra distinction, generic quotient interface, elementary
naturality interface, final local/global assembly and examples remain separate.
They expose different assumptions or reusable results; merging them merely to
reduce the file count would obscure those boundaries.

## Selective proof cleanup

Seven proof sites were revised without changing their statements or assumptions:

- Three path-image lemmas use the function's own induction rule instead of
  repeated list induction, temporary variable renaming and signed case tactics.
- `lift_path_identity` gives the extensional dart argument an explicit Isar binder.
- `parameter_tree_typed` exposes the argument index and its bound directly.
- `ih_mask_append` uses a short structured induction.
- `coordinate_image_lift` names the list cases and separates the signed step.

Structured endpoint/grid arguments, fiber side conditions and named witnesses
were retained. The remaining default-linter advisories are reviewed proof-style
choices, not suppressed rules or admitted obligations. The verification and lint
records report the exact checked results rather than treating advisory removal
as the objective.

## Documentation and package hygiene

The abstract now leads with the local/global theorem and states the uniform
laws needed for constructed-fold descent. The README includes a reading guide.
Twelve unused bibliography entries were removed, the original AFP dependency's
citation was corrected to its official metadata, and Dybjer--Moeneclaey's volume
and pages were checked. The stale reference to a vendored dependency license
was removed; the entry includes the BSD-3-Clause license when staged separately.
The parent remains external and pinned, not copied or redefined.

Full proof/document checks, the selected-fact oracle audit, mandatory and default
lint, focused proof-search review, and independent source review are recorded in
`VERIFICATION.md`. These technical checks prepare an author-review candidate;
they do not constitute AFP submission, editorial approval or acceptance.
