# Dependent families and displayed algebras over structural HIT syntax

This new Isabelle entry expands the mathematics of `HoTT_HIT_Metatheory`.
It is not a checker extension, and does not change the old calculus.

## What is formalized

- Typed signed paths, endpoint preservation under inverse cancellation,
  terminating cancellation, and a typed path-equality presentation.
- Genuinely varying set-valued fibers and mutually inverse edge transport.
  Transport preserves fibers, is bijective, respects path equality, and
  satisfies inverse/composition laws.
- Generator boundary coherence iff coherence along every typed path.
- In a connected graph with chosen routes, a constructive bijection between
  sections and root-fiber elements fixed by generator monodromy. The extension
  is independent of the route used to reach a vertex.
- Dependent sums and normalized dependent products for second families
  `G x a`, including typing, beta/eta, and evaluation naturality.
- Actual imports of the old `tm`, `endpt`, `hsig`, `wt`, and `subst`.
  Original endpoint interpretation commutes with term substitution;
  substitution preserves selected well-typed constructor-instance graphs and
  induces pullback of dependent families.
- Actual term substitution preserves mixed constructor trees when opaque
  parameter carriers are mapped to their substitution images. The constructed
  fold and endpoint evaluation commute with substitution under explicitly
  pulled-back methods; displayed algebras pull back accordingly.
- Displayed point algebras construct structural dependent folds on original
  constructor terms, with typing, beta equations, uniqueness, and dependent
  endpoint interpretation. Boundary methods are uniform over arbitrary typed
  induction-hypothesis lists, not post-hoc checks of a finished fold.
- A mixed `Par`/`Rec` extension masks induction hypotheses at parameter
  positions, permits supplied external parameter terms, and retains the original
  arities and endpoints. Its first theorem restricts `Par j` to `j != h`.
- Constructor contexts through recursive slots, including mixed-parameter
  constructors, give genuine contextual generating edges. Local displayed point-method naturality yields fold
  coherence under these edges, composed/inverse paths, and admitted path
  cancellation. Edge-admissibility predicates include empty-edge graphs.

Examples distinguish real dependence and nontrivial monodromy: distinct
endpoint fibers, a twisted Boolean loop with no section, and second fibers
that depend on both the vertex and the first component.

## What is not claimed

This is a semantic dependent layer in Isabelle/HOL, not a new full dependent
lambda calculus. There is no universe, univalence, Kan structure, general
higher-dimensional HIT, or groupoid-valued motive. No normalization result is
inherited from the old nondependent calculus. Path-cancellation preservation
is not a dependent lambda-calculus subject-reduction theorem.

Constructor contexts may vary recursive arguments while external parameters
are held fixed. Paths varying external parameter values are not included.
Contextual transport is part of the motive's supplied algebra data;
local method naturality is a real obligation, not synthesized for arbitrary
families. We do not assert interchange, higher coherence, homotopy-initiality
of a full quotient HIT, or equality descent for the full old calculus. The
connected-family classification applies to a connected vertex type, not
silently to every raw `tm`.

A global section assumed in a coherence theorem is not a constructed HIT
eliminator. The monodromy classification and displayed folds are the separate
construction results. Boundary coherence and constructor naturality are
necessary local method obligations, not automatically true for arbitrary
methods. The old-term substitution theorem is not a substitution theorem for
a newly defined syntactic dependent lambda calculus.

## Build

Target: **Isabelle2026**. Supply the exact public `HoTT_HIT_Metatheory` source
as a session directory, then run:

```sh
isabelle build -d /path/to/HoTT_HIT_Metatheory -D . -o document_build=pdflatex HoTT_HIT_Dependent
```

Use `-o document=false` for a proof-only iteration. The verification record
will identify the final source hashes and build status. No AFP submission or
acceptance of this new entry is implied.

## Attribution and related work

Arthur Freitas Ramos, David Barros Hulak, and Ruy de Queiroz. This builds on
their published structural HIT metatheory. General dependent-family and
monodromy mathematics is established; the claimed deliverable is a scoped
formalization and integration, not a new foundational theory.

See the generated document bibliography for the HoTT book, Hofmann--Streicher,
Sojakova, Kaposi--Kovacs, and Veltri--van der Weide.
