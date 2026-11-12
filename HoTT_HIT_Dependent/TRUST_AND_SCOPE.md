# Trust boundary and mathematical scope

The development uses Isabelle/HOL's ordinary foundational logic and library.
It introduces no new axiomatization, proof oracle, admitted proof, or
`quick_and_dirty` setting. An in-session ML audit checks oracle dependencies
of selected headline theorems. That audit inspects existing proofs; it does
not construct proofs through an alternative trusted path.

Locale assumptions are not hidden axioms. They are explicit theorem
hypotheses specifying fiber membership, inverse transport, displayed point
methods, uniform boundary methods, and local constructor naturality.
Examples instantiate these hypotheses, including nonconstant fibers and
nonidentity transport. The Boolean twisted-loop example also demonstrates
that a section need not exist.

HOL's `undefined` appears intentionally in two roles:

- Structural folds outside the constructor-tree grammar. Their induction and
  typing theorems are restricted to the proved grammar. Parameter induction
  hypotheses are masked at opaque parameter positions.
- Dependent functions outside their source fiber. Normalizing these values
  makes the inverse-transport law literal function equality. No off-domain
  value is asserted to inhabit a fiber.

Neither use supplies a missing proof or asserts a value in an empty type.

## Proven layer versus future goals

This is an external set-valued dependent semantic layer linked to the
published structural HIT syntax. It is not a new syntactic dependent type
theory and does not establish a general model of all higher inductive types.
In particular, no universe, univalence, general groupoid-valued motive, Kan
operation, or higher coherence is introduced.

The point folds are constructed from methods, and uniqueness is proved on
the stated constructor grammar. Their boundary and contextual coherence
follow from local displayed-algebra data. These obligations cannot be omitted
for arbitrary methods. Equality descent concerns the explicitly presented
admitted path equations, not every equality of the old term calculus.

The old substitution theorem induces genuine semantic reindexing, but is not
by itself a substitution theorem for a new dependent lambda calculus.
Likewise, cancellation preservation and termination are results about the
path presentation. Old nondependent strong normalization is not transferred.

The source theorem statements, not an informal summary, determine the exact
scope of each result. No AFP submission, acceptance, or journal/registry
publication is claimed for this new entry.
