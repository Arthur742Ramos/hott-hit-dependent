# Dependent families and displayed algebras over structural HIT syntax

This Isabelle/HOL development extends the mathematics of the published
`HoTT_HIT_Metatheory`. It imports the original signatures, terms, endpoints,
typing and substitution; it neither changes that calculus nor extends its
executable checker.

See [VERIFICATION.md](VERIFICATION.md) and `SOURCE_MANIFEST.json` for the
exact checked source, toolchain, review and document record. No AFP submission
or acceptance is claimed.

## Mathematical results

### Dependent families and constructed sections

Fibers are subsets of a common HOL carrier and can vary with a base term.
Typed admitted paths act by bijections between fibers. The admitted edge set
can be empty. Generator boundary coherence extends to all admitted paths;
for a connected graph with chosen routes, sections are classified by the
root-fiber elements fixed by generator monodromy. Dependent sums and
normalized dependent products support genuinely second-indexed families
`G x a`, with computation and transport laws.

Displayed point methods construct recursive sections on the original
constructor-tree grammar. Typing, point computation, uniqueness and endpoint
interpretation are proved. The mixed-argument version supplies induction
hypotheses only at `Rec` positions; `Par j` arguments are supplied opaque
terms, with `j != h` for the HIT being eliminated. Uniform boundary methods
quantify arbitrary correctly typed induction hypotheses, not only the values
of the finished fold.

Constructor contexts may change recursive slots while surrounding parameters
remain fixed. Given contextual transport and uniform local method naturality,
the constructed section is coherent under those contextual paths. Whole
mixed displayed-HIT algebras, including their path-method obligations, pull
back under the original term substitution. Contextual algebras also pull back,
with substituted surrounding terms and context-indexed transport. Source
argument/tree admissibility is retained explicitly; it is not inferred
backwards from well-formed substituted terms.

### Path equations and actual quotients

A typed presentation closes specified path equations under symmetry,
transitivity, composition, reversal and inverse cancellation. Its hom sets
are actual sets of equivalence classes. Identity, composition and inverse
operations are defined and proved lawful. Transport is defined on these
classes and is independent of the chosen representative, provided every
specified equation is respected on **all elements of its source fiber**.
Maps sending generating edges to typed paths induce maps of these hom-set
quotients when they preserve the specified equations.

These are indexed hom sets, not a globally tagged arrow datatype. Identity
classes at different objects can have the same underlying set. Constructed
fold descent is restricted to valid constructor trees; it does not assert a
global dependent section on every raw `tm`.

### Interchange and original path-constructor naturality

The presentation includes independent recursive-slot interchange under valid
outer constructor contexts. Signed-generator and arbitrary two-path grid
interchange are derived. A sufficient transport interface requires equality
of the relevant total slot-action functions when the other slot endpoint
changes, plus commutation on all elements of the appropriate source fiber.
These are explicit, strong sufficient hypotheses, not a characterization of
all possible coherent families.

The original `EArg`/`ECon` endpoint syntax acts on typed tuples of argument
paths. The canonical edge graph uses actual pairs `(constructor, arguments)`,
so changed constructor arguments have their own generating instances.
Naturality squares for those original path constructors are typed, and local
all-fiber squares extend along composed and reversed paths in a supplied
argument graph.

`Coherent_Signature` combines shell-closed interchange and canonical
naturality cells. The endpoint action preserves identity, composition and
inverses modulo interchange. Its elementary serialization is equivalent to
the direct action of the original endpoint expression.

### Examples and separating results

Verified examples include a Boolean twisted loop with no section, genuinely
varying endpoint fibers, and an infinite-fiber binary-constructor example
with two free integer coordinates. The latter verifies interchange on all
fiber elements, not merely on the constructed section.

A counterexample has coherent displayed point methods and a preserved
selected section but noncommuting transports on another fiber element. It
shows why fold coherence cannot replace all-fiber relation compatibility and
why interchange adds equations beyond inverse cancellation.

The separately verified count-affine model has infinite fibers and a concrete
recursive-generator naturality square with arbitrary residual integer values.
Its transport depends only on endpoints: it respects every parallel equation,
so it witnesses consistency rather than faithfulness of the chosen presentation.

### Local-to-global coherence

Within the stated sufficient interchange-family interface, compatibility
with all canonical tuple naturality cells is equivalent to positive
single-recursive-slot naturality. Both conditions quantify every valid outer
constructor shell and every element of the source fiber. Elementary edges may
already be recursive constructor-context edges; no reduction to bare path
generators alone is claimed. The proof compares serialized elementary endpoint
images with direct endpoint motion modulo interchange. The same strong
slot-independence and commutation assumptions remain on both sides.

The specialization `constructed_coherent_elimination` assumes a
contextual displayed algebra with the same signature, carriers, motive,
constructor methods and transport actions. It descends the recursively
constructed fold to the derived combined coherence quotient and proves the
target fold lies in its fiber, starting from a term in the constructor
grammar. It assumes no pre-existing global section.

## Deliberate limits

This is a set-valued semantic layer, not a new syntactic dependent type theory
or a general model of higher inductive types. There is no claimed universe,
univalence, Kan structure, groupoid-valued motive, full typed universal
property, homotopy-initiality theorem, or equality completeness for the old
calculus. External parameter values do not vary along contextual paths.

Inverse cancellation terminates, but no normalizer or decidable equality for
the enlarged path presentation is claimed. No dependent normalization theorem
is inherited from the old nondependent calculus. Higher coherence beyond the
specified equations is not inferred automatically.

## Build and verification

Target: **Isabelle2026**. Supply the published `HoTT_HIT_Metatheory` session
from a separate official AFP checkout. Set `AFP` to that checkout root:

```sh
isabelle build -d "$AFP/thys" -D . \
  -o threads=2 -o document_build=pdflatex HoTT_HIT_Dependent
```

The session includes every theory and its headline oracle-dependency audit.
The verification record identifies the full proof/PDF builds and source hashes.
The official `afp_mandatory` linter bundle passes all 30 theories with zero
findings. The default bundle retains 19 independently reviewed advisories.
See `LINT.md` for exact rules/results and `AFP_PREPARATION.md` for remaining
author and submission-readiness decisions.

## Attribution and related work

Arthur Freitas Ramos, David Barros Hulak, and Ruy de Queiroz. This is a scoped
formalization and integration of established mathematics, not a claim to have
invented dependent elimination, monodromy, or category theory.

Primary references include the HoTT book, Hofmann--Streicher, Sojakova,
Kaposi--Kovacs, Dybjer--Moeneclaey and Veltri--van der Weide. Related established
AFP infrastructure includes Eugene Stark's [Category3](https://isa-afp.org/entries/Category3.html)
(2016) and Georg Struth's [Catoids](https://isa-afp.org/entries/Catoids.html)
(2023). They are related work, **not imported or reused dependencies** of this
entry. The actual dependency is the published structural HIT metatheory and
its Isabelle/HOL base.
