# Trust boundary and mathematical scope

Read this scope statement together with `VERIFICATION.md` and the exact
source manifest. Earlier milestone receipts describe their own snapshots,
not later source revisions.

## Proof trust

The development uses ordinary Isabelle/HOL definitions, inductive relations,
locales and kernel-checked proofs. No new axiomatization, admitted proof,
proof oracle or `quick_and_dirty` setting is used. Source inspection and the
in-session audit are recorded for the checked snapshot. The in-session headline audit inspects theorem oracle dependencies;
it is not an alternative proof-producing extension or a substitute for
source inspection and the normal session build.

Locale laws are explicit theorem hypotheses. They specify fiber membership,
mutually inverse transport on admitted edges, method typing, uniform displayed
boundaries, contextual naturality and additional path-equation compatibility.
A conditional theorem does not establish that every signature or every choice
of methods satisfies those laws.

## Total HOL operations and their domains

`undefined` has two intentional roles: structural folds outside their proved
constructor grammar, and dependent functions outside their source fiber.
Opaque parameter positions have their induction hypotheses masked. Product
functions are normalized off-domain so inverse transport gives literal HOL
function equality. None of these definitions proves membership in an empty
fiber. Uses of list indexing, head/tail and option extraction are justified
by the arity, grammar, length and displayed-argument hypotheses of the relevant
theorems, not by interpreting arbitrary out-of-range values as valid data.

An abstract quotient operation selects a representative using HOL choice
(`SOME`). Genuine hom-set classes are proved nonempty and contain typed paths.
The operation is proved independent of that choice on the stated fiber.
This is not an executable representative-selection procedure, a normalizer,
or a decision procedure for path equality.

## Three levels that must not be conflated

1. **Constructed fold.** Local point methods define a recursive section on
   valid constructor trees. Uniform displayed boundaries and contextual
   method naturality establish coherence of that section.
2. **Whole family.** Transport descends through imposed path equations only
   when they act equally on every source-fiber element. The noncommuting
   counterexample shows that agreement on a selected section is insufficient.
3. **Quotient hom sets.** Classes are indexed by their endpoints. Operations
   and transport are restricted to membership in the corresponding hom set.
   These sets need not form a disjoint global arrow carrier. In the underlying
   raw-term graph, empty identity paths also exist at raw terms outside the
   constructor grammar; the fold-descent theorem retains its grammar premise.

## Strength of the coherence assumptions

The interchange interface deliberately uses strong sufficient laws. Its
slot-independence clauses are equalities of total action functions, not merely
agreements on one chosen fiber or on the image of a method. Commutation is
required on all values of the appropriate source fiber, uniformly under valid
outer shells. These hypotheses are not advertised as necessary or as the most
general possible dependent interchange interface.

Within the stated sufficient interchange-family interface, compatibility
with all canonical tuple naturality cells is equivalent to positive
single-recursive-slot naturality. Both conditions quantify every valid outer
constructor shell and every element of the source fiber. Elementary edges may
already be recursive constructor-context edges; no reduction to bare path
generators alone is claimed. The proof compares serialized elementary endpoint
images with direct endpoint motion modulo interchange. The same strong
slot-independence and commutation assumptions remain on both sides.

## Semantic and syntactic boundaries

Fibers are sets, not arbitrary groupoids. The entry imports the old syntax and
substitution but does not introduce dependent types into that object language.
The mixed grammar excludes same-sort `Par h`, and contextual holes occupy only
recursive slots; external parameter terms remain fixed along such paths.
External arity is enforced for path constructors by argument admissibility: a
path constructor containing a same-sort `Par h` slot has no admitted instances
in this fragment. Graph-path typing means that endpoints and admitted edges
match. Typing in the imported object calculus additionally requires the stated
signature and external-parameter typing premises; arbitrary supplied parameter
sets are not silently assumed to contain well-typed terms.
Substitution changes permitted parameter carriers, motives, methods and
context actions together. Original source admissibility remains explicit
because substitution need not reflect the grammar.

The results do not give a full typed universal property of a HIT quotient,
homotopy-initiality, a general universe, univalence, Kan operations or arbitrary
higher coherence. Termination of inverse cancellation says nothing by itself
about normalization or decidable equality after interchange and naturality
relations are imposed. Old nondependent normalization is not transferred.

## Publication status

AFP-oriented preparation is not submission or acceptance. No editor contact,
AFP upload, journal submission or registry publication is part of this task.
The final theorem statements and audited dependency graph, rather than an
informal summary or theorem count, determine the scope of the deliverable.

## Constructed-fold specialization

The final specialization `constructed_coherent_elimination` assumes a
contextual displayed algebra with the same signature, carriers, motive,
constructor methods and transport actions. It descends the recursively
constructed fold to the derived combined coherence quotient and proves the
target fold lies in its fiber, starting from a term in the constructor
grammar. It assumes no pre-existing global section. This specialization has passed its exact proof check and independent source
review.
