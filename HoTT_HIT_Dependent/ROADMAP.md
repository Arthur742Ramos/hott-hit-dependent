# Established scope and next mathematical targets

This release constructs dependent folds over the imported recursive and mixed
external-parameter syntax, proves whole displayed/contextual algebra
substitution, constructs indexed path quotients with all-fiber transport,
and derives endpoint functoriality and local-to-global canonical naturality
from explicit interchange laws. The constructed fold descends to the combined
quotient under uniform contextual displayed-method laws. See `VERIFICATION.md`
for the exact checked snapshot, not just the existence of a theorem filename.

## Next targets, in order

1. **Quotient-level substitution.** Extend the existing whole-algebra pullback
   to prove that substitution preserves the new interchange/naturality
   presentation and its quotient action. This is not already implied by the
   current substitution theorem.
2. **Typed universal property.** Restrict objects to the constructor grammar,
   define the appropriate algebras and morphisms, and prove the intended
   universal property. Structural fold uniqueness is not homotopy-initiality.
   Assess an endpoint-tagged Category3 or Catoids wrapper rather than claiming
   category-library interoperability without an interpretation.
3. **Weaker coherence hypotheses.** Replace total-function slot independence
   by suitably fiber-restricted laws where possible, preserving contextual
   stability of imposed equations. Current hypotheses are sufficient, not a
   necessary characterization of all coherent motives.
4. **Varying parameters and richer signatures.** Add parameter-path actions.
   Same-sort `Par h` requires a supplied section or a different discipline;
   current argument admissibility excludes those instances.
5. **Separate dependent object calculus.** Specify dependent contexts,
   binders, substitution, conversion and computation, then prove its typing
   and subject-reduction results. This semantic development does not itself
   extend the imported nondependent object language.
6. **Higher semantics.** Groupoid-valued motives, higher cells, universes,
   univalence and Kan operations require additional coherence definitions.

Normalization and decidable equality are outside this expansion. The existing
inverse-cancellation measure and old nondependent calculus do not establish
either property for the enlarged presentation.

## Before any AFP submission

The official mandatory lint pass is complete; see `LINT.md` for its scope
and the reviewed default advisories. Review the exact candidate, metadata, dependency/reuse decisions and
maintainer commitment with the authors. Obtain authorization for submission.
AFP acceptance remains an editorial and refereeing decision, not a
consequence of a successful build or an automated review.
