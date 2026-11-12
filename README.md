# Dependent families and displayed algebras for structural HIT syntax

Verified Isabelle2026 source by **Arthur Freitas Ramos, David Barros Hulak,
and Ruy de Queiroz**. This is a new mathematical extension of their published
`HoTT_HIT_Metatheory`, not an executable-checker continuation.

## Main results

- Constructed dependent folds on original point-constructor trees, first for
  recursive signatures and then for mixed external `Par`/`Rec` arities.
- Point computation and uniqueness; typed interpretation of original endpoint
  expressions; uniform boundary-method obligations for arbitrary typed IHs.
- Actual term-substitution naturality of the constructed fold and displayed
  algebras, with explicit substitution images of opaque parameter carriers
  and pulled-back methods.
- Constructor-path induction through recursive slots of both fragments,
  including admitted path/equality lifting and transport coherence.
- Varying set-valued fibers, dependent sums/products, inverse transport and
  dependent cancellation preservation, and a monodromy classification of
  connected dependent sections.
- Nontrivial recursive and list-deletion examples, with different endpoint
  fibers and nonidentity transport; a twisted Boolean loop has no section.

Read [the entry README](HoTT_HIT_Dependent/README.md) and
[trust/scope statement](HoTT_HIT_Dependent/TRUST_AND_SCOPE.md) for exact limits.
This is a set-valued dependent semantic layer, not a complete new syntactic
dependent type theory, an unrestricted model of HITs, or a transferred
normalization theorem. External parameters are fixed along contextual paths;
higher interchange and full quotient/computational-equality completeness are
not claimed. Contextual transport and local displayed naturality are explicit
algebra data, not automatic for arbitrary motives.

## Reproduce

Install **Isabelle2026** and a working LaTeX installation with pdfLaTeX, then:

```sh
isabelle build -D . -o document_build=pdflatex HoTT_HIT_Dependent
```

Both this entry and the pinned public dependency are included. No private
repository or external proof session is required. To inspect dependency hashes:

```sh
(cd vendor && sha256sum -c SHA256SUMS)
```

See `VERIFICATION.md` for the exact build and independent-review record.
The new source is BSD-3-Clause; the public AFP dependency retains its original
license and attribution under `vendor/`.

No AFP, journal or registry submission of this new entry is implied.
