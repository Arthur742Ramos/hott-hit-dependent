# Dependent families and coherent displayed algebras for structural HIT syntax

Isabelle2026 source by **Arthur Freitas Ramos, David Barros Hulak, and Ruy de
Queiroz**, extending their published `HoTT_HIT_Metatheory` through actual
signature, term, endpoint and substitution imports.

## Main mathematical results

- Constructed dependent folds for recursive and mixed external `Par`/`Rec`
  grammars, with point computation, uniqueness, endpoint interpretation and
  whole displayed/contextual algebra substitution.
- Actual indexed path quotients, lawful identity/composition/inverse and
  representative-independent transport on every fiber element.
- Constructor and original endpoint functoriality modulo interchange,
  including arbitrary signed path grids and elementary serialization.
- **Local-to-global coherence:** within the stated sufficient all-fiber
  interchange interface, positive single-recursive-slot naturality is
  equivalent to compatibility with all canonical tuple naturality cells,
  uniformly under valid outer constructor contexts.
- Descent of the recursively constructed fold to that combined quotient,
  assuming the uniform contextual displayed-method laws, not a supplied
  global section.
- Infinite varying-fiber examples and a finite counterexample showing that
  coherence of one section does not imply all-fiber interchange.

Read [the entry README](HoTT_HIT_Dependent/README.md),
[trust and scope](HoTT_HIT_Dependent/TRUST_AND_SCOPE.md), and
[AFP preparation assessment](HoTT_HIT_Dependent/AFP_PREPARATION.md).
This is a set-valued semantic extension, not a new dependent object calculus
or a general model of HITs. The interchange hypotheses are sufficient, not
necessary. External parameters remain fixed along contextual paths. A full
typed universal property, higher groupoid-valued motives, quotient-level
substitution, normalization and decidable equality remain outside this release.

## Reproduce

Install **Isabelle2026** and LaTeX with pdfLaTeX, then run:

```sh
isabelle build -D . -o threads=2 -o document_build=pdflatex HoTT_HIT_Dependent
```

For the AFP-style proof-outline document and browser information:

```sh
isabelle build -D . -o threads=2 -o document_build=pdflatex \
  -o browser_info -o document=pdf \
  -o "document_variants=document:outline=/proof,/ML" HoTT_HIT_Dependent
```

The exact pinned public dependency is included; no private repository or
custom prebuilt proof session is required. Check dependency hashes with:

```sh
(cd vendor && sha256sum -c SHA256SUMS)
```

See [VERIFICATION.md](VERIFICATION.md) for exact checked sources, commands,
review scope and remaining readiness gates. The official AFP linter has not
been run. No AFP, journal or registry submission has been performed.

The new source uses BSD-3-Clause. The public AFP dependency retains its
original license and attribution under `vendor/`.
