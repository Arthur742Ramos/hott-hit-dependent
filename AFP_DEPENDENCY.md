# External AFP dependency

The repository and reproducibility ZIP contain **only the new dependent entry**,
not a vendored copy of `HoTT_HIT_Metatheory`. Supply that already-published parent
from a separate official Archive of Formal Proofs checkout. No global component
registration, private repository or custom prebuilt proof heap is required.

## Verified source pin

- Isabelle: **Isabelle2026**, distribution source ID `096842708b28`.
- Official AFP snapshot: **afp-2026-11-12**.
- Dated archive: https://isa-afp.org/release/afp-2026-11-12.tar.gz
- Archive SHA256:
  `7d1c36b42ce9ba65a0b38f576324038a2d682a44f36f3a8e53ce8a2dc3d97583`.
- Entry: https://isa-afp.org/entries/HoTT_HIT_Metatheory.html .
- Parent authors: Arthur Freitas Ramos, David Barros Hulak, and
  Ruy Jose Guerra Barretto de Queiroz.

The dated archive was downloaded and its bytes matched the independently
retrieved official `afp-current.tar.gz` on 2026-11-12. Its `thys/ROOTS` registers
`HoTT_HIT_Metatheory`. The 17 parent source/document files are pinned in
`AFP_DEPENDENCY_SHA256SUMS`; they match the previous vendored snapshot exactly.
The existing source imports are unchanged. The parent retains its AFP license
and attribution in the external checkout.

For reproducibility, obtain and unpack the verified archive **outside this
repository**. Check the whole archive before extracting it:

```sh
curl -fL https://isa-afp.org/release/afp-2026-11-12.tar.gz -o afp-2026-11-12.tar.gz &&
printf '%s  %s\n' \
  7d1c36b42ce9ba65a0b38f576324038a2d682a44f36f3a8e53ce8a2dc3d97583 \
  afp-2026-11-12.tar.gz | sha256sum -c - &&
tar -xzf afp-2026-11-12.tar.gz
```

Set `AFP` to the resulting `afp-2026-11-12` directory. Check its relevant files
from that directory:

```sh
(cd "$AFP" && sha256sum -c /absolute/path/to/hott-hit-dependent/AFP_DEPENDENCY_SHA256SUMS)
```

The `current` archive URL changes over time. Do not silently substitute a newer
snapshot for this recorded pin when reproducing these results. A different AFP
checkout may work, but needs its own verification. If the dated download is
unavailable, obtain the matching archive or files from official AFP history and
check the recorded hashes; the project does not automatically fetch a fallback.

## Session discovery

The project `ROOTS` lists only `HoTT_HIT_Dependent`. Its `ROOT` retains
`session HoTT_HIT_Dependent (AFP) = HoTT_HIT_Metatheory +` and the theories import
the parent's existing definitions. Add the **external** checkout's `thys`
directory with `-d "$AFP/thys"`, as in the top-level README. This discovers AFP
sessions without selecting the whole AFP for rebuilding: only the requested
entry and its required ancestors are built.

Earlier public commits and existing version history preserve the former bundled
package. The current source-only ZIP deliberately does not include the parent,
AFP tooling or the full AFP archive. This packaging change is not an AFP
submission or acceptance of the new entry.
