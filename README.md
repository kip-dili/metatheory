# metatheory

Mechanized proofs in Rocq about core Kip: static semantics, dynamic semantics, type soundness, and compile-time overload elaboration.

## Building

This project expects Rocq 9.0 or newer. The opam metadata is in `rocq-kip-core.opam`.

To build everything:

```sh
make
```

The top-level `Makefile` runs
`rocq makefile` on `_CoqProject` and
then builds the generated `Makefile.coq`.

To remove generated build artifacts:

```sh
make clean
```

## Repository layout

The main proofs live under `theories/`:

- `Syntax.v`: shared syntax, contexts, substitutions, case alignment, and other foundational definitions.
- `Static.v`: the declarative static semantics, including well-formedness, pattern judgments, semantic values, and expression typing.
- `StaticFacts.v`: lemmas and proof automation for the static semantics.
- `Dynamic.v`: the dynamic semantics, including executable environments, values, and small-step evaluation.
- `DynamicFacts.v`: lemmas connecting the dynamic semantics to the static semantics.
- `Soundness.v`: the main progress and preservation proofs.
- `Elaboration.v`: a separate elaboration layer for overload resolution and its connection back to the split core development.

Other top-level files:

- `_CoqProject`: logical path and file order for the Rocq build.
- `Makefile`: convenience wrapper around the generated `Makefile.coq`.
- `rocq-kip-core.opam`: opam package metadata and dependency bounds.

Building produces Rocq artifacts such as `.vo`, `.vos`, `.vok`, and `.glob` files alongside the source files in `theories/`.
