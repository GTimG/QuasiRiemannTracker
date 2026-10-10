# Build and verify

The source build instructions are in [reproduce/README.md](reproduce/README.md).
They pin ordinary Lean 4.34.1, the exact required dependency sources and their
compatibility patches. The bootstrap checks hashes and preserves a mismatching
existing dependency directory instead of resetting it.

The proof entrypoint is `formalization/Cycle25/Assembly/Final/Endpoint.lean`.
`reproduce/verify_source.py` checks the exact 3,224-module source closure.
The historical clean build freshly compiled the 301 Cycle25/reused-moment
modules; it reused the 2,923 pinned OpenAI modules and third-party libraries.
The portable recipe can rebuild those sources too. Its preparation and the
19 patched dependency modules were separately tested, as recorded in
`reproduce/portability-validation.json`.

[Verification.md](Verification.md) lists the seven mathematical statements
accepted by all three kernels, including the exact quartic boundary. Follow
[the independent-kernel recipe](evidence/multi-kernel/README.md) after building
the source. A successful source build and the independent comparison/kernel
check are separate checks.

To rerun the ordinary Lean endpoint audit after building, run from
`formalization/`:

```sh
elan run leanprover/lean4:v4.34.1 lake env lean ../evidence/ordinary-lean/Audit.lean
```

It writes declaration inventories under `Cycle25/Assembly/Final/` and fails
on a forbidden dependency. The original audit output is retained beside it.
The inventories can be regenerated and are omitted from the archive.

The paper source is in `manuscript/`. The rendered paper is published beside
the source archive under `public/proofs/cycle25-quartic-20261010/paper.pdf`
in the tracker repository. The same PDF is served on the author's site.
