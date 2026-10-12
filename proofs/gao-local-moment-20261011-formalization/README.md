# All-height density extension

This increment formalizes the height split in
[`PlainUnmarkedDensity.tex`](../gao-local-moment-20261011-v3/PlainUnmarkedDensity.tex),
lines 209–216. The module's generic scale `Y` corresponds to the manuscript's
scale `U`; applying it to `U = K Y` requires rescaling the counting function.

The three declarations in [`AllHeightDensity.lean`](LocalMoment/AllHeightDensity.lean)
prove that a bounded-height estimate `N(p,Y,T) ≤ C Y^ρ(p)` for `T ≤ Y^τ`
and a lattice-count estimate `N(p,Y,T) ≤ D Y` imply
`N(p,Y,T) ≤ max(C,D) (1+T)^J Y^ρ(p)` for every `T ≥ 0`, assuming
`ρ(p) ≥ 0` and `τ J ≥ 1`. The scale threshold is chosen before all parameters
`p` and heights `T`. Both an explicit-threshold statement and an eventual
statement preserve this quantifier order.

The bounded-height estimate and lattice-count estimate are explicit premises.
Their application to the manuscript's actual row family, the bounded-scale
completion, the full weighted source estimate and the all-family continuation
remain part of the outstanding proof. The proposed bound has the research
candidate status described in the
[author's clarification](../gao-local-moment-20261011-status-clarification/README.md).

The three declarations compile with Lean **4.34.1** (compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`) and cached Mathlib dependencies at
commit **`d13f23b723b8a846827a245b89c10fc7d3f11612`**. The captured
[axiom audit](evidence/AllHeightDensity.log) lists `propext`, `Classical.choice`
and `Quot.sound` for every declaration. This validation covers the new module
using already-built dependencies. Independent dependency replay and the
repository's complete result verification remain outstanding.

To reproduce, use the pinned Mathlib checkout with its dependencies built for
the specified compiler. From that checkout, run:

```sh
cd /path/to/mathlib
/path/to/lean-4.34.1/bin/lake env /path/to/lean-4.34.1/bin/lean \
  /path/to/QuasiRiemannTracker/proofs/gao-local-moment-20261011-formalization/LocalMoment/AllHeightDensity.lean
```

The command compiles the source and prints all three axiom sets. License and
attribution are recorded in [NOTICE.md](NOTICE.md) and [LICENSE](LICENSE).
