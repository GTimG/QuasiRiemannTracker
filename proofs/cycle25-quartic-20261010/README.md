# The quartic QRH boundary

Hailey Collet · HaileyCollet@gmail.com · Apache-2.0  
Proof ID: `cycle25-quartic-20261010` · Catalogue status: **verification-pending**

This submission proves nonvanishing in the open half-plane `Re(s) > b₀`, where

\[
b_0=\frac{11}{12}-\frac{\ell_0}{4},\qquad
927\ell_0^4-3135\ell_0^3+2433\ell_0^2+275\ell_0-100=0,
\]

and `ℓ₀` is the unique root in `[1/6, 1/5]`. Lean also certifies the tighter isolating interval `0.16712007850680 < ℓ₀ < 0.16712007850682`. The rational catalogue bound is

\[
\theta=\frac{683505193}{781250000}=0.87488664704,
\qquad 0<\theta-b_0<4\times10^{-14}.
\]

The theorem covers Mathlib's Riemann zeta function, every complex Dirichlet character of every positive modulus, and OpenAI's finite-order Hecke family over `ℚ(ζ₃)`. The Dirichlet and Hecke statements retain their principal-character pole exceptions. The zeta endpoint uses Mathlib's totalized definition; the usual analytic reading excludes `s = 1`. Nothing here asserts a result for Hecke characters over other number fields. All claimed half-planes are strict.

The public entrypoint is `formalization/Cycle25/Assembly/Final/Endpoint.lean`. It exports `Cycle25.beta_le_theta`, `Cycle25.hecke_nonzero`, `Cycle25.dirichlet_nonzero` and `Cycle25.zeta_nonzero` at the exact boundary. The `*_catalogue` versions use the rational bound above. Despite its name, `Cycle25.theta` denotes the exact boundary; `Cycle25.Arithmetic.theta` denotes the rational rounding.

The proof combines variable-κ moments, reflected physical numerator estimates and a common-probe contradiction. It reuses OpenAI's coarse `7/8` bound to initialize the argument, Akash Levy's weighted-numerator construction, and the completed zero-slot moment from the earlier `4/33` branch. These dependencies are part of the proof. The final nonvanishing declarations require no supplied analytic estimate.

There is also a reusable auxiliary result in `formalization/Cycle25/Energy/Endpoint.lean`: `Cycle25.Energy.terminal_positive_at`. It treats the original canonical ray-prime family with one common smooth slot profile, `7/10 ≤ κ ≤ 3/4`, `β ≥ 51/100` and `2β − 1 ≤ κ`. It preserves the original `NaturalState` eligibility and `PositiveAt` conclusion. Its mesh depends on the cap, mask, profile-control parameters and ε, with seminorm orders chosen before the character and ideal and constants chosen afterward. The precise smoothness, support and arithmetic conditions are in the declaration. This result can be used through that interface without assuming the new quartic nonvanishing conclusion.

Lean, NanoDa and con-ron accepted all seven exported statements and their proof closures, with exact-statement comparison and only the three standard axioms. The clean source rebuild also passed: 301 modules compiled against pinned upstream libraries. See [Verification.md](Verification.md) for the scope, controls and recorded results. All three kernels passed; acceptance as **framework-verified** is requested. Catalogue status remains **verification-pending** until maintainer review. See `REPRODUCE.md` for reproduction and evidence, and [PROVENANCE.md](PROVENANCE.md) for authorship and source attribution.
