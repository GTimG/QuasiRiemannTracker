# Endpoint assembly review, 11 October 2026

This review was produced by a separate AI review pass within the same research session. It is not an independent maintainer or external mathematical certification.

## Verdict

I found no remaining missing analytic inference within the written scope of `EndpointAssembly.tex`, using the fixed-family local proposition in `PhysicalLocalAssembly.tex` and the pinned incumbent analytic framework. The reviewed conclusion is a complete proposed written source proof at `theta = 4374433/5000000`. This is not an assertion that the new endpoint has been elaborated as a complete Lean theorem, checked by independent kernels, accepted by an upstream maintainer, or qualified as a verified tracker record.

The review read the actual source contracts and analytic statements; it did not infer completeness from positive scalar audits alone. It depends on the pinned incumbent source theorems identified in the assembly. Their full proofs are not independently re-proved by this review.

## Physical numerator

The local proposition is inserted only on the audited near-endpoint row and small free-shift range. The physical fixed base is the source principal presentation for the target-dependent finite set S. The source coefficient identities conjugate the entire reflected product, retain relative fixed-ray coefficients and the common profile, and preserve original natural zeros. Growing retained free-row dyads eventually exclude the finite fixed-inducing exceptions.

The exact selected-slot theorem uses the full original slot width in the denominator of q, and masks error gains to zero. Its selected positive-gain product retains target-capacity gain even if its actual width is below 0.03. The old moment pays such short width with reserve 21/1000. If an actual plain scale is below 0.41, the separate old-moment reserve is 33/4000. No lower bound on positive-main supply or lower bound for the product of all main factors is assumed.

The source's combined conductor is retained in both reflection and coefficient damping. The large free-shift payment is valid for the entire allowed range, including the point at which the old selected capacity vanishes. This last point needs the actual unrestricted physical zero-slot estimate, not the weaker all-free-row density adapter. I checked the following directly:

- `Energy/Bands.ZeroAt` has no affine length-capacity condition; its target is `Z^(state.width+epsilon)` with each positive scale bounded by the fixed global cap `Z^L`.
- `Physical/CertifiedZero.finite_pair_zeroAt` gives the actual row-pair moment with each scale up to `U^2`.
- `certified_reflected_zero_fourier_moment` retains independent Fourier heights.
- `Physical/OriginalFourth.certified_original_numerator_fourth` accepts either its positive capacity inequality or an empty selected family, with reflected lengths up to the stated fixed cap.

Thus the zero-capacity branch incurs no uncharged positive-part plain-length cost. The large-shift scalar reserve has derivative 7/18 before the clipping point and 1/2 afterward and is continuous there.

For rows below d=1/2, the convenience selection wrapper's d>=1/2 hypothesis is not used. The generic `zero_error_whole_slots` theorem applies directly. The fixed lower row cutoff d0=1/200 lets one choose original slots uniformly fine, and total supply is greater than 1/3 while required old capacity is at most 5/21.

## Scalar coverage and feedback

I ran `python3 RH/tools/local_moment_endpoint_audit.py --check`; the exact stored certificate passed with 18, 6, and 1 Bernstein rectangles for the three stated endpoints. Its output remains explicitly conditional and not eligible as a tracker certificate by itself.

I separately checked the exact fractions in the new lower-row and auxiliary bounds:

- `G_old(1/200) <= 573880513637/750000000000 < theta-1/10`.
- The floor bound is `12898208027/15000000000 < theta-1/100`.
- The small-row relative exponent is `-21483987121/250000000000 < -1/20`.
- The saving after the upper row extension is `499/5000000000 > 9*10^-8`.

The old general row exponent is convex because `-q*min(d,2y-d)/(12*kappa)` is convex for q>=0 and all remaining d-dependence is affine. This covers [1/200,1/2] by its two endpoints. The interval [1/2,h-0.001] is affine. At the junction the smaller new capacity coefficient improves the exponent, and affinity covers the new interval up to h; the tiny extension is paid separately.

The kappa feedback is checked separately for the two branches. The new branch has derivative less than 1/50. The old branch includes the derivative of its physical denominator, so its safe bound is `695/14112 < 1/8`. Since `kappa-kappa_star = 2*(beta_star-theta)`, the feedback improvements are respectively at least `24/25` and `3/4` of the contradiction gap. Applying only the new-capacity derivative estimate to the old branch would have been incorrect; the final assembly does not do so.

## Principal probe, remaining rows, and continuation

The principal-probe estimate uses the actual hypotheses of B0.27, now stated explicitly in the endpoint fragment:

`M=x+y=1-ell`,

`y-2x+ell=-597590039/5000000000<0`,

`1+3ell-2M=-123299/750000<0`.

Its exponent is therefore `(5x+y)/12 = theta-k`. Dividing by the nonzero source normalization costs only logarithms. The principal Euler residue is unchanged, and the new geometry remains in the stated contour domains. Its principal remainders retain the positive y/4, h/24, and fixed prime-product reserves.

The explicit small-row bound is the source B0.56. The large-row bound is B0.57 with the outer real z-line chosen after the positive row extension. The height tails use the source's raw polynomial bounds before separation and choose the tail order after the target-dependent analysis-height exponent. This does not alter the common exponent margin.

I checked `Cycle25/Assembly/Continuation.lean`: `UniformCommonProbe` chooses common positive real margins before the target character, while `PrimitiveProbeContract` permits the probe, masked presentation, Big-O constants, and threshold to depend on that target. The new assembly has exactly this order. Its common Delta is fixed before the target; height orders and the analysis-height exponent may depend on the target. The continuation boundary remains above theta, where the Gaussian and Euler correction are nonzero. The Mellin transform therefore excludes a common strip below the presumed zero supremum. The proof uses a primitive zero arbitrarily near that supremum; it does not assume the supremum is attained.

Finally, the imprimitive Hecke finite factors are nonzero in the positive half-plane. The norm-lift product transfers the result to ordinary Dirichlet characters for theta<Re(s)<1, where both factors are finite. Re(s)>=1 is handled by the classical nonvanishing theorem with its principal-pole exception, so no zero-times-pole reasoning occurs at s=1. The modulus-one character gives zeta.

## Publication scope

The mathematical scope is a proposed complete written proof relative to explicitly pinned analytic inputs and the new local source proof, with internal adversarial review. The computational scope is exact scalar checks and selected compiled supporting lemmas. Publication should preserve both distinctions and should not label the contribution as an independently certified or accepted record.
