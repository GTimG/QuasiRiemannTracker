# Internal adversarial analytic review, 11 October 2026

This review was produced by a separate AI review pass within the same research session. It is not an independent maintainer or external mathematical certification.

This is the final review of the new fixed-family local-moment source assembly. It supersedes the early version of this note, written before the actual signed-row, density, fixed-dictionary, and restricted-child proofs were supplied.

## Verdict and precise scope

`PhysicalLocalAssembly.tex` now gives a written analytic proof of the stated local physical moment relative to the pinned Cycle25 incumbent theorems and the explicitly cited companion derivations. I found no remaining missing analytic inference within that fixed-family proposition after the corrections below. This is a source proof, not a newly compiled complete moment theorem, a clean dependency replay, or independent-kernel verification. Its statement deliberately allows constants and finite height orders to depend on the fixed arithmetic dictionary. It does not claim the stronger quantifier order in which those orders precede all fixed character moduli.

The global endpoint has its separate row-count, numerator, continuation, supremum, and transfer argument. This note establishes the local and physical-numerator application pieces; the completed review of the companion global argument is recorded in `ENDPOINT_REVIEW.md`.

## Analytic points resolved by source identities

- The signed effective row is reconstructed with residues `1+t` and `1-t`, including canceled local punctures, genuine second common factors, and arbitrary valuations. The first projector divides the row. The second projector generally does not: its dyadic count is paid by the paired extraction scalars. The B3.68 clipping terms are nonpositive after B3.69, which justifies the high pointwise exponent without introducing a false row divisor.
- Zero bins use the literal fixed exclusion ideal and one fixed parent translate of its ray-character group. Different translates are partitioned before binning. Conjugation applies to the whole character; replacing the conjugate of `eta*psi_w` by `conj(eta)*psi_w` would change the family. `FixedDictionaryBridge.tex` supplies the exact coefficient identity, natural conductor bound, mask invariance, and twist-exclusion equivalence needed here.
- `PlainUnmarkedDensity.tex` obtains a threshold before all heights: use the detector at height `U^tau_det` when `T` is below that height, and use the trivial row count paid by a fixed power of `T` above it. The moment degrees are chosen before `tau_det`. The external bin exponent is chosen after the resulting density degree. The balanced cutoff is chosen before constructing the actual witnesses.
- The low-bin restriction is imposed after both transforms on a positive energy. The actual allocation and radial identities allow arbitrary `keep`, so no Poisson formula is applied to a zero-bin indicator. Exhausting the slots invokes the incumbent unrestricted zero-slot theorem. The actual-width correction is `d_* + r(F-d_*)_+ <= delta_2 + r F_+`; neglecting the simultaneous width saving when `d_*` is negative would be invalid.
- The padded main radius is the existing `mainCommonRadius` at `sigma=3a` and `omega=delta+reserve`. Its actual domination theorem covers the enlarged smooth ball. The second nominal width and defect are recomputed from this radius; the extracted error radii remain their old radii.
- The complete first labels stay inside Cauchy and the common Fourier Hilbert norm. The joint reconstruction count replaces, rather than precedes, an independent first-label count. A common dominating Fourier measure handles smooth parameters that depend on frozen labels.

## Comparison and terminal checks

The comparison expands the extra common mask, uses the exact conductor-bound reflection and natural Euler-restoration identity, and invokes the old moment with budget at most `0.93 M + o(M)`. The full centered difference retains its original common mask. Polynomial-size Euler holes have uniformly small-power absolute coefficient mass and do not change positive-real zero maxima.

For the main fixed-inducing terminal the exact B3.75 expression is

`F1 = (c+5d+R+E)/6 + Bc - 4a - 5omega/6` when `c>=d`,

and `F1 = c+(R+E)/6 + Bc - 4a - 5omega/6` otherwise.

The earlier `-5a` was a weaker lower bound, not the exact identity. Retaining the exact negative maximum in B3.80 gives `A-M`, attained at the comparison length `M/4`. It pays the positive fixed-amplifier terminal loss. Replacing this maximum by its positive part would erase the needed proof. The unchanged error terminal has allowance `A-M+3sigma+o(M)<0`.

## Physical numerator corrections

`PhysicalScaleShortening.tex` deals with both kinds of shortening that the local window does not itself allow.

1. If either actual plain length is below `0.41`, the old `9/2` moment has reserve `33/4000`, using the exact audited coarse bounds `n<=211/500` and `z<=71/2000`.
2. If the actual selected prime width is below `0.03`, the old moment has reserve `21/1000`, regardless of whether both plain lengths stay in the local window.
3. The source theorem `Cycle25.Numerator.SlotSelection.zero_error_whole_slots` requires target capacity at most the total original supply, not the positive-main supply. It returns positive-gain main slots whose physical width may be short while their squared spike still saves `U^(2q*target-delta*mesh)`. The exact full amplitude class theorem is `Cycle25.Numerator.source_class_main_selection`; errors have zero gain but retain their widths in the denominator of `q`. Zero-gain main factors must not be reinserted into the lower-bounded product.
4. The full-main product upper bound and the weighted free-shift coefficient mass remain those of the source. The selected subset may depend on the dilation box, but the original amplitude class and its upper bound do not.
5. All larger free shifts are paid by the old capacity and the coefficient damping. The normalized reserve is continuous at capacity zero, has derivative `7/18` while that capacity is positive and `1/2` afterward, and already exceeds `3/10000` at `t=1/1000`. Thus the proof covers every shift permitted by the original support cutoff, including the empty selected family.

`ScaleShortening.lean` checks six elementary rational/affine statements with Mathlib only. Its refreshed receipt records successful compilation, no warnings, and only `propext`, `Classical.choice`, and `Quot.sound`. It does not certify the analytic source identities just cited.

## Remaining limits

The local proposition is restricted to the source fixed-family setting with no parent moving support of positive width. A polynomial-size extra common mask is row-independent within the relevant sum, though it may depend on frozen outer labels. Neither the analytic argument nor the elementary Lean receipt licenses arbitrary extra ray twists, a row-dependent mask before Poisson summation, a new independent label count, or a global density threshold depending on the eventual live height. These restrictions are part of the proven statement rather than deferred analytic obligations.
