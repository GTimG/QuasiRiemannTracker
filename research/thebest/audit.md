# Independent analytic audit and structural research targets

This is a research audit, not a new proof or verified bound. It reads the local
reviewed catalogue, the quartic manuscript and its named analytic interfaces,
and the single-prime contribution. Numerical values below are diagnostic
floating-point evaluations of the manuscript's formulas, not certificates.

## What is actually strongest

The local `catalogue/results.json` records the quartic contribution as the
strongest verified result. Its boundary is

\[
b_0=11/12-\ell_0/4=0.874886647039964\ldots,
\quad
927\ell_0^4-3135\ell_0^3+2433\ell_0^2+275\ell_0-100=0,
\]

where the root is isolated near `0.16712007850681`. The published rational
`683505193/781250000` is a proved upper approximation. The independently
developed single-prime `29/33` route is weaker, but its mixed moment and
different detector architecture are reusable analytic material.

The quartic proof already combines moving-radical common-profile moments,
weighted reflected numerators, amplitude-sensitive slot selection, a signed
Gram estimate, and a variable zero-supremum parameter. Merely proposing one
of these ingredients is not new. Its exact certificate establishes a global
maximum of the stated envelope, so a finer numerical search of that same
envelope is not a structural improvement.

Primary source: `proofs/cycle25-quartic-20261010/manuscript/paper.md`, especially
B0.4--B0.9, B0.22--B0.27, B0.37--B0.48, and B3.4.

## The active obstruction, quantitatively

At the binding configuration in B0.45--B0.48:

| Quantity | Approximate value | Meaning |
|---|---:|---|
| `kappa` | 0.74977329408 | `2 b0 - 1` |
| `delta` | 0.46934485870 | zero-bin parameter |
| `p` | 0.5 | maximal physical prime-amplitude class |
| `h` | 0.79394759739 | largest relevant row-bin exponent |
| `x`, `y` | 0.37317248112, 0.45970744037 | physical geometry |
| `t` | 1.16395357651 | optimized detector truncation |
| `r`, `m` | 0.74569994272, 0.41825363378 | crossing of short inverse/plain witnesses |
| `R` | 0.59033235353 | bad-row count exponent |

The inverse capacity is `(1-r)/2 = 0.12715002864`; the plain witness
capacity is `(1-2m)/(6 kappa) = 0.03634270379`. The independent reflected
numerator capacity is approximately `0.03512832468`. Available slot length
is `ell/h = 0.21049258044`, so adding more total prime supply alone does not
address the bottleneck. The second inverse-moment constraint
`2r+8z <= 3` has slack approximately `0.4914` at inverse capacity. Improving
that constraint alone cannot move this binding point.

The physical reflection positive-part term in B0.27 vanishes at the optimum:
`1+3ell-2(x+y) = 5ell-1 < 0`. Improving that term locally is similarly
inactive. In contrast the exceptional Gram term contributes
`(y-x)/12 = 0.00721124660` to the physical exponent: a substantial structural
cost, not a negligible precision artifact.

The bad-row count comes from balancing two envelopes:

\[
R_s(t)=1-\delta+\delta C_\kappa(p)(3/2-t),\qquad
R_l(t)=1-\delta+(5/6-\delta)(t-1).
\]

The coefficient `5/6` in the long envelope comes from the loss in the
sixth-power amplification estimate B0.9, not an arbitrary tuning parameter.
The numerator then pays `1/4 + 3R/4` by Hölder. These two information losses
and the Gram exceptional channel are natural targets for new analysis.

## Priority 1: a joint witness/numerator large-deviation estimate

The existing detector produces *simultaneously* a large inverse witness and
a large plain witness at a shared zero height (B0.17--B0.18). The final
estimate compresses these into a row count and subsequently uses Hölder
against the reflected physical numerator. This forgets potential correlation
between the saturated witnesses and that numerator.

Seek a mixed estimate, initially only near the binding lengths, of the form

\[
\sum_u |M_u(U^r)|^2 |S_u(U^m)|^2
       |S_u(U^n;W^\vee)|^4 |Q_{u,I}|^2
\ll U^{E(r,m,n,z)+\epsilon},
\]

or a truncated/large-values version that is cheaper than this full moment.
At the binding row bin the unshifted reflected numerator has
`n = 1-y/h`, approximately `0.421`. The large witness plain has length
approximately `0.418`, suggesting a particularly concrete nearby-length
joint problem. Similar lengths alone do not identify profiles, heights, or
characters; the physical numerator and detector can have fixed twists and
opposite orientations that must be retained.

Use the saturated inequalities on the bad rows to divide out the witness
factors. A saving `U^{-eta}` in the resulting numerator sum improves its
Z-exponent by `h eta`. This is the correct deliverable: an explicit exponent
improvement on the bad-row set, not an unspecified claim of independence.

First calculation: expand the mixed quadratic/quartic form at these lengths,
classify diagonal and off-diagonal sextic congruences, and determine whether
the candidate saving is already contradicted by a diagonal family. Avoid
trying to establish a huge uniform moment family before testing this local
configuration. An estimate obtained solely by recombining the current MI,
MP, and Hölder inequalities is unlikely to improve their certified envelope.

## Priority 2: replace sixth-power padding in the long inverse bound

B0.9 reconstructs rows `u a^6`, averaging over only roughly `(H/U)^(1/6)`
copies, and gives

\[
\sum_{q_u\asymp U}^{(6)} |M_u(D)|^2
\ll U^{1/6}H^{5/6}(UD)^\epsilon,
\qquad H\gtrsim D.
\]

This creates the long-witness slope `5/6`. A direct large sieve on
sixth-power-free rows, a reciprocity argument using the Möbius coefficient,
or a higher-rank amplifier could conceivably prove a local replacement
`1 + lambda (r-1)` with `lambda < 5/6` near the long-witness transition.
It must improve the actual arithmetic estimate; changing the exponent of
the padding without preserving the row character is invalid.

Replacing `V=5/6-delta` by `lambda-delta` in B0.40 gives

\[
R=1-\delta+\frac{\delta C(\lambda-\delta)}
 {2(\lambda-\delta+\delta C)}.
\]

At the binding configuration, the derivative of the numerator exponent
with respect to `lambda` is approximately `0.03201289`. Thus any genuine
decrease of that slope gives a strict local saving. This number is a
sensitivity diagnostic, not the derivative of a fully reoptimized theorem.
One can target a small compact length interval rather than all lengths.

## Priority 3: identify and project the exceptional Gram channel

B0.22 is a signed estimate for the *actual physical coefficients*:

\[
\sum_m |A_m|^2\ll (Q/Y)
\{1+P_a^{1/6}+P_a^2/Y\},\qquad P_a=Y^2/Q.
\]

The `P_a^(1/6)` term is traced explicitly to exceptional frequencies
`k=e r^6`. Classify its complete arithmetic kernel before bounding it in
absolute value. Two possibilities deserve separate tests:

1. It is a low-rank structured component that can be evaluated, moved into
   an explicit main term, or canceled by a finite combination of probes.
2. It contains an irreducible positive component inseparable from the
   desired principal residue.

For a proposed probe combination, compute both its quadratic exceptional
Gram form and its principal linear functional. The decisive finite problem
is whether the Gram form has a null direction on which the principal
functional is nonzero. This is more informative than optimizing an arbitrary
radial weight. If every null direction kills the residue, this strategy has
a clean obstruction and should be abandoned in that form.

Do not simply delete sixth-power rows: the principal signal in B0.28 comes
from the related sixth-power decomposition and the pole of `zeta_K(6z)`.
Also, B0.22 is not asserted for arbitrary column coefficients; a new
projection requires a fresh signed arithmetic derivation.

## What not to spend the next cycle on

An additional obstruction supplied by the coordinating investigation is
particularly strong. For `ell` in `[1/6,1/5]`, set
`kappa=(5-3ell)/6`, `p=1/2`, and
`delta=kappa(5-9ell)/(6kappa+(6kappa+2)ell)`. Substitution into B0.47 gives

\[
F-b=\frac{h(21\ell-40)P(\ell)}
 {24(3\ell^2-4\ell-5)(234\ell^3-753\ell^2+525\ell+100)},
\]

where `P` is the quartic defining the current endpoint. This audit
independently checked the equality by exact rational evaluation at 21 points
across the interval; that check is not a symbolic identity proof. The
coordinator is preparing the exact polynomial certificate. The sign is
unambiguous: both `21ell-40` and `3ell^2-4ell-5` are negative, while the last
factor is at least `100+525/6-753/25 > 0`. Since `P` is increasing on this
interval, the expression is positive for `ell>ell0` and every `h>0`.

Consequently the same bad amplitude/zero bin obstructs every adaptive
choice of positive geometry parameter `h` **within this unchanged envelope**.
Combining such bounds by triangle inequality also preserves the obstruction;
convexly averaging the displayed exponent excess leaves it positive. This
does not rule out cancellation in the actual probe, new joint estimates,
or a new physical geometry whose analytic envelope is different. Those
are precisely the substantive research targets above.

- More digits in the quartic root or the same two-variable certificate.
- More prime slots with no new capacity or correlation estimate.
- Improving only the slack MI constraint or the inactive reflection term.
- Treating MP as an arbitrary-coefficient large sieve. Its positive-slot
  theorem has canonical prime pools, a common profile, fixed ray-character
  coefficients, a common mesh, and the zero-supremum hypothesis.
- Feeding an improved desired zero-free boundary into MP as an assumption.
  Initialization is the existing `7/8` theorem; the legitimate feedback
  variable is `kappa = 2 beta_* - 1` in a contradiction.
- Increasing moment order without first deriving the new capacity, diagonal
  cost, and bad-row Hölder exponent. A higher moment is not automatically
  stronger when its admissible lengths shrink.

## Recommended next deliverable

Produce a symbolic local exponent model with one genuinely new input in
each branch: a joint bad-row numerator saving, a long-inverse slope
improvement, or a controlled exceptional Gram subtraction. First identify
the arithmetic lemma and its diagonal obstruction; then reoptimize and
certify the full envelope, including nearby bins and character transfer.
No numerical improvement should be called a new bound before its analytic
input is proved and the source-level admissibility conditions are checked.
