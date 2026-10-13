# Structural routes beyond the quartic boundary

Research note, 2026-10-13. This is a proposal and a diagnosis of the current argument, not a new nonvanishing theorem or a claim of priority. No new kernel check was performed for this note.

## What is already available

The strongest reviewed catalogue entry is Hailey Collet's quartic endpoint

\[
b_0=11/12-\ell_0/4=0.8748866470399641\ldots,
\quad 927\ell_0^4-3135\ell_0^3+2433\ell_0^2+275\ell_0-100=0.
\]

Its rational catalogue corollary is `683505193/781250000`. The manuscript is [paper.tex](../../../public/proofs/cycle25-quartic-20261010/paper.tex). The predecessor [weighted numerator manuscript](../../../proofs/akashlevy-20261009-weighted-numerator/manuscript/weighted_numerator_proof.tex) already makes the important structural change from a pointwise numerator bound to a fourth moment of the actual numerator. Recommending that change again would not be new. Likewise, using the zero supremum to set `kappa = 2 beta_* - 1`, retaining powerful-part conductor savings, and respecting the physical Euler correction are already in the quartic proof.

The quartic paper proves a global exponent certificate, B0.49, with equality only at

\[
\delta_0\simeq0.4693448587,\quad p=1/2,
\quad h_0\simeq0.7939475974.
\]

Consequently, a change that improves only bins far from that point will not improve the endpoint. The useful question is which analytic inequality loses information in a neighborhood of that binding point.

## First choice: estimate detector and physical numerator together

The present argument first counts rows that have a large zero detector (B0.38–B0.40), then estimates the physical numerator on those rows using Hölder and an unrestricted marked fourth moment (B0.41). In the normalized notation of the paper the resulting exponent is

\[
\frac14+\frac34R-\frac12qz_A.
\]

Here there are at most `U^(R+epsilon)` rows and `z_A` is the prime capacity available to the reflected physical numerator. This treats the large-detector event and large-numerator event separately. A **joint moment of their actual polynomials** could show they cannot occur together often enough to saturate both inequalities. This changes the object being estimated; it is not an adjustment of slot lengths.

Here is a precise sufficient lemma on an inverse-detector branch. Write `M_u(U^r)` for its normalized inverse witness and `S_u(U^m)` for the reflected physical numerator, with the actual fixed twists, orientations, independent heights and eligible rows. Suppose the branch supplies

\[
|M_u(U^r)|^2\ge U^{\delta r-o(1)}.
\]

A proposed new estimate is

\[
\sum_{u\ {\rm eligible}}
 |M_u(U^r)|^2 |S_u(U^m)|^4
 \ll U^{1+\eta(r,m)+\epsilon}.
\tag{J}
\]

The function `eta` is an allowed loss, not assumed to be zero. On that branch, (J) gives a restricted fourth moment at most `U^(1+eta-delta*r+epsilon)` and hence

\[
\sum_{u\ {\rm in\ branch}}|S_u(U^m)|
\ll U^{1/4+3R/4+(\eta-\delta r)/4+\epsilon}.
\]

Thus the unmarked joint moment already beats the existing marked numerator estimate if

\[
\eta(r,m)<\delta r-2qz_A.
\tag{gain test}
\]

This implication is elementary and rigorous assuming (J). The new analytic estimate (J) is unproved here. Prime marks can be added later, with a new capacity theorem; capacities of the separate moments cannot simply be added.

At the quartic binding geometry, direct numerical evaluation of B0.38–B0.45 gives

| Quantity | Approximate value |
| --- | ---: |
| `kappa` | 0.7497732941 |
| detector crossing length `t` | 1.1639535765 |
| inverse witness length `r` | 0.7456999427 |
| plain detector length `t-r` | 0.4182536338 |
| reflected physical length `m=1-y/h` | 0.4209851609 |
| row-count exponent `R` | 0.5903323535 |
| physical capacity `z_A` | 0.03512832468 |
| `delta*r-2*q*z_A` | 0.3335031357 |

These are exploratory floating-point evaluations, not endpoint certificates. The concrete first objective is therefore a joint inverse/plain estimate with loss **strictly less than about 0.3335**, locally in this range. A power saving `xi` in the restricted fourth moment reduces the physical error exponent at the longest row scale by `h*xi/4`. This is sensitivity of that error term, not a proved change in the final zero-free boundary.

There is a real obstruction: the product polynomial `M*S^2` has length exponent `r+2m ≈ 1.58767`. Even a favorable generic large-sieve bound of shape `U+N` would lose about 0.58767, failing the gain test. Thus this proposal needs arithmetic cancellation or a stronger tailored mean value; ordinary Cauchy–Schwarz and repackaging will not suffice.

### Concrete experiment and proof target

1. Expand `M*S^2` before taking absolute values. Form its convolution coefficients, retaining the Möbius factor, fixed target character, and all common-prime zero extensions. In matching orientations, the row dependence is a sextic symbol at the product; in opposite orientations it is a ratio, which can be encoded using exponents modulo six. Derive the exact Gram kernel over the original row set. This is a finite identity and is a sensible first formalization target.
2. Separate pairs of products whose ratio is a sixth power from the off-diagonal. Bound the former first. An unexpectedly large diagonal is a warning, but it falsifies (J) only with control showing that the off-diagonal cannot cancel it. On an incomplete row set, the diagonal alone is not a lower bound; see `gram-expansion.md` and its exact counterexample.
3. For the off-diagonal, retain Möbius signs through reciprocity and Poisson summation. Compare the exact signed quadratic form with the form obtained after absolute values. Test small Eisenstein-integer annuli, with genuine sextic characters, different fixed target twists, and independent heights. A finite-field analogue is useful debugging, but is not evidence of the required uniform asymptotic by itself.
4. Prove the bound first for one common annular profile and squarefree rows, then include repeated row valuations and the combined conductor. Use common-profile scale suprema for physical Euler shifts as in B0.44; arbitrary moving row coefficients are not permitted by the existing MP theorem.
5. Add the other detector branches. On the plain branch the corresponding object is `|S_detector|^4 |S_physical|^4`, with its own witness threshold and independent heights. Long inverse witnesses use sixth-power reconstruction and require a separate joint estimate. Improving only the inverse branch at the crossing does not improve the maximum if the competing branch remains binding.

**Success criterion:** new branch-specific restricted numerator bounds with a strict saving on an open neighborhood of the current binding point, retaining the old bounds outside it. Compactness and the existing strict global certificate then offer a route to a genuinely lower endpoint. No need to establish the strongest possible mixed moment everywhere.

**Failure criterion:** a lower bound for the full quadratic form (for example, a large sixth-power diagonal together with a sufficient lower bound on the off-diagonal) forces loss at least the gain-test threshold. Record that obstruction as a theorem and stop trying to improve this route through numerical parameter choices.

## Second choice: preserve correlations between the local numerator errors

The physical correction expands into local polynomials `H_p` and `Delta_p`. B0.43–B0.44 bound their absolute coefficient mass row by row, then apply the common-profile moment. The sharp term is explicitly `Delta_(p,1) ~ Q` at row valuation at least two; normalization and the powerful part cancel its size but supply no additional saving.

A possible structural improvement is to retain the **vector of shifted plain polynomials** and its Gram matrix instead of replacing every entry by a scale supremum. The exact starting object is

\[
\sum_u\left|\sum_h c_u(h)S_u(Y/h)\right|^4,
\]

with `c_u(h)` derived from the physical local table, not an arbitrary coefficient family. Correlations between nearby shifts and the signs in `G_p = -conj(psi_u(p))*H_p + Delta_p` might lower this norm even when the absolute mass is critical.

The small implementable experiment is to construct the exact local coefficient vectors for each of the six row valuations, multiply one or two prime factors, and compare the absolute-mass bound with the actual quadratic form for the shifted sums. The output should identify an algebraic cancellation surviving all fixed phases, or a counterexample showing that no such phase-uniform cancellation exists. Squaring or averaging cannot discard the natural character zeros at row primes.

This route is less immediately persuasive than the joint detector route: the local large term might be a true obstruction, and the quartic binding behavior may already be realizable with harmless local corrections. Improving coefficient mass alone is useful only if it changes the exponent at the binding geometry, not merely a constant. Do not promise an endpoint gain from a smaller numerical operator norm.

## Third choice: redesign the compensating operator, subject to a no-free-gain test

The compensating prime currently acts locally through `G_p`, leaving a main piece `-conj(psi_u(p))*H_p`. One can search over finite linear combinations of admissible marked physical probes, with coefficients independent of the row, so that their local Euler tables cancel an additional leading error monomial while retaining a nonzero principal double residue.

This is a finite symbolic linear-algebra problem before it is an analytic one: enumerate candidate marks from the existing completed-index construction; compute every valuation `j=0,...,5`; impose cancellation equations simultaneously for the actual phase variables; require nonzero principal residue; then price the reflected energy and coefficient mass of each candidate. Merely replacing `G_p` by an attractive polynomial is invalid unless that polynomial comes from an admissible physical probe with a proved reflection estimate.

The key falsification test is whether every universally cancelled unwanted monomial also cancels the principal residue, or whether the extra mark costs at least as much exponent as it gains. Such an obstruction is valuable: it would explain why more compensation alone cannot beat the quartic framework. A successful finite solution would be a concrete new probe, substantially more meaningful than a new choice of existing parameters.

## Tempting shortcuts that do not supply a new argument

- The maximizing amplitude parameter `p=1/2` is the endpoint of the current zero-supremum-dependent prime-sum bound. It is not saturation of the trivial triangle inequality for prime sums. Therefore it does **not** by itself imply that the characters are nearly constant on primes; a pretentiousness or rigidity argument needs a new quantitative theorem at this smaller amplitude scale.
- Generic higher moments do not come free. Their diagonal structure, conductor range, moving-radical terms and principal rows must be checked. An optimistic new moment capacity inserted into the scalar optimization is a conditional scenario, not a proof.
- Restricting the target to norm lifts of Dirichlet characters does not automatically restrict the intermediate sextic twists to norm lifts. Any smaller-family bootstrap first needs a family closed under the exact operations used by its detector and reflection.
- The common power saving must be chosen independently of the final target character. Target-dependent constants, conductor cutoffs and height exponents are allowed in the existing proof; a target-dependent improvement in the real boundary cannot close the family-supremum contradiction.

## Recommendation

Start with the exact Gram expansion and diagonal obstruction test for the **joint detector–physical-numerator moment**, at the explicit binding scales above. It directly attacks the information loss introduced between B0.40 and B0.41, has a quantitative pass/fail target, and can be investigated without claiming a new zero-free theorem. The original sources examined here do not establish that mixed estimate; no literature-wide novelty search has been performed.
