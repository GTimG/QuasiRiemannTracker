# Referee report

## Overall assessment

**I regard the submitted argument as a complete proof of the stated rational bound.** I found no blocking mathematical gap, no undisclosed zero-free hypothesis, and no violation of the First Proof LaTeX contract.

The claimed bound is
\[
\theta=\frac{874957019421}{10^{12}}=0.874957019421,
\]
and its improvement over the required incumbent is exactly
\[
\frac{3499999}{4000000}-\theta
=\frac{42730579}{10^{12}}>0.
\]
The metadata comment, displayed bound, and main theorem agree.

I found **one definite provenance error**: the certificate hash in the `StageOneCertificate` entry of `references.bib` is stale. The correct hash appears in `answer.tex`, and the embedded script agrees exactly with the executed script. This does not invalidate the proof or make its essential computational certificate unavailable. I also recommend explicitly defining the Gaussian \(V_{\rm G}\) at its first appearance.

The assessment below distinguishes:

- mathematical arguments checked in `answer.tex`;
- imported results checked against the literature;
- computational corroboration;
- historical verification claims that I have **not** treated as premises.

This is a mathematical referee assessment, not a Lean/kernel verification.

---

## 1. Files, compilation, and computational checks

### 1.1 Current research-notes snapshot

I ran the prescribed verification code at the beginning of the review and again as the final tool call.

The current snapshot has:

- **Bytes:** `522184`
- **SHA-256:**  
  `429d7faa207421960b17135aeac39a0b4602b121bf1865407c280e026f19bdf6`

These match the supplied specification. The notes were not edited.

I consulted the source-reproduction section to recover the complete current source and the accompanying checker files. I did not substitute a notes-only mathematical argument for a proof in `answer.tex`.

### 1.2 Complete source used for compilation

The recovered current `answer.tex` has:

- **Bytes:** `491783`
- **SHA-256:**  
  `6d533f92a514067fa2021ab17b52e39e221e222550673467b7321761d2418f8d`

This is the current source identified by the capsule, not the older predecessor whose hash is recorded in the historical-input discussion.

I ran `pdflatex` on the complete document, not a fragment. A third pass stabilized the cross-references.

| Contract requirement | Result |
|---|---|
| Exactly `\documentclass[12pt]{article}` | Pass |
| Standalone document | Pass |
| At most 200 pages | **160 pages** |
| Permitted margin/layout settings | Pass |
| No prohibited line-spacing changes | Pass |
| No explicit in-document font-size changes | Pass |
| Successful compilation | Pass |
| Final undefined-reference or LaTeX warnings | None |
| Overfull boxes in final log | None |
| Extracted text outside physical page boundaries | None detected |
| Exactly one uniform-bound metadata comment | Pass |

The document does not use external `\input`, `\include`, or bibliography-file directives to supply missing proof material.

### 1.3 Executed certificates

All four supplied scripts exited successfully.

| Script | Result and scope |
|---|---|
| `exact_certificate.py` | All rational and symbolic assertions passed |
| `local_transform_certificate.py` | Five quotient-free Euler identities, affine local-error checks, and transformation ledgers passed |
| `finite_local_certificate.py` | 20 Gauss identities and 768 full-frequency identities passed at norms \(7,13,19,25\) |
| `moment_transport_certificate.py` | All reported finite transport and zero-pattern checks passed, including \(7^6=117649\) moving-character tests |

I additionally checked that the essential script printed in the `answer.tex` verbatim block agrees **byte-for-byte, under its stated normalization**, with the executed `exact_certificate.py`. Its hash is
```text
af406d0f43d651838a65c39da9eb69c3837fba72f2ddad7c15adb4dc9bc7711f
```

I independently checked several simplifying identities, including the endpoint cancellation of \(z_0\), the capacity-loss constant
\[
\frac{2(5/12)(1/3)}{3(13/18)^2}
=\frac{30}{169}<\frac14,
\]
and the exact improvement over the incumbent.

These computations corroborate the algebra. **They do not, by themselves, prove the analytic moment estimates.** Those require the written arguments audited below.

[Computational audit record](sandbox:/mnt/data/referee_work/referee_computational_checks.json) · [Final LaTeX log](sandbox:/mnt/data/referee_work/answer.log)

---

## 2. Literature checks

### 2.1 Goldmakher–Louvel

The cited Definition 1 requires a family of primitive, trivial-infinite-type Hecke characters, a finite reciprocity-class structure, and the primitive-conductor property for products of coprime indices in the same class. Theorem 1.1 then supplies the stated squarefree quadratic large sieve. The manuscript does not merely assume that its symbols fit this framework: its unit adjustment at \(\lambda_3\), conductor calculation, and common-class argument address these hypotheses. ([arxiv.org](https://arxiv.org/pdf/1112.1642v2))

### 2.2 Heath-Brown

Theorem 2 has the bound
\[
(M+N+(MN)^{2/3})(MN)^\epsilon
\]
with both starred sums over squarefree Eisenstein elements congruent to \(1\pmod3\). It does **not** require squarefree rational norms. I checked the author-uploaded manuscript and the matching statement in Dunn–Radziwiłł, Theorem 9.1. Thus the indexing used in Appendix C is appropriate. ([researchgate.net](https://www.researchgate.net/publication/254847691_Kummer%27s_Conjecture_for_Cubic_Gauss_Sums))

### 2.3 Dunn–Radziwiłł

The cited version contains the Kubota multiplier, infinity coefficients, cusp expansions, and Appendix A coefficient table used here. In particular, the conjugation convention \(\overline{d_j(-\mu)}\) is important and is handled correctly. The submission imports the theta formulas, not the paper’s GRH-conditional prime asymptotic. ([arxiv.org](https://arxiv.org/pdf/2109.07463v3))

### 2.4 Hecke continuation and functional equations

Poonen’s Theorem 5.22 supplies the required continuation and functional equation. The submission specializes the complex-place gamma factor consistently to
\[
(3Q)^{s/2}(2\pi)^{-s}\Gamma(s)L_F(s,\psi).
\]
The principal regularization is separately handled rather than incorrectly treating the principal \(L\)-function as entire. ([math.mit.edu](https://math.mit.edu/~poonen/786/notes.pdf))

### 2.5 Fixed-ray prime supply

Thorner–Zaman’s theorem includes the possible exceptional-zero term. For a **fixed** extension, that term is lower order in the eventual prime asymptotic. The submission uses precisely this fixed-extension consequence; it does not assert a prime asymptotic uniform in a moving target conductor. ([arxiv.org](https://arxiv.org/pdf/1803.02823v3))

### 2.6 Fixed-numerator symbols and imprimitive factors

Milne VIII.5.5 provides the ray-class factorization of a fixed-numerator power-residue symbol. DLMF 25.15.4 gives the primitive/imprimitive Dirichlet identity used in the transfer. The submission also supplies the elementary nonvanishing argument for the deleted Euler factors in \(\Re s>0\). ([jmilne.org](https://www.jmilne.org/math/CourseNotes/CFT.pdf))

### 2.7 Prior-improvement discussion

Liu’s version 1 was submitted on **October 8, 2026**, and Theorem 21.1 states the all-Hecke/all-Dirichlet bound
\[
\frac{1507-2\sqrt{921}}{1653}.
\]
The manuscript’s comparison with that stated constant is accurate, and its exact checker verifies the claimed rational interval for the difference. No theorem from Liu is needed in the present proof. ([arxiv.org](https://arxiv.org/abs/2610.12234v1))

The cited heuristic exploration does label its smaller extrapolated values as heuristic and uses a changed long-row slope. The submission correctly refuses to import that slope change without a new moment estimate. ([github.com](https://github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification/blob/main/reports/improvement_exploration.md))

I did not use any claimed formal-verification result or earlier critic approval to validate an analytic step.

---

## 3. Main-text audit, in manuscript order

For readability, adjacent paragraphs proving one local claim are discussed together. The audit follows the document’s order.

### Section 1: Problem statement and interpretation

The adopted interpretation is explicit and faithful to the stage task:

- the required improvement is over \(3499999/4000000\), not merely over \(7/8\);
- the theorem concerns every Dirichlet character;
- “smallest” is not represented as an absolute optimum over all conceivable methods;
- the restricted optimality claim is separately specified.

There is no ambiguity being silently used to weaken the task.

### Section 2: Result, attribution, and scope

The rational arithmetic is correct. The main theorem includes:

- \(q=1\), hence \(\zeta\);
- principal characters;
- imprimitive characters;
- real zeros;
- unrestricted height;
- the auxiliary finite-order Hecke family over \(\mathbb Q(\sqrt{-3})\).

The text distinguishes the submitted rational from the nearby algebraic optimization threshold. It also distinguishes attribution from a proof dependency. These distinctions are necessary and are maintained later.

The statement that essential arguments are in the document is borne out by the appendices: the new proof does not merely cite the old manuscript’s moment lemmas at expanded parameter ranges.

### Section 3: Geometry and constraint ledger

The displayed geometry is consistent. Independent numerical diagnostics from the exact rationals give
\[
\begin{aligned}
\ell&\approx0.1668385889826667,\\
b&\approx0.1234056854241650,\\
l_x&\approx0.3548778627965842,\\
l_y&\approx0.4782835482207492,\\
h&\approx0.8119607261860825.
\end{aligned}
\]
The exact checks, rather than these decimals, establish the inequalities used in the proof.

The identities for \(C(s)\), \(C(\theta)\), and \(\theta\) agree. In particular, the change of geometry is propagated to the Mellin exponent; the old additive constant is not inadvertently retained.

The definition of \(B\) is appropriate. It assumes only the elementary bound \(B\le1\), not the incumbent or the old \(11/12\) result.

### Continuation criterion

The criterion is valid.

The important points are all present:

1. The two comparison estimates give a common exponent \(C(b_*)\) with
   \[
   \theta<b_*<B.
   \]
2. Moving the defining contour right gives arbitrary power decay as \(Z\downarrow0\).
3. These endpoint estimates give a holomorphic Mellin transform on \(\Re s>b_*\).
4. Fourier inversion identifies that transform on the original line.
5. Meromorphic continuation yields the identity with \(L_F^S\).
6. The nonvanishing right side excludes zeros throughout the enlarged half-plane.

No supremum is assumed to be attained. A principal pole does not obstruct the argument: it corresponds to a zero of the reciprocal.

The quantifiers are also correct. Target-dependent constants and starting scales are allowed; the positive saving and resulting boundary must be common, and the closure section supplies those.

### Hecke induction and Dirichlet transfer

The imprimitive Euler factors are holomorphic units for \(\Re s>0\), so zero orders are preserved in the relevant region.

The norm-lift factorization is correctly used after deleting the relevant primes. The possible pole cancellation at \(s=1\) is not ignored. The special primitive character \(\varepsilon_3\) is handled by
\[
L(1,\varepsilon_3)
=\sum_{n\ge0}\frac1{(3n+1)(3n+2)}>0.
\]

Thus the transfer genuinely establishes an all-Dirichlet conclusion, rather than only a Hecke or zeta conclusion.

---

### Section 4.1: Fixed data and the base probe

The roles of the fixed ray group \(T\), the target-dependent excluded set \(S\), and the fixed-numerator character \(\Xi\) are distinguished correctly.

In particular:

- \(\Xi\) is not incorrectly assumed to factor through \(T\);
- the target-dependent data are fixed before the varying scales;
- inverse character values are evaluated only on units;
- the primitive auxiliary character at \(S\) is used to remove forbidden Poisson frequencies.

The construction of \(\xi\) works at the primes over both \(2\) and \(3\). The order-dividing-six condition is used later when frequencies are written as \(ua^6\).

### Low separation

The Mellin separation has the correct normalization \(Q^{-1/2}\). The row multipliers of modulus one are retained, and the arithmetic coefficient in the additive factor is independent of the row variable.

The support cutoff \(\Omega\) is chosen before the row summation. This is important for the later Hilbert-space estimates.

### Physical slots and whole-index marks

The slots are required to be disjoint at the level of their underlying prime supports. Consequently each selected prime occurs only once in a tuple.

The modified probe is defined by an exact finite operation, including:

- the factor \(q_{p_J}^{-3/2}\);
- the marked scale \(Zq_{p_{J^c}}\);
- the rescaled \(X,Y\);
- unchanged original slot windows.

The low representation retains the same completed-index marks. There is no replacement of a whole-index condition by a squarefree-index condition.

### Poisson representation

The finite transform uses the full modulus \(sb_*A\), including the case \((s,A)\ne1\). The definition of \(F(s,A,H)\) explicitly records that overlap.

The prefactor accounting is consistent:
\[
\frac{X}{q_A}\cdot
\frac{\sqrt{q_s}}{\sqrt{q_{b_*}q_sX}}
=\frac{X^{1/2}}{\sqrt{q_{b_*}}q_A}.
\]

The sixth-power decomposition includes unit factors in \(u\). The zero frequency is removed by primitivity at the excluded primes, rather than discarded without justification.

The positivity proof for \(m_0(1/6)\) is sound: it does not assume that the Fourier transform of the original nonnegative weight is itself nonnegative.

### Local scalar calculation and Euler product

The local calculation covers:

- \(t=k=0\);
- the \(t=0,\ k>0\) branch;
- \(k=0\);
- \(k=1\);
- the vanishing for \(k\ge2\);
- principal zero-extended Gauss characters;
- all six valuations \(j=0,\ldots,5\).

The unit factors are kept until their cancellation. The quadratic-refinement calculation accounts for the cross-prime phases; it is not simply an assertion that the coefficients are multiplicative.

The extraction of the scalar quotient is consistent with the local term
\[
-\eta(p)\overline{\chi_p(u)}Q^{-x}.
\]
For \(u=1\), this is exactly the target reciprocal factor.

The normal-convergence bounds distinguish primes dividing \(u\) from the remaining primes. The former form a finite product controlled by a divisor-product estimate; the latter have a summable defect.

### Quotient-free selected correction

This is a significant strength of the treatment.

The proof does **not** continue the raw quotient \(P_p^*/P_p\) through possible zeros of \(P_p\). Instead, it defines \(G_p\) and the full selected-tuple correction by expressions without that denominator.

The tuple formula is holomorphic in the required Euler regions. The later factorization into individual slot quotients is used only in the dynamic region where \(H_p\) has separately been shown to be bounded away from zero.

I found no illicit division at an unknown zero in this part.

---

### Section 5: Low estimate

The elementary energy lemma handles the slack variables and both branches of the minimum. Its use of
\[
\frac y4+\frac{(T-y)_+}{2}\ge\frac T4
\]
is valid without an additional sign assumption on \(T\) or \(y\).

For the rescaled tuple, the Gram parameter remains
\[
P_a=Y'^2/Q=q_{b_*}^{-1}Z^b.
\]
The scale conditions needed for the Gram remainder and the row ranges follow from the exact geometry ledger.

The proof applies the general reflected-energy estimate before specializing the geometry. It does not assume that an old optimized low bound remains valid after changing lengths.

The final tuple exponent is correctly calculated:
\[
-d+\frac{(5\ell+d-1)_+}{8}\le-\frac{7d}{8}\le0.
\]
The count of rescaled tuples and their \(q_{p_J}^{-3/2}\) weight are each included once.

### Section 6: Principal correction and comparison

The extension below \(7/8\) is proved directly from the rational local expressions. The numerical contraction estimate is supported by the ideal-count tail bound.

The argument gives both:

- a holomorphic, nonvanishing \(H_\eta\);
- a nonzero eventual normalizer \(A_T(Z)\) with only logarithmic reciprocal growth.

The prime asymptotic is applied to a fixed ray extension. Deleting the target-dependent finite set changes the starting threshold, not the limiting density.

The contour moves cross only the stated poles at \(w=1\) and \(z=1/6\). The reciprocal target is initially kept to the right of \(B\). The principal target is regularized correctly, and polynomial height bounds are dominated by the three independent decay coordinates.

The resulting three principal error exponents agree with the displayed Mellin powers.

---

### Section 7: Growth, logarithmic control, and detection

**Strip growth.** The damped-rectangle argument correctly separates qualitative fixed-conductor growth from uniform boundary estimates. It therefore does not accidentally introduce an uncontrolled conductor-dependent constant into the uniform strip bound.

**Logarithmic control.** The holomorphic logarithm is chosen only after zeros have been excluded from the relevant disk. Borel–Carathéodory followed by three-circles gives a subpower bound; it is not an unsupported inference from zero-freeness alone.

**Deleted Euler factors.** The primitive conductor and the deletion radical are both tracked. This matters on the reflected line, where the real part can be slightly negative.

**Buffered bins.** The maximum is over a finite family and a compact zero rectangle. The increment argument and downward rounding produce the required buffer. The floor bin is not assigned a fictitious witnessing zero.

**Dyadic pointwise estimates.** Only the retained contour segment is shifted through the buffered rectangle. Infinite tails remain on an absolute line. The distinction between pointwise horizontal-trace bounds and integrated tail bounds is correctly maintained.

**Simultaneous witnesses.** The truncated inverse construction has the required cancellation below \(D_*\), and the gamma-shift error is uniformly negligible throughout \(1\le t\le3/2\). The Fourier separation supplies the same twist height in both witness factors.

The saturation conclusion follows from comparing the product lower bound with the two pointwise upper bounds. Since \(\delta\ge1/50\), the deduction
\[
m\le\frac12+O(\epsilon)
\]
is uniform.

**Prime amplitudes.** The ray expansion produces characters in the declared family. The logarithmic-derivative argument retains the original deleted factors. The amplitude subdivision does not claim a lower bound when \(g_i=0\).

I found no preliminary zero-free theorem hidden in the detector.

---

### Section 8: Row counts

The orientation paragraph is correct: the whole witness product is conjugated when needed, not merely its character notation. The resulting prime coefficients remain fixed independently of the row.

The inverse and plain capacities are applied with their proper hypotheses. The inverse capacity is decremented by a fixed positive amount, so the argument does not take an unjustified limit of estimates requiring strict inequalities.

The passage from \(\kappa_0\) to
\[
\kappa=2B-1
\]
is explicitly paid for. The bound
\[
\frac{30}{169}\Delta<\frac{\Delta}{4}
\]
is correct.

The crucial logical point is that the plain lemma’s premise is discharged by the definition of this \(\kappa\):
\[
B=\frac{1+\kappa}{2}.
\]
Its use is therefore not a conditional assumption about an independently conjectured zero-free region.

The cases \(\delta\le5/6\), \(\delta\ge5/6\), the unselected alternative, and the floor are separately handled.

### Section 9: Dynamic local errors

The off-row cancellation is expressed as a holomorphic local identity. Individual quotients are introduced only after the cutoff makes \(H_p\ne0\) on the dynamic region.

The ramified boundary table isolates the sole term that needs a conductor saving. The proof then applies
\[
q_{\mathfrak f_u}
\ll_S q_u\prod_{p\in J_0}q_p^{-(j_p-1)}
\]
to the **entire set of distinct strict labels at once**.

This avoids spending the same conductor deficit independently for several slots. The identity
\[
-\Re w-\left(\frac12-\Re w\right)=-\frac12
\]
explains the resulting central exponent at a strict label.

The aggregate \(12e\) loss is explicitly retained in the high-side ledger. It is not silently relabeled as an arbitrarily small loss at fixed \(e\).

### Section 10: Nonprincipal comparison

The contour path remains in the stated Euler region, first with global reciprocal control and then inside the buffered rectangle.

Amplitude subdivisions are made only after the original fixed-bin expression has been continued. The proof does not analytically continue row sets defined by pointwise inequalities.

The exponent
\[
E(d;\delta,q,R)
\]
matches the outside powers, row count, reflected numerator, and central slot normalizations.

The small-row argument includes nonidentity unit rows. The statement that only \(u=1\) has a principal numerator is supported by the Kummer-character argument, not by ignoring units.

The large-row estimate is an actual summable infinite tail. The very large fixed value of \(z_\infty\) changes constants and required smooth orders, but not the logical order of choices.

### Section 11: Continuous certificate and closure

The continuous-domain proof is stronger than a grid check:

- the near-active region uses an exact completed square;
- the other \(y\)-coefficients have coefficientwise rational lower bounds;
- the remainder uses positive Bernstein coefficients on two rectangles;
- \(\mathcal J\) is bounded above and below away from zero.

The executed script verifies the printed identities and inequalities.

The separate floor, short-row, large-\(\delta\), small-row, and unbounded-row estimates cover the complementary ranges. The extension from \(d=h\) to \(d=h+\zeta\) spends less than the reserved margin.

The order of choices is logically consistent:

1. count losses and capacity decrement;
2. a mesh independent of the target;
3. finitely many physical slots;
4. principal margins and remaining real losses;
5. target-dependent arithmetic data;
6. internal height orders;
7. a sufficiently small positive \(\tau\);
8. the external tail order last.

This yields common positive comparison savings while allowing target-dependent starting scales. The continuation criterion then applies exactly as stated.

### Section 12: Optimization and limitations

The general low-energy calculation includes the cases \(M+\ell\ne1\). The dual certificate checks the full right-hand sides, not merely coefficient domination.

The lower-bound proposition is explicitly about a restricted exponent program. Its argument uses a valid admissible endpoint and proves a contradiction when the proposed boundary lies below the isolated cubic threshold.

The manuscript does not claim that relaxed energy variables are realized by actual arithmetic rows, or that the restricted lower bound is an absolute barrier for every possible extension of the method.

The final discussion of stronger inverse or mixed moments concerns future improvements, not an assumption needed for the submitted theorem.

---

## 4. Appendix audit

## Appendix A: Arithmetic conventions and smooth calculus

The primary-generator convention, zero extension of all character powers, and distinction between the two uses of \(G\) are consistently maintained.

The finite Gauss identities have an all-prime derivation in the text. The finite computations are supplementary checks, not the proof.

The fixed-numerator ray argument does not absorb moving good primes into a fixed modulus. That distinction is maintained in the later recursions.

The smooth-separation rules use a common ambient Fourier density chosen before evaluating rows or live labels. Euler differentiation of a normalized monomial kernel does not produce a derivative-order power of the large scale. This supports the later order-of-choices arguments.

## Appendix B: Completed reflection

The appendix supplies the extension needed beyond a unit-frequency reflection formula:

- all fixed-modulus frequencies, including nonunits, are retained;
- active and inactive moving-prime branches are distinguished;
- the \(j=0\) and \(j=4\) branches are explicitly evaluated;
- cusp sectors and their fixed phases are identified;
- the angular derivative removes cusp constant terms;
- the Mellin normalization and conductor exponent are checked;
- absolute convergence is established before later kernel manipulations.

The marked reflection uses \(1_{p\mid A}=1-\chi_p(A)^0\) with the zero extension intact. The inactive-mark coefficient and the active-mark coefficient consequently have the stated different sizes.

The final pair-phase analysis explains why nonresidual primes must be frozen before the hybrid norm. The manuscript performs that freezing.

## Appendix C: Hybrid norm, reflected energy, and Gram estimate

### Imported sieve hypotheses

The quadratic family is explicitly made unit-invariant and primitive. The cubic sieve’s indexing matches the dual squarefree variables.

### Collision masks

The two Möbius expansions are performed before the corresponding positive estimates. In particular, the pair-dependent masks are not simply dropped inside a signed character sum.

The coefficient-independence conditions needed to apply the two sieves are preserved. The later removal of bounded coefficients occurs only at a positive stage.

### Reflected energy

The source support permits shared primes between the squarefree and cube variables, and the proof retains them.

The small-argument kernel saving is extracted before the row norm is squared. Powerful-row counting contributes its exponent once. Growing fourth-power and puncture labels remain explicit rather than entering a supposedly fixed arithmetic modulus.

The discarded dual region is treated by a separate absolute lattice tail, not counted at a retained-length cutoff.

### Correlations and Gram estimate

The finite correlation identities include prime powers and zero-extended principal powers.

The artificial extension off the genuine residual-coprime locus is explicitly defined as artificial. The full Möbius indicator is inserted before it is used in a factorized estimate.

The Gram argument separates mean-free frequencies from sixth-power-type frequencies. Its final three terms
\[
1,\qquad P_a^{1/6},\qquad P_a^2/Y'
\]
have distinct justifications. The physical geometry supplies the inequality needed to absorb the third into the second.

---

## Appendix D: Inverse-moment induction

This is an essential proof component, not a routine citation. I checked the following transitions separately.

### Statement and canonical class

The canonical class is restrictive enough for the recursion: it permits product-form slot coefficients, a fixed puncture, and a label-only divisor weight. It does not claim an estimate for arbitrary residual column coefficients.

The two invariants explicitly include the puncture norm.

### Short completion

The cube-factor inversion preserves the whole-index mark. Its central normalization is correct.

The terminal reflected-energy estimate is applied with the actual residual row annulus and actual puncture size. The three energy branches are separately bounded.

### First masked Poisson transform

The primitive character, its conductor, and the complementary zero mask are specified before Poisson summation.

Principal terms are separated and counted directly. The full nonprincipal raw sum is displayed before frequency truncation and off-coprime extension.

### First arithmetic transport

The all-modulus CRT calculation proves the new coefficient identity. The eight-state table is not used as a substitute for that calculation.

The cube-derived factor is retained as
\[
\chi_n(J)^4\,1_{(n,\operatorname{rad}q_0)=1},
\]
with \(J\) still averaged and \(q_0\) treated as a fixed puncture parameter.

### First separation and positive majorant

The outer frequency ball is independent of the live residual columns. Its complement is discarded on the genuine raw expression.

The common Fourier density is chosen before the current rows and labels. Weighted Cauchy precedes the removal of bounded outer coefficients.

The old-label fibre bound removes the old \(f,h\) without counting them again later.

### Second Poisson transform

The common squarefree factor produces exactly the stated mask. The second transform returns the coefficient to the canonical form.

The identity defining \(k_{\rm new}\), \(f_{\rm new}\), and the new puncture retains all zeros.

### Child squarefreeness and independence

The retained common scalar zeros ensure that \(J,C,d_2,v'\) are pairwise coprime on the nonzero support. Hence \(f_{\rm new}\) is genuinely squarefree before the positive enlargement.

The new puncture is fixed after \(\gamma=(q_0,t',r_g)\) is fixed and is independent of the child row and child label.

### Source projections and fibre counts

The projection \(\Gamma_\sigma\) is taken from source witnesses, not replaced by its containing norm balls when checking child admissibility.

The containing balls are used only for counting. The reconstruction weight depends on the child label alone after the fixed triple is separated.

Thus \(J,C,d_2,v'\) are not counted both as external labels and as the new averaged label.

### Exponent and termination

The exact identity
\[
\kappa_i+\lambda_c+C_c+2F_c=F
\]
provides the normalization cancellation.

The clipping loss appears twice where required. The margin losses and strict row decrease are explicit, and the depth is finite.

### Initialization

The overlap decomposition between the inverse polynomial and slot primes preserves squarefreeness and the original slot coefficients. The overlap triangle is taken before the subsequent square.

The initialization has its own puncture check, reconstruction count, and exponent identity. It is not merely asserted to be analogous to the recursion.

### Sixth-power amplification

The mask identity is exact, including shared primes of \(u\) and the amplifier ideal. The map \((u,a)\mapsto ua^6\) is injective with the stated conventions.

The endpoint \(r=1\) is obtained with a fixed strict auxiliary margin, not by taking an unproved limit. The slope remains \(5/6\).

I found no unresolved coefficient-independence, zero-mask, or counting gap in this induction.

---

## Appendix E: Extended plain fourth moment

### Mask deletion and natural reflection

Extra masks are fixed within the row sum. Their deletion is exact and does not replace natural row-dependent zeros by freely chosen punctures.

The conductor-times-redundant-radical bound supplies the needed effective width. Reflection is applied only to nonprincipal inducing characters.

Row-dependent reflected scales are handled through coefficient mass and scale suprema. These suprema are not applied to an exceptional centered difference whose cancellation must remain intact.

### Prime estimate and the \(\kappa\)-range

The prime estimate is valid under the explicitly stated premise when \(\kappa<1\), and absolute counting supplies the \(\kappa=1\) case.

The extension to \(13/18\) is supported by the actual comparison inequalities:
\[
6\kappa-1\ge\frac{10}{3},
\qquad z<\frac M{20}
\]
in the long-input range. The endpoint itself retains strict comparison margins.

### Induction order

Zero-slot bands are completed before positive-slot bands. Within a band, the uncentered range is proved before it is used to estimate a comparison product.

The remaining recursive calls have strictly smaller effective width. This avoids a same-band cycle.

### Centered coefficient

The equal-product-scale subtraction remains one coefficient. Complete extraction updates both rectangles by the same exact extracted norms.

Whole-product Fourier separation introduces one common norm power per side. It does not assign independent powers to the two plain variables.

### First transform and Gauss norm

The allocated convolution coefficients are explicitly defined, including their masks and signed rectangles.

The residual coprimality is removed using the complete Möbius indicator before independent norms are formed. The artificial extension is not presented as a primitive Poisson formula on noncoprime moduli.

### Amplifier

The pool is eventually disjoint from every live slot window. Only the valuations \(1,6,7\) contribute to the difference between the relevant Gauss rows, and their central coefficients give the stated extraction costs.

Amplifier errors are not amplified again.

### Second transform

The genuine complete common support is removed before the correlation is factorized. Shared slot/plain prime powers are therefore accounted for in the common scalar rather than incorrectly left as independent residual factors.

The partitioned scalar is extended by zero outside its genuine partition before being bounded.

### Child coefficient class

The final divisor allocation introduces no puncture on an unrestricted quotient. The old common masks, character, and whole-product norm power survive.

The two sides differ by a member of \(\Theta\), so their exceptional/nonexceptional classification is compatible.

### Nonexceptional children

Triangle inequality is applied to the centered rectangles only in this branch. Each rectangle is clipped separately, with its exact normalization change recorded.

Whole-slot removal occurs once after the actual affine defect has been computed. Its overshoot is at most one slot length, not one loss per removed slot.

### Exceptional rows

The sixth-power-form count uses the original moving support and the forced local valuation classes. It includes rows admitted after positive enlargement.

The uncentered volume bound and the centered cancellation are separate estimates; neither is used outside its appropriate range.

### Masked rectangle cancellation

The main coefficient is independent of both scale and norm-twist height after the divisor extraction. Equal products of scales therefore cancel the two product main terms.

The proof includes an all-scale volume fallback, so a small or empty rectangle is not treated as though the positive lower-length estimate still applied.

### Mesh and height uniformity

The support errors are aggregated before taking exponent tolerances. This is what permits the mesh to be chosen independently of the fixed slot count.

Internal Fourier and seminorm orders are propagated through a finite depth. External tail differentiation does not retrospectively enlarge an internal power of the height.

I found no essential gap in the extension of the plain moment or its use in the row count.

---

## 5. Corrections and clarifications

### 5.1 Definite correction: stale bibliography hash

The `StageOneCertificate` entry in `references.bib` records
```text
9b0743dad938cb5721f9a021dbc8756cd1139ea36a5c7b02ef2c976337183753
```
but the current embedded and executed script has hash
```text
af406d0f43d651838a65c39da9eb69c3837fba72f2ddad7c15adb4dc9bc7711f
```

**Required editorial correction:** update that entry or explicitly label it as a historical certificate revision.

This is not a research-notes snapshot mismatch. Nor is it an essential-certificate gap: the complete current certificate is printed in `answer.tex`, its correct digest is printed there, and the executed file matches it exactly.

### 5.2 Clarification: define \(V_{\rm G}\)

At the first use of \(V_{\rm G}\), it would improve clarity to write explicitly
\[
V_{\rm G}(x)
=\frac1{2\sqrt{\pi}}
  \exp\!\left(-\frac{(\log x)^2}{4}\right),
\qquad
\int_0^\infty V_{\rm G}(x)x^t\,\frac{dx}{x}=e^{t^2}.
\]

The intended function is determined by the already specified Mellin weight \(\Phi(t)=e^{t^2}\), so this is not a missing essential analytic lemma.

### 5.3 Historical receipts

I have not independently remeasured the absent historical reference archive. The document expressly distinguishes those historical receipts from current checks, and no theorem is deduced from a matching historical hash.

---

## 6. Final determination

The submission meets the substantive requirements:

- It proves a rational boundary strictly below the stage incumbent.
- The metadata agrees with the theorem.
- The argument is for the entire required Dirichlet family.
- Principal poles, imprimitive Euler factors, real zeros, and all heights are handled.
- The necessary Hecke family is retained.
- The moment hypotheses are discharged, not assumed.
- The continuous optimization certificate is exact.
- The remaining optimization questions are not unresolved premises of the theorem.
- The complete document compiles within the required formatting and page limit.

The stale bibliography hash should be corrected, but it does not affect mathematical readiness.

<research_notes_status>verified</research_notes_status>