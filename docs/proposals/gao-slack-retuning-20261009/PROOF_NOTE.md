# Candidate slack retuning of the tracker boundary

Date: 2026-10-09. Status: **endpoint and recovery budgets checked; complete source re-instantiation and validation pending**. No Lean or kernel replay, tracker admission, or priority claim is attached to this note.

## Proposition and inputs

Put
\[
\theta_*=
\frac{437478509710049473064301925667}
     {500000000000000000000000000000}
=0.874957019420098946128603851334.
\]
This fraction is reduced. Against Nielstron's pinned boundary
\(\theta_N=874957019420098946128604623/10^{27}\), its exact improvement is
\[
\theta_N-\theta_*=
\frac{385833}{500000000000000000000000000000}
=7.71666\times10^{-25}.
\]

**Conditional retuning criterion.** If the whole masked-moment, physical coefficient, low-probe, principal and transport chain is re-established for the new geometry and budgets below, the original continuation engine gives nonvanishing on \(\Re s>\theta_*\) for the complete finite-order Eisenstein Hecke and Dirichlet families, retaining their original pole exceptions. The new geometry instances of those analytic estimates have not yet been verified. This criterion is not a completed nonvanishing theorem.

The generic analytic methods come from the pinned OpenAI and ProofCouncil/Nielstron sources. Several cited declarations, however, are frozen at the old `QRH.tightTheta`, `ell`, `lx` and `ly`. They cannot be applied directly to the new probe. In particular, the old transport hypothesis \(\theta_N\le\beta\) is not licensed by \(\beta>\theta_*\) when \(\beta\in(\theta_*,\theta_N)\). A complete source re-instantiation must re-prove these new geometry instances; changing numerical wrappers alone does not discharge that obligation. No final nonvanishing theorem or high-probe estimate at the new boundary is being assumed as an already available input.

Pins: tracker `40844a7614b67840801e65b836b3da2e1f7ff029`; its analytic package pins OpenAI/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The [dependency map][map] identifies the analytic source chain. All tracker references below use the first pin, rather than a moving branch.

## Geometry and continuous exponent margin

Use the [existing geometry][geometry], replacing its working threshold by \(\theta_*\):
\[
\ell=11/3-4\theta_*,\quad \kappa_0=2\theta_*-1,
\quad b=-\frac{(3\ell+1)(36\ell^2-75\ell+19)}{3(114\ell^2-159\ell-7)},
\]
\[
l_x=(1-\ell-b)/2,\quad l_y=(1-\ell+b)/2,
\quad h=1-l_x+\ell,\quad C(s)=s+l_x/2-1+h/6.
\]
Use the original Gaussian profile families, calibration, compensation and ray construction, evaluated at the new physical lengths and slot sum. This is a new instance of the canonical probe; its ratios to the old lengths need not stay bounded as the base tends to infinity. Write \(c=1/(3\kappa_0)\),
\[
D(x)=3-(1+2c)x,\quad P(x)=(2-2cx)(1-x),
\quad J(\delta,x)=(5/6-\delta)D(x)+\delta P(x).
\]
Let \(E(\delta,x)\) and \(F(\delta,y)\) be the explicit rational expressions in [Certificate.lean][certificate], evaluated at this geometry. Recompute their coefficients; the old fixed numerical conclusions are not imported.

**New numerical wrapper.** On \(0\le\delta\le5/6\), \(0\le x\le1/2\),
\[
25/39\le J(\delta,x)\le5/2,\qquad
F(\delta,1/2-x)>5\cdot10^{-27},
\quad E(\delta,x)<-2\cdot10^{-27}.
\]
The last inequality follows from the exact identity \(F=-JE\). The middle inequality follows by the same polynomial proof: two positive Bernstein expansions for \(\delta\in[0,1/4]\) and \([1/4,1/3]\), and a square expansion for \(\delta\ge1/3\). Writing \(F(\delta,0)=a_2\delta^2+a_1\delta+a_0\), its recomputed exact square residual is \(D_v=a_0-a_1^2/(4a_2)\), with
\[
D_v=5.0043066545169341331932567411945\ldots\times10^{-27}>5\cdot10^{-27}.
\]
Every Bernstein coefficient exceeds the unchanged floor \(723/10^6\), and all nine shifted higher-\(y\) coefficients remain positive. These are exact rational comparisons; the displayed decimal is descriptive.
The [independent Fraction implementation](certificate.py)
and [stored certificate](certificate.json)
derive the full polynomial, check its square identity and both Bernstein
patches, and reject reusing the old tiny-loss budgets at this endpoint.

The [other-range estimates][ranges] are also rechecked at the new geometry: the high-amplitude saving remains \(7/100\), and the floor exponent remains below \(-1/200\). Also \(\kappa_0\ge13/18\), \(h+\zeta\le17/20\), and
\(l_y/2-(13/75)h-1/50\ge7/100\). Thus the endpoint is the only tiny reserve; no large-amplitude or floor component is dropped.

## Complete loss ledger and parameter order

Use the following **new** budgets throughout the numerical wrappers:

| Quantity | Value |
|---|---:|
| Polynomial margin | \(5\cdot10^{-27}\) |
| Endpoint exponent reserve | \(2\cdot10^{-27}\) |
| Complete central loss allowance | \(10^{-27}\) |
| Outer-row padding \(\zeta\) | \(10^{-29}\) |
| Cap on the positive fine parameter \(t\) | \(10^{-31}\) |

For each contradiction gap \(\Delta=\beta-\theta_*>0\), [FineSmallData.exists_high_data_fine_small][fine] accepts any positive cap. Choose its mesh as \(\min(t,\operatorname{dynamicMesh}(t))/(6\ell)\). Its raw slots sum to \(1/6\); as in [OptimizedData][data], use actual slots \(\ell_j=6\ell\,D.\mathrm{ell}_j\). They are positive and distinct, sum to \(\ell\), and the constructive choice gives \(0<t<10^{-31}\) and
\[
2000\varepsilon\le t,\quad2000e\le t,
\quad(N+8)\mathrm{eps}\le t,\quad0<\sigma\le t.
\]
Slots also satisfy both \(\ell_j\le t/200\) and \(\ell_j\le\operatorname{dynamicMesh}(t)/200\), with the existing positive lower slot bound. The ray modulus, fixed exclusions and coefficients are chosen as in the source construction.

The new wrapper for [OptimizedData.optimized_central_budget][data] is proved directly. After the analytic estimate supplies its degree \(J_0\), `D.height_choice` chooses \(\tau>0\) with \(2\tau(1+J_0)\le t\), and the phase/height gates retained. The complete loss is
\[
\begin{aligned}
L={}&h(159\varepsilon+2t+7t)+2\zeta+3t
 +(26e+(N+8)\mathrm{eps}+t+t\ell)\\
 &+(t+2\tau+2\tau J_0)+\sigma
 \le(18+185/2000)t+2\zeta<19t+2\zeta<10^{-27}.
\end{aligned}
\]
Indeed \((19\cdot10^{-31}+2\cdot10^{-29})/10^{-27}=219/10000\). The margin therefore pays the actual logarithmic, dyadic, conductor, slot, Mellin-height, amplitude-class and normalization losses, as well as a positive saving. No smaller loss is obtained by discarding a recovery term.

For a future formal replay, nine numerical consumer files must receive the new budget: `OptimizedAdaptiveSaving`, `ActualCubeArithmeticSaving`, `ActualNormalizedNonfloorCube`, `OptimizedMixedSaving`, `OptimizedData`, `ActualNonfloorCubeNorm`, `OptimizedTransportBudget`, `CompleteNonfloorCubeData`, and `CompleteNonfloorRowsData`, all under `QRH/Detector/`. Their old literal bounds are not cited as lemmas at the new threshold.

## Analytic source chains still to re-establish

| Contract | Source schema and retained gates; new geometry instance pending where frozen |
|---|---|
| Actual masked plain moment | [QRHPlainMoment.actual_uniform_moment][moment]: \(\kappa\ge13/18\), \(2\beta-1\le\kappa\), \(\beta\ge51/100\); original `PositiveAt`/`ZeroAt`, coefficient, mask, fixed-ray, height and width gates |
| Uniform actual source counts | [actual_uniform_amplitude_class_count][count]: degree before character and height-tail choice; actual detector maxima and amplitude bins, common physical coefficients, arbitrary admissible positive losses |
| Physical coefficient bound | [actual_uniform_cube_class_bound][cube]: complete `cubeArithmeticSum`; it assumes no saving, and supplies its full exponent for subsequent numerical budgeting |
| Any positive fine cap | [exists_high_data_fine_small][fine]; bound and slot mesh are inputs, not fixed \(10^{-28}\) quantities |
| Complete physical transport | [actual_nonfloor_probe_transport][transport]: \(0<\zeta\le1/48\), original masks, support, phase/height gates, all floors and dyadic rows; fixed reserves \(1/200\), \(1/3000\) remain |
| Principal correction | [sourceCorrection_differentiable and sourceCorrection_bound][principal]: analyticity and \(|H(s)-1|\le1/2\) on \(\Re s>87/100\), hence at the new continuation boundary |
| Actual low probe | [original_normalized_compensatedPhysicalProbe_low_optimized][low]: same compensated physical probe and nonzero ray normalizer; arbitrary positive low loss; re-evaluate its algebraic geometry at \(\theta_*\) |
| Principal signal recovery | [actual_ray_principal_comparison][comparison]: exact excluded-character signal, residue constant and \(C(0)\); its \((87/100)\ell_{\min}\) error is retained |
| Signal identity and continuation | [signalMellin_eq_amplitude][signal] and the proof in [nonzero_of_probe_bounds][continuation]: genuine reciprocal L-signal, Gaussian multiplier, regularizer and principal pole exception |

The frozen count, low, principal and transport chains all need re-instantiation, not just the nine numerical consumer files. Their old source snapshots remain immutable. In the new cohort, changing the working geometry also changes the meaning of dependent alias-based declarations even where their text is unchanged; new explicit-literal targets are required. The original L-functions, character quantifiers and pole predicates must remain source-identical.

Here \(\beta\) is the original supremum of nontrivial Hecke-zero real parts, not a new zero bound assumed as input. Under \(\beta>\theta_*\), \(\beta\ge51/100\) automatically and \(\Delta\le(1-\kappa_0)/2\). Set the moment's dynamic \(\kappa=\kappa_0+2\Delta=2\beta-1\). Its uniform mesh is independent of \(\kappa\) and of the finite coefficient index type. Degrees and fixed data precede characters/tails as required; constants may depend on the fixed character modulus as in the original estimates.

After re-establishing the new geometry instances of these contracts, the exponent and loss wrappers and the principal/floor/transport bounds would construct the corresponding normalized physical probe \(\mathcal J_\eta(Z)\) with
\[
\mathcal J_\eta(Z)=O(Z^{C(\theta_*)+\omega}),\qquad
\mathcal J_\eta(Z)-\mathrm{signal}_\eta(Z)
=O(Z^{C(\beta)-\sigma/8})
\]
for \(0<\omega<\beta-\theta_*\). These are the required whole-source conclusions; their complete derivation at the new geometry remains to be verified. With \(\omega=(\beta-\theta_*)/2\), the signal identity and Mellin continuation contradict a primitive zero approaching \(\beta\). Finite Euler deletion preserves its zero and principal status. Thus \(\beta\le\theta_*\); the original norm-lift product then transfers the result to every positive-modulus Dirichlet character.

The full finite-order Hecke family is retained, including imprimitive characters and literal natural zeros. Hecke excludes precisely the principal pole case \(s=1\); Dirichlet retains \(\neg(\chi=1\land s=1)\). The classical zeta assertion concerns its meromorphic continuation away from its pole; Mathlib's assigned total-function value at 1 is a separate convention.

## What is and is not established

The 22 exact arithmetic checks cover this rational geometry, continuous polynomial representation and fixed reserves. They do not certify analytic inequalities. Earlier internal review checked numerical retuning and proposed assembly contracts, but did not re-establish all frozen analytic APIs for the new geometry. Follow-up source review identified that gap. A copied full proof-source cohort is now being prepared; no new geometry instance has been typechecked or kernel-replayed, and the complete theorem remains unproved here. This is numerical slack recovery, with no new arithmetic estimate, independent verification, or priority determination.

The [endpoint obstruction][barrier] for this particular model remains: \(657\ell^3-954\ell^2+21\ell+20=0\) gives the limiting boundary
\(0.8749570194200989461286038505614529823071518741876328\ldots\). The tracker is only \(7.72438547\ldots\times10^{-25}\) above it. This is not a barrier for other proofs; a meaningful next improvement must change an analytic estimate or the probe architecture.

[map]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/qrh-20261009/audit/DEPENDENCY_MAP.md
[geometry]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/compressed/formalization/QRH/Geometry.lean
[certificate]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/compressed/formalization/QRH/Certificate.lean
[ranges]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/compressed/formalization/QRH/OtherRanges.lean
[fine]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/compressed/formalization/QRH/Detector/FineSmallData.lean
[data]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/compressed/formalization/QRH/Detector/OptimizedData.lean
[moment]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/compressed/formalization/QRH/Energy/UniformMoment.lean
[count]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/compressed/formalization/QRH/Detector/ActualAmplitudeClassCount.lean
[cube]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/compressed/formalization/QRH/Detector/ActualCubeClassBound.lean
[transport]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/compressed/formalization/QRH/PrimeRows/OptimizedNonfloorTransport.lean
[principal]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/compressed/formalization/QRH/Detector/OptimizedPrincipalSignal.lean
[low]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/compressed/formalization/QRH/Detector/LowNormalized.lean
[comparison]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/compressed/formalization/QRH/Detector/OptimizedPrincipalNormalized.lean
[signal]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL/Hecke/SignalIdentity.lean
[continuation]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/compressed/formalization/QRH/Detector/OptimizedContinuation.lean
[barrier]: https://github.com/GTimG/QuasiRiemannTracker/blob/40844a7614b67840801e65b836b3da2e1f7ff029/proofs/nielstron-20261009-tightening/tightening/research/Barrier.lean
