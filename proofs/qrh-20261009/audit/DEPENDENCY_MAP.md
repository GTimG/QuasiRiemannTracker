# Manuscript-to-Lean proof map

Authoritative manuscript: `inputs/qrh-formalization-handoff-20261009/accepted-answer.tex`, SHA256 `c8b9994d6a55521b53fe4664ba190e46dc0a02f7d85221e25d39efa4dcd34de9`. Inputs, editorial issues and historical embedded source capsules remain unchanged. The three exact final targets pass independent statement parity, source builds and allowed-only transitive axiom checks; see `final-verification.json`.

All local file names below are relative to `formalization/QRH`. Original OpenAI definitions and sources remain at their pinned revision. The proof follows the prompt's shortest-route allowance rather than restating every manuscript lemma.

| Manuscript obligation | Checked formal implementation |
|---|---|
| `thm:main`, all positive-modulus Dirichlet characters | `Nonvanishing.lean`, `QRH.DirichletCharacter.LFunction_ne_zero_of_theta_lt_re`; exact original function and pole exception |
| Zeta corollary | `Nonvanishing.lean` and `ZetaTransfer.lean`; explicit value-at-1 case |
| Finite-order Hecke conclusion over Q(sqrt(-3)) | `Nonvanishing.lean`, `QRH.Hecke.LFunction_ne_zero_of_theta_lt_re`; original `HeckeFamily.Character`/`LFunction`, all characters and original exception |
| Exact geometry, optimized physical scales | `Geometry.lean`: theta, ell, b, lx, ly, h, C; exact rational identities and ledger |
| Continuous exponent inequality and strict slack | `Certificate.lean`, `Adaptive.lean`, `DynamicLoss.lean`, `OtherRanges.lean`; real-domain Bernstein/square proof, exact adaptive crossing, conductor correction and reserves |
| Extended plain moment, κ≥13/18 | `Energy/CertifiedExistence.lean`, `Energy/UniformMoment.lean`; actual analytic successor and width induction, no assumed moment field |
| Reflected and unreflected transport, common coefficients/masks and exceptional cancellation | `PlainReflectionGeometry.lean` and checked `Energy/*` extensions of deleted/live, robust, original/reference and physical stages; original `comparison_same_product`/`normalized_input_difference` cancels before estimates |
| Uniform κ mesh and dynamic κ=2β−1 | `Energy/UniformMesh.lean`, `Energy/UniformMoment.lean`, `Detector/DynamicMomentInput.lean`, `UniformDetectorMoment.lean`; mesh independent of κ/slot count, constants and degree before κ |
| Four detector moment inputs | `Detector/UniformAllMoments.lean`; every original analytic moment field proved |
| Actual detector counts and amplitude classes | `ActualDetectorFiberCount`, `ActualAdaptiveBatchCount`, `ActualSourceCount`, `ActualAmplitudeClassCount`; original masks, profiles, conductors and labels |
| Optimized central exponent and actual Mellin cube | `OptimizedCentralExponent`, `OptimizedMixedSaving`, `ActualCubeArithmeticSaving`, `ActualNonfloorCubeNorm`, `ActualNormalizedNonfloorCube`; actual coefficient sum/common Mellin kernel and nonzero ray normalizer |
| Fine positive distinct slots and order of parameters | `Detector/FineSmallData.lean`, `OptimizedData.lean`, `CompleteNonfloorRowsData.lean`; slots sum to ell, degree fixed before tail parameter |
| Actual optimized low probe | `Detector/LowNormalized.lean`, `ActualOptimizedLow.lean`; reflected penalty absorbed via actual lower product norm; full Gaussian physical sums |
| Floor rows | `PrimeRows/OptimizedCubeFloor*.lean`; dyadic, Mellin, normalized and collected estimates |
| Principal correction and analytic region below θ | `Detector/ExtendedEulerRegion`, `ExtendedGlobal*`, `ExtendedPrincipal*`, `ExtendedFiniteProduct*`; genuine bounds on Re(s)>87/100 for original functions |
| Principal residues and signal identification at optimized shift C(0) | `OptimizedPrincipalRemainders`, `OptimizedPrincipalPhysicalRemainder`, `OptimizedPrincipalSignal`, `OptimizedPrincipalResidueActual`, `OptimizedPrincipalNormalized`; exact original Hecke signal and ray normalization |
| Small and large physical errors and cube transport | `PrimeRows/Optimized*Tail*`, `OptimizedCube*`, `OptimizedCanonical*`, `OptimizedNormalizedTransport*`, `OptimizedNonfloorTransport`; small contour offset 1/200 explicitly budgeted |
| Uniform positive high saving | `Detector/ActualOptimizedHigh.lean`, `exists_actual_optimized_high`: sole hypothesis θ<β; ∃D,S before ∀η, saving D.sigma/8 |
| Mellin continuation and common bound | `Detector/OptimizedContinuation.lean`: actual Hecke signal, regularized L-function, Gaussian multiplier and identity theorem at θ |
| Strict drop of actual zero supremum | `Detector/OptimizedSupremum.lean`, unconditional `OAI.SevenEighths.QRHFinalAssembly.beta_le_theta`; low/high estimates discharged, primitive zero approximating supremum, original finite deletion |
| Norm lift and all-character transfer | Original `Hecke.Dirichlet.LFunction_eq_dirichlet_product`, original Re(s)≥1 nonvanishing, and `Nonvanishing.lean`; no primitive/nonprincipal restriction in final statement |
| Independent statement and soundness checks | Frozen `IndependentTargets.lean`, `StatementParity.lean`, `audit/FinalTargetsRequired.lean`; all three final constants checked at literal θ and allowed-only axioms |

The actual masked moment keeps β≥51/100, fixed-modulus and window hypotheses, and full original coefficient/mask/height gates. The final contradiction β>θ proves this β bound and constructs the required data. Uniform saving is fixed before choosing a character; fixed-character constants may depend on its modulus as allowed. No finite grid or arithmetic certificate substitutes for an analytic estimate.

Standalone parity for all presentations of `lem:plain` is not asserted: finite character combinations, zero-length absorption, all row presentations and β<51/100 are not separately packaged. They are not used as assumptions or required to derive the three completed targets. Optional restricted optimality is outside the required route.

`HeckeFamily.Character.ofResidue` constructs the auxiliary period for any unit-trivial residue character on a nonzero modulus, so the period field does not restrict the intended finite-order family. The original ideal Dirichlet-series and differentiability bridges remain source-identical and have inspected allowed-only axioms. The Hecke L-function is the established continued lattice function divided by 6; it has not been shadowed.

Mathlib's nonzero total-function value `riemannZeta 1 = (γ - log (4π))/2` is separate from the meromorphic pole. The Dirichlet exception is `¬(χ=1 ∧ s=1)`; the Hecke exception is `s≠1 ∨ χ.residue≠1`. Both appear unchanged in the final statements.
