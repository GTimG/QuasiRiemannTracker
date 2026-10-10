# Manual review of the retuned source chain

Date: 2026-10-10. **Source-contract review; not a compiled or independently
verified nonvanishing theorem.** No Lean or kernel was run.

The candidate is `437478509710049473064301925667/(5*10^29)`.
The input pin, complete source hashes and reproducible overlay are in the
[source packet](README.md). This review uses the generated candidate,
not the incumbent's compiled declarations. An unchanged proof text can
have a different statement after its geometry dependency changes.

## What the review covers

Three internal, model-assisted source reviews examined the low/reflection branch,
the actual moment/count/cube branch, and the principal/transport/
continuation/family-transfer branch. None found a violated listed gate
or a new nonvanishing assumption. This does not independently validate
every underlying generic analytic proof or elaborate the 207 modules.

Source paths below are relative to the generated `formalization/QRH/`.
They identify declarations for inspection, rather than checked binaries.

| Chain | Source evidence | Required new-instance checks |
|---|---|---|
| Low reflected energy | `Reflection/LowOriginalEnergy:44`, `LowCompletedRows:45`, `Detector/LowReflectedLength:24` | `ell` and mass bounds, `M+ell=1`; retain the actual puncture lists and reflected penalty |
| Low physical scales | `Detector/LowSourceScales:103`, `LowGaussianRemote:30`, `LowCentralTuple:69` | `b>0`, `2lx-ly>ell`, `lx>ell`, `ly>=lx`, `ly<1` |
| Low normalization | `Detector/LowWindowBound:52`, `LowNormalized:60` | Arbitrary positive loss, split between the raw probe and nonzero ray normalizer |
| Actual moments | `Energy/UniformMoment:21`, `Detector/UniformAllMoments:25` | `kappa>=13/18`, `2beta-1<=kappa`, `beta>=51/100`; all four actual moment fields |
| Slot supply and crossing | `Detector/OptimizedBatchWidths:9`, `Hecke/DynamicCrossing:27` | `ell>=1/6`, `4/9<=c<=6/13`, positive common mesh and fine distinct slots |
| Actual counts and cube | `Detector/ActualAmplitudeClassCount:52`, `ActualCubeClassBound:54` | Detector/phase budgets, degree-before-height order, all log, height, modulus and coefficient costs |
| Fresh source data | `Detector/CompleteNonfloorCubeData:50` | Construct `SourceData D` after the new small parameters; retain `FirstTail(4e)` |
| Principal recovery | `Detector/OptimizedPrincipalRemainders:590`, `OptimizedPrincipalNormalized:44` | Both contour remainders and both normalized errors retained |
| Complete physical transport | `PrimeRows/OptimizedNonfloorTransport:81`, `Detector/OptimizedTransportBudget:12` | Floors, nonfloor rows and tails; fixed reserves `1/200`, `1/3000` and the conductor cap |
| Supremum and family transfer | `Detector/OptimizedSupremum:13`, `OptimizedContinuation:21`, `TighterNonvanishing:19` | Same reciprocal signal and correction; all original characters and principal-pole exceptions |

## Exact geometry checks

The rational [certificate](certificate.py)
now checks 34 conditions. Its original 22 endpoint/range checks are
supplemented by the following source-level geometry obligations:

\[
\theta_*>87/100,\qquad 2/5\le l_y<1,\qquad
l_x>\ell,\qquad 2l_x-l_y>\ell,\qquad l_y\ge l_x,
\]
\[
M+\ell=1,\qquad l_x+b/6=2C(\theta_*),\qquad C(\theta_*)>0,
\]
and the signs of the certificate denominators. The two principal
contour reserves are also checked exactly:

\[
\frac{l_y}{20}-\frac{1+h}{1000}-\frac1{3000}>0,
\qquad
\frac h{600}-\frac1{1000}-\frac1{3000}>0.
\]

These inequalities close the listed arithmetic gates; they do not
turn an endpoint certificate into an analytic proof.

## Parameter and source order

Under the contradiction `beta>theta*`, put `Delta=beta-theta*` and
`kappa=kappa0+2Delta=2beta-1`. This proves the moment premises and
does not assume the desired strip. The small detector parameter
`D.kappa` is distinct from this moment exponent.

Choose `D` with `0<t<10^-31`, then construct its finite exclusion set
and modulus. The incumbent's concrete set need not satisfy
`FirstTail(4e)` for the new `e`; it must not be reused without proof.
The candidate calls `exists_source_data D`; its [pinned constructor](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL/Detector/FinalAssemblyData.lean)
uses [finite source existence for every positive `e`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/NumberTheory/DirichletL/ParametersFixedSource.lean).
These data precede the
character and the large base, so their costs are fixed constants,
with finite Euler deletion and principal status retained in recovery.
After the analytic degree is supplied, choose the height using
`D.height_choice`. The old height cannot be kept merely because the
change in endpoint is small.

The available slot supply is at least `7/37`, from `d<=37/42` and
`ell>=1/6`. It is **not** uniformly greater than `1/5` over
`d<=7/8`. The proofs retain the smaller bound they actually require.

The low branch carries energy loss `507 epsilon`, its square-root
and Gram losses, then Gaussian dyad recovery. Choosing
`epsilon=min(loss/512,1/2)` pays it; the final normalizer receives
the other half of the chosen low loss. The high branch retains
`logCost+heightCost*(1+J)`, the complete coefficient losses,
the modulus factor and both principal comparison errors.
The new central allowance remains `10^-27`; none of those terms
is replaced by zero.

## Remaining verification

The source overlay and manual gate review remove the proposed
shortcut of applying an old frozen API to a new probe. They have not
established a new accepted strip. The whole retuned cohort still
requires validation against its pinned external dependencies,
the literal independent full-family targets, allowed transitive
axioms and the independent kernels. No incumbent QRH compiled
library can certify the changed geometry. No new arithmetic engine,
registry theorem or verified tracker record is promoted here.
