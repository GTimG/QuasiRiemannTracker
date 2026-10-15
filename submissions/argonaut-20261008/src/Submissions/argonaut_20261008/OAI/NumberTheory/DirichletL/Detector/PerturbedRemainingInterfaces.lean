import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedHighAssembly
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedCanonicalFrontier

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set

namespace SevenEighths.PerturbedRemainingInterfaces

open HeckeFamily ProbePhysical ProbeMellinBoundary
open HeckeInverseAmplification hiding PrimeIdeal
open ProbeRaySlots
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
open SevenEighths.ProbeHighRowFamily SevenEighths.ProbeFinalAssembly
open SevenEighths.PerturbedMomentConstruction
open SevenEighths.PerturbedCountBridge
open SevenEighths.PerturbedCountProjection
open SevenEighths.PerturbedCentral
open SevenEighths.PerturbedHighAssembly
open SevenEighths.PerturbedCanonicalFrontier
open SevenEighths.HighFrontierTargets hiding totalE
open SevenEighths.Parameters

local notation "O" => HeckeFamily.O

/-!
# Exact remaining canonical and Euler interfaces

Floor rows, nonfloor rows, Gamma-to-Delta moments, exact height matching and the
physical high assembly have already been proved in the preceding modules.  The
only interfaces below are:

* the First-region canonical-minus-central output;
* the principal/Euler comparison on exactly the same `F.S`, modulus, window,
  shifted powers and total-mass normalizer.

No inhabitant is postulated and no unconditional high theorem is claimed.
-/

/--
Raw Euler handoff.  This is the exact two-error form requested from the
separate kernel/window/remainder producer.  The source `F` is already fixed;
there is no permission to enlarge `S` or choose a second modulus here.
-/
def EulerPrincipalRawAt
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine)) : Prop :=
  letI : NeZero (∏P∈F.S, P) :=
    ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  ∃C : ℝ, 0 < C ∧ ∀eta : Character, ∀ᶠZ : ℝ in atTop,
    let Y : Fin D.N → ℝ := fun j => Z ^ (D.ell j)
    let T : Fin D.N → Finset PrimeIdeal := fun j =>
      pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
    let normer := sourceResidueConstant F.W F.W (∏P∈F.S, P) *
      (Probe.principalScalar Finset.univ Z totalE
        (slotMass T (residueWeights (fun _ => F.w) Y)) : ℂ)
    normer ≠ 0 ∧
    ‖principalPhysicalPool eta F.S T (fun _ y => (F.w y : ℂ)) Y
        F.W F.W (Z ^ sourceLx) (Z ^ sourceLy) Z / normer -
      HeckeSignal.signal (eta.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection eta F.S) (-11 / 16) Z‖ ≤
      C * (Z ^ (HeckeZeroSupremum.beta - 11 / 16 - 17 / 48000 + D.t / 8) +
        Z ^ (HeckeZeroSupremum.beta - 11 / 16 + D.e -
          boundary * ((7 / 8 : ℝ) * D.rmin)))

/-- Saved Euler comparison after paying the same datum's two scalar budgets. -/
def EulerPrincipalComparisonAt
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine)) : Prop :=
  letI : NeZero (∏P∈F.S, P) :=
    ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  ∃C : ℝ, 0 < C ∧ ∀eta : Character, ∀ᶠZ : ℝ in atTop,
    let Y : Fin D.N → ℝ := fun j => Z ^ (D.ell j)
    let T : Fin D.N → Finset PrimeIdeal := fun j =>
      pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
    let normer := sourceResidueConstant F.W F.W (∏P∈F.S, P) *
      (Probe.principalScalar Finset.univ Z totalE
        (slotMass T (residueWeights (fun _ => F.w) Y)) : ℂ)
    normer ≠ 0 ∧
    ‖principalPhysicalPool eta F.S T (fun _ y => (F.w y : ℂ)) Y
        F.W F.W (Z ^ sourceLx) (Z ^ sourceLy) Z / normer -
      HeckeSignal.signal (eta.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection eta F.S) (-11 / 16) Z‖ ≤
      C * Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma)

/-- The same `D.principal_budget` pays the first Euler exponent. -/
lemma same_D_principal_exponent
    {Delta : ℝ} (D : HighDataPerturbed Delta) :
    HeckeZeroSupremum.beta - 11 / 16 - 17 / 48000 + D.t / 8 ≤
      HeckeZeroSupremum.beta - 11 / 16 - D.sigma := by
  linarith [D.principal_budget]

/-- The same boundary-aware window budget pays the second Euler exponent. -/
lemma same_D_window_exponent
    {Delta : ℝ} (D : HighDataPerturbed Delta) :
    HeckeZeroSupremum.beta - 11 / 16 + D.e -
        boundary * ((7 / 8 : ℝ) * D.rmin) ≤
      HeckeZeroSupremum.beta - 11 / 16 - D.sigma := by
  have hwindow : D.sigma + D.e ≤
      boundary * ((7 / 8 : ℝ) * D.rmin) := by
    simpa only [boundary, rho0, perturbedBoundary, perturbedRho]
      using D.window_boundary_budget
  linarith

/-- Convert the exact Euler producer output to the one-saving form. -/
theorem eulerPrincipalComparisonAt_of_raw
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (hraw : EulerPrincipalRawAt D hfine F) :
    EulerPrincipalComparisonAt D hfine F := by
  unfold EulerPrincipalRawAt at hraw
  obtain ⟨C, hC, hraw⟩ := hraw
  unfold EulerPrincipalComparisonAt
  refine ⟨2 * C, by positivity, ?_⟩
  intro eta
  filter_upwards [hraw eta, eventually_ge_atTop (1 : ℝ)] with Z hrawZ hZ
  dsimp only at hrawZ ⊢
  obtain ⟨hnormer, hbound⟩ := hrawZ
  refine ⟨hnormer, hbound.trans ?_⟩
  have h1 : Z ^ (HeckeZeroSupremum.beta - 11 / 16 - 17 / 48000 + D.t / 8) ≤
      Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (same_D_principal_exponent D)
  have h2 : Z ^ (HeckeZeroSupremum.beta - 11 / 16 + D.e -
        boundary * ((7 / 8 : ℝ) * D.rmin)) ≤
      Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (same_D_window_exponent D)
  calc
    C * (Z ^ (HeckeZeroSupremum.beta - 11 / 16 - 17 / 48000 + D.t / 8) +
        Z ^ (HeckeZeroSupremum.beta - 11 / 16 + D.e -
          boundary * ((7 / 8 : ℝ) * D.rmin)))
        ≤ C * (Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma) +
          Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma)) := by gcongr
    _ = (2 * C) * Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma) := by ring

/--
Assemble the exact row-labelled transport from independent canonical and Euler
outputs.  This is only a bridge; it does not assert either input.
-/
theorem same_data_transport_of_canonical_and_euler
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (theta : ℝ)
    (hcanonical : SameDataCanonicalPhysicalAt D hfine F theta)
    (heuler : EulerPrincipalComparisonAt D hfine F) :
    SameDataTransportAt D hfine F theta := by
  letI : NeZero (∏P∈F.S, P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  obtain ⟨n, hn, hcanonical⟩ := hcanonical
  obtain ⟨Ce, hCe, heuler⟩ := heuler
  refine ⟨n, hn, ?_⟩
  intro eta
  obtain ⟨Cc, hCc, hcanonicalEta⟩ := hcanonical eta
  refine ⟨Cc + Ce, add_pos hCc hCe, ?_⟩
  filter_upwards [hcanonicalEta, heuler eta] with Z hcanZ heuZ
  dsimp only at hcanZ heuZ ⊢
  obtain ⟨hnormer, idx, grid, hidx, hbins, hray, hcanBound⟩ := hcanZ
  obtain ⟨_hnormerEuler, heuBound⟩ := heuZ
  refine ⟨hnormer, idx, grid, hidx, hbins, hray, ?_⟩
  let Y : Fin D.N → ℝ := fun j => Z ^ (D.ell j)
  let T : Fin D.N → Finset PrimeIdeal := fun j =>
    pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
  let normer := sourceResidueConstant F.W F.W (∏P∈F.S, P) *
    (Probe.principalScalar Finset.univ Z totalE
      (slotMass T (residueWeights (fun _ => F.w) Y)) : ℂ)
  let rows := rowBand (Z ^ (1 / 100 : ℝ)) (Z ^ (physicalHeight + D.t))
  let alpha : FreeRow → ℝ := fun u => 51 / 100 + D.e * grid u
  let height : FreeRow → ℝ := fun u => (3 * idx u + 1 : ℕ) * Z ^ theta
  change ‖HighFrontierTargets.normalizedProbeAt F.modulus ⊤ F.S F.exclusions
      F.maximal D.ell 1 2 (fun _ => F.w) F.W F.W totalE sourceLx sourceLy eta Z -
    HeckeSignal.signal (eta.excludePrimes F.S F.exclusions.prime)
      (sourceCorrection eta F.S) (-11 / 16) Z -
    finiteCentralCubeRows F.S F.exclusions F.maximal eta rows T
      (fun j P hP => (mem_pool _ F.S 1 2 (Y j) P).mp hP |>.2.2.2)
      (fun _ y => (F.w y : ℂ)) Y F.W F.W
      (Z ^ sourceLx) (Z ^ sourceLy) Z D.e alpha height / normer‖ ≤ _
  calc
    _ = ‖(HighFrontierTargets.normalizedProbeAt F.modulus ⊤ F.S F.exclusions
        F.maximal D.ell 1 2 (fun _ => F.w) F.W F.W totalE sourceLx sourceLy eta Z -
      principalPhysicalPool eta F.S T (fun _ y => (F.w y : ℂ)) Y
        F.W F.W (Z ^ sourceLx) (Z ^ sourceLy) Z / normer -
      finiteCentralCubeRows F.S F.exclusions F.maximal eta rows T
        (fun j P hP => (mem_pool _ F.S 1 2 (Y j) P).mp hP |>.2.2.2)
        (fun _ y => (F.w y : ℂ)) Y F.W F.W
        (Z ^ sourceLx) (Z ^ sourceLy) Z D.e alpha height / normer) +
      (principalPhysicalPool eta F.S T (fun _ y => (F.w y : ℂ)) Y
        F.W F.W (Z ^ sourceLx) (Z ^ sourceLy) Z / normer -
      HeckeSignal.signal (eta.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection eta F.S) (-11 / 16) Z)‖ := by
          congr 1
          ring
    _ ≤ ‖HighFrontierTargets.normalizedProbeAt F.modulus ⊤ F.S F.exclusions
        F.maximal D.ell 1 2 (fun _ => F.w) F.W F.W totalE sourceLx sourceLy eta Z -
      principalPhysicalPool eta F.S T (fun _ y => (F.w y : ℂ)) Y
        F.W F.W (Z ^ sourceLx) (Z ^ sourceLy) Z / normer -
      finiteCentralCubeRows F.S F.exclusions F.maximal eta rows T
        (fun j P hP => (mem_pool _ F.S 1 2 (Y j) P).mp hP |>.2.2.2)
        (fun _ y => (F.w y : ℂ)) Y F.W F.W
        (Z ^ sourceLx) (Z ^ sourceLy) Z D.e alpha height / normer‖ +
      ‖principalPhysicalPool eta F.S T (fun _ y => (F.w y : ℂ)) Y
        F.W F.W (Z ^ sourceLx) (Z ^ sourceLy) Z / normer -
      HeckeSignal.signal (eta.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection eta F.S) (-11 / 16) Z‖ := norm_add_le _ _
    _ ≤ Cc * Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma) +
        Ce * Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma) :=
      add_le_add (by simpa only [Y, T, normer, rows, alpha, height] using hcanBound)
        (by simpa only [Y, T, normer] using heuBound)
    _ = (Cc + Ce) * Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma) := by ring

/-- Precisely the two producer outputs still missing after the independent work. -/
structure RemainingHighInterfaces
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (theta : ℝ) where
  canonicalPhysical : SameDataCanonicalPhysicalAt D hfine F theta
  eulerPrincipalRaw : EulerPrincipalRawAt D hfine F

/--
Conditional bridge from the two remaining owner interfaces to HighProbeOutputAt.
The returned HighProbeOutputAt retains its SourceMomentBoundAt antecedent;
this theorem does not supply that moment witness. Counts, floor and nonfloor
estimates are assembled by the imported high bridge. Actual moment-witness
consumption for the same D/F/counts and chosen height resides in
PerturbedCommonProbeAssembly. This theorem is not an unconditional bound.
-/
theorem highProbeOutputAt_of_remaining_interfaces
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (wide : WideCountParameters.{0, 0, 0, 0} F.modulus ⊤ D.t)
    (hbeta : boundary < HeckeZeroSupremum.beta)
    {theta : ℝ} (htheta : 0 < theta)
    (hthetad : theta < (1 / 200 : ℝ) / 2)
    (hthetacost : 4 * theta < (1 / 200 : ℝ) * D.cost)
    (htheta2 : 2 * theta ≤ D.t)
    (hthetaeps : theta * (2 + 4 * D.eps) < D.t)
    (hremaining : RemainingHighInterfaces D hfine F theta) :
    HighFrontierTargets.HighProbeOutputAt F.modulus ⊤ le_top F.S F.exclusions
      F.maximal D.ell (fun _ => F.w) F.W F.W
      (1 / 200) (7 / 8) 1 2 D.ε D.t D.t D.t
      HighFrontierTargets.positiveGap D.t wide.toCountParameters
      totalE sourceLx sourceLy theta D.t D.eps D.sigma := by
  have heuler := eulerPrincipalComparisonAt_of_raw D hfine F
    hremaining.eulerPrincipalRaw
  have htransport := same_data_transport_of_canonical_and_euler D hfine F theta
    hremaining.canonicalPhysical heuler
  exact highProbeOutputAt_of_same_data_transport D hfine F wide hbeta htheta
    hthetad hthetacost htheta2 hthetaeps htransport

end SevenEighths.PerturbedRemainingInterfaces

end

end OAI
