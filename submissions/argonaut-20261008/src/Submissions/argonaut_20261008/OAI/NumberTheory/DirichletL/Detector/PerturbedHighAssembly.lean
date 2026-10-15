import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedCentralMomentJoin
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedFloorRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.CentralSupportedSplit

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set

namespace SevenEighths.PerturbedHighAssembly

open HeckeFamily ProbePhysical ProbeMellinBoundary
open HeckeInverseAmplification hiding PrimeIdeal
open ProbeRaySlots
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
open SevenEighths.ProbeHighRowFamily SevenEighths.ProbeFinalAssembly
open SevenEighths.PerturbedCentral SevenEighths.PerturbedCountBridge
open SevenEighths.PerturbedCountProjection
open SevenEighths.PerturbedMomentConstruction
open SevenEighths.PerturbedSameDataCentral
open SevenEighths.PerturbedFloorRows
open SevenEighths.HighFrontierTargets hiding totalE
open SevenEighths.Parameters

local notation "O" => HeckeFamily.O

private theorem transportPoolOutside
    {M : Ideal O} (H : Subgroup (O ⧸ M)ˣ)
    (S : Finset (Ideal O)) (N : ℕ) (a b : ℝ) (Y : Fin N → ℝ) :
    ∀j P, P ∈ pool (RayQuotient.identityClass M H) S a b (Y j) → P.val ∉ S :=
  fun j P hP => (mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

/-!
# Exact remaining transport output

This is the row-labelled conclusion needed from the canonical/Euler side.  It
uses the already fixed `F.S`, modulus, window, total mass and shifted powers.
It is deliberately a proposition, not an assumption field of `D` or `F`.
-/

def SameDataTransportAt
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (theta : ℝ) : Prop :=
  letI : NeZero (∏P∈F.S, P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  ∃n : ℕ, 0 < n ∧ ∀eta : Character, ∃Ct : ℝ, 0 < Ct ∧ ∀ᶠZ : ℝ in atTop,
    let Y : Fin D.N → ℝ := fun j => Z ^ (D.ell j)
    let T : Fin D.N → Finset PrimeIdeal := fun j =>
      pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
    let hT := transportPoolOutside (M := F.modulus) (⊤) F.S D.N 1 2 Y
    let normer := sourceResidueConstant F.W F.W (∏P∈F.S, P) *
      (Probe.principalScalar Finset.univ Z totalE
        (slotMass T (residueWeights (fun _ => F.w) Y)) : ℂ)
    normer ≠ 0 ∧ ∃idx grid : FreeRow → ℕ,
    (∀u, 1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49 / 100 : ℝ) / D.e⌋₊ ∧
      ((3 * idx u + 1 : ℕ) : ℝ) * Z ^ theta + Z ^ theta / 2 ≤
        (3 * idx u + 2 : ℕ) * Z ^ theta) ∧
    (∀u, let alpha : ℝ := 51 / 100 + D.e * grid u
      (51 / 100 : ℝ) ≤ alpha ∧ alpha ≤ 1 ∧
      alpha ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime eta u
          (rayCubeFamily F.modulus ⊤ le_top u))
        (3 * idx u * Z ^ theta) ∧
      detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime eta u
          (rayCubeFamily F.modulus ⊤ le_top u))
        (3 * idx u * Z ^ theta) < alpha + D.e ∧
      detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime eta u
          (rayCubeFamily F.modulus ⊤ le_top u))
        (3 * (idx u + 1 : ℕ) * Z ^ theta) < alpha + 2 * D.e ∧
      ((51 / 100 : ℝ) < alpha → ∃j s,
        LFunction
          (sourceDetectorFamily F.S F.exclusions.prime eta u
            (rayCubeFamily F.modulus ⊤ le_top u) j) s = 0 ∧
        ¬((sourceDetectorFamily F.S F.exclusions.prime eta u
            (rayCubeFamily F.modulus ⊤ le_top u) j).residue = 1 ∧ s = 1) ∧
        alpha ≤ s.re ∧ s.re < alpha + D.e ∧
        |s.im| ≤ 3 * idx u * Z ^ theta)) ∧
    (∀u∈rowBand (Z ^ (1 / 100 : ℝ)) (Z ^ (physicalHeight + D.t)),
      (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 →
      (∀chi, (rayCubeFamily F.modulus ⊤ le_top u chi).residue ≠ 1) ∧
      (∀chi, (rayCubeFamily F.modulus ⊤ le_top u chi).modulus.absNorm ≤
        conductorConstant * F.modulus.absNorm *
          (Ideal.span {u.val} : Ideal O).absNorm) ∧
      ∀hnp : ∀chi, (rayCubeFamily F.modulus ⊤ le_top u chi).residue ≠ 1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily F.modulus ⊤ le_top u) hnp
          (3 * (idx u + 1 : ℕ) * Z ^ theta) <
            51 / 100 + D.e * grid u + 2 * D.e) ∧
    let rows := rowBand (Z ^ (1 / 100 : ℝ)) (Z ^ (physicalHeight + D.t))
    let alpha : FreeRow → ℝ := fun u => 51 / 100 + D.e * grid u
    let height : FreeRow → ℝ := fun u => (3 * idx u + 1 : ℕ) * Z ^ theta
    ‖HighFrontierTargets.normalizedProbeAt F.modulus ⊤ F.S F.exclusions
        F.maximal D.ell 1 2 (fun _ => F.w) F.W F.W totalE sourceLx sourceLy eta Z -
      HeckeSignal.signal (eta.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection eta F.S) (-11 / 16) Z -
      finiteCentralCubeRows F.S F.exclusions F.maximal eta rows T hT
        (fun _ y => (F.w y : ℂ)) Y F.W F.W
        (Z ^ sourceLx) (Z ^ sourceLy) Z D.e alpha height / normer‖ ≤
      Ct * Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma)

/-!
## Physical high bridge

All floor and nonfloor estimates are now genuine theorems.  The sole analytic
input below is `SameDataTransportAt`, whose production is exactly the remaining
canonical/Euler handoff.
-/

theorem highProbeOutputAt_of_same_data_transport
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
    (htransport : SameDataTransportAt D hfine F theta) :
    HighFrontierTargets.HighProbeOutputAt F.modulus ⊤ le_top F.S F.exclusions
      F.maximal D.ell (fun _ => F.w) F.W F.W
      (1 / 200) (7 / 8) 1 2 D.ε D.t D.t D.t
      HighFrontierTargets.positiveGap D.t wide.toCountParameters
      totalE sourceLx sourceLy theta D.t D.eps D.sigma := by
  letI : NeZero (∏P∈F.S, P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  obtain ⟨n, hn, htransport⟩ := htransport
  have hfloor := same_data_floor_rows D hfine F hbeta htheta hthetad
    hthetacost hthetaeps n
  have hnonfloor := same_data_nonfloor_rows D hfine F wide
    (by simpa only [boundary, rho0, HighFrontierTargets.sigmaBoundary,
      HighFrontierTargets.rho] using hbeta)
    htheta hthetad hthetacost htheta2 hthetaeps n ⌊(49 / 100 : ℝ) / D.e⌋₊
  obtain ⟨Cf, hCf, hfloor⟩ := hfloor
  obtain ⟨Cn, hCn, hnonfloor⟩ := hnonfloor
  unfold HighFrontierTargets.HighProbeOutputAt
  refine ⟨Cn, hCn, ?_⟩
  intro eta
  obtain ⟨Ct0, hCt0, htransportEta⟩ := htransport eta
  let Ct : ℝ := Ct0 + Cf * (eta.modulus.absNorm : ℝ) ^ (2 * D.eps)
  have hCt : 0 < Ct := by dsimp [Ct]; positivity
  refine ⟨Ct, hCt, ?_⟩
  filter_upwards [htransportEta, hfloor eta, hnonfloor eta,
    ProbeHighRowFamily.sourceDyad_geometry_eventually
      (1 / 200) (7 / 8) D.t (physicalHeight + D.t)
      (by norm_num) (by norm_num) D.t_pos
      (SevenEighths.PerturbedSameDataCentral.same_D_conductor D),
    eventually_external_height_le_moment_height n htheta,
    eventually_ge_atTop (1 : ℝ)] with Z htransportZ hfloorZ hnonfloorZ hgeo hheight hZ
  intro C0 hC0 hsource
  dsimp only at htransportZ
  obtain ⟨hnormer, idx, grid, hidx, hbins, hray, herror⟩ := htransportZ
  let Y : Fin D.N → ℝ := fun j => Z ^ (D.ell j)
  let T : Fin D.N → Finset PrimeIdeal := fun j =>
    pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
  let hT := transportPoolOutside (M := F.modulus) (⊤) F.S D.N 1 2 Y
  let normer := sourceResidueConstant F.W F.W (∏P∈F.S, P) *
    (Probe.principalScalar Finset.univ Z totalE
      (slotMass T (residueWeights (fun _ => F.w) Y)) : ℂ)
  let rows := rowBand (Z ^ (1 / 100 : ℝ)) (Z ^ (physicalHeight + D.t))
  let floors := supportedFloorRows F.S F.maximal rows grid
  let nonfloors := supportedNonfloorRows F.S F.maximal rows grid
  let alpha : FreeRow → ℝ := fun u => 51 / 100 + D.e * grid u
  let height : FreeRow → ℝ := fun u => (3 * idx u + 1 : ℕ) * Z ^ theta
  have hrowsFloor : ∀u∈floors,
      u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
      rowNorm u ≤ Z ^ (physicalHeight + D.t) := by
    intro u hu
    have hm := (mem_supportedFloorRows F.S F.maximal rows grid u).mp hu
    have hr := mem_rowBand.mp hm.1
    exact ⟨hr.1, hr.2.1, hm.2.1, hr.2.2.le⟩
  have hrowsNonfloor : ∀u∈nonfloors,
      u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
      rowNorm u ≤ Z ^ (physicalHeight + D.t) := by
    intro u hu
    have hm := (mem_supportedNonfloorRows F.S F.maximal rows grid u).mp hu
    have hr := mem_rowBand.mp hm.1
    exact ⟨hr.1, hr.2.1, hm.2.1, hr.2.2.le⟩
  have hfloorIdx : ∀u∈floors, idx u ≤ n := fun u _ => (hidx u).2.1
  have hfloorBin : ∀u∈floors, detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime eta u
        (rayCubeFamily F.modulus ⊤ le_top u))
      (3 * (idx u + 1 : ℕ) * Z ^ theta) < 51 / 100 + 2 * D.e := by
    intro u hu
    have hg := ((mem_supportedFloorRows F.S F.maximal rows grid u).mp hu).2.2
    have hh := (hbins u).2.2.2.2.1
    simpa only [hg, Nat.cast_zero, mul_zero, add_zero] using hh
  have hfloorBound := (hfloorZ floors hrowsFloor idx hfloorIdx hfloorBin).2
  have hnonLabels : ∀u∈nonfloors,
      idx u ≤ n ∧ grid u ≤ ⌊(49 / 100 : ℝ) / D.e⌋₊ ∧ grid u ≠ 0 ∧
        51 / 100 + D.e * grid u ≤ 1 := by
    intro u hu
    have hg := ((mem_supportedNonfloorRows F.S F.maximal rows grid u).mp hu).2.2
    exact ⟨(hidx u).2.1, (hidx u).2.2.1, hg, (hbins u).2.1⟩
  have hnonNext : ∀u∈nonfloors, detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime eta u
        (rayCubeFamily F.modulus ⊤ le_top u))
      (3 * (idx u + 1 : ℕ) * Z ^ theta) <
        51 / 100 + D.e * grid u + 2 * D.e :=
    fun u _ => (hbins u).2.2.2.2.1
  have hnonCurrent : ∀u∈nonfloors,
      51 / 100 + D.e * grid u ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime eta u
          (rayCubeFamily F.modulus ⊤ le_top u))
        ((3 * idx u : ℕ) * Z ^ theta) :=
    fun u _ => by simpa only [Nat.cast_mul, Nat.cast_ofNat] using (hbins u).2.2.1
  have hmom :
      ∀k∈smallDyadicIndices (Z ^ (physicalHeight + D.t)),
        ∀i∈Finset.range (n + 1),
        ∀j∈Finset.range (⌊(49 / 100 : ℝ) / D.e⌋₊ + 1),
        let rows' := cubeBinRows (nonfloors ∩ dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z ^ theta ∧
            |t.2| ≤ (3 * i + 1 : ℕ) * Z ^ theta) ∧
          |t.1.2| ≤ (3 * i + 1 : ℕ) * Z ^ theta) →
        SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime eta rows'
          D.ell (fun _ y => (F.w y : ℂ)) Z
          (sourceDyadConductor Z D.t k) (51 / 100 + D.e * j)
          D.ε theta (7 / 8) 2 D.t D.t i
          ((17 / 50 : ℂ) + t.1.2 * Complex.I)
          (deltaGap HeckeZeroSupremum.beta)
          (if 2 * (51 / 100 + D.e * j) - 1 ≤ 5 / 6 then wide.cB else wide.cH)
          (if 2 * (51 / 100 + D.e * j) - 1 ≤ 5 / 6 then wide.kB else wide.kH)
          (C0 * Z ^ D.t) (Z ^ (2 * theta)) D.t := by
    intro k hk i hi j hj
    dsimp only
    intro hne t ht
    let Rk := nonfloors ∩ dyadicRows 1 k
    let Rij := cubeBinRows Rk idx grid i j
    have hsubk : Rij ⊆ Rk := Finset.filter_subset _ _
    have hsub : Rij ⊆ nonfloors := hsubk.trans Finset.inter_subset_left
    have hgeo' := hgeo nonfloors
      (fun u hu => ⟨(hrowsNonfloor u hu).1, (hrowsNonfloor u hu).2.1,
        (hrowsNonfloor u hu).2.2.2⟩) k (hne.mono hsubk)
    obtain ⟨u0, hu0⟩ := hne
    have huj : grid u0 = j := ((mem_cubeBinRows Rk idx grid i j u0).mp hu0).2.2
    have hju : j ≠ 0 := huj ▸ (hnonLabels u0 (hsub hu0)).2.2.1
    have ha : (51 / 100 : ℝ) < 51 / 100 + D.e * j := by
      have hjpos : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hju
      nlinarith [D.e_pos]
    have ha1 : 51 / 100 + D.e * j ≤ 1 := by
      simpa only [huj] using (hnonLabels u0 (hsub hu0)).2.2.2
    have hrows' : ∀u∈Rij,
        u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
          (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
          rowNorm u ≤ Z ^ (sourceDyadConductor Z D.t k - D.t) := by
      intro u hu
      exact ⟨(hrowsNonfloor u (hsub hu)).1,
        (hrowsNonfloor u (hsub hu)).2.1,
        (hrowsNonfloor u (hsub hu)).2.2.1,
        hgeo'.2.2.2.2.2 u (hsubk hu)⟩
    have hile : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have him : |t.1.2| ≤ Z ^ (2 * theta) := ht.2.trans (hheight.2 i hile)
    have hs := hsource Rij (sourceDyadConductor Z D.t k)
      (51 / 100 + D.e * j) hgeo'.2.2.1 hgeo'.2.2.2.1 ha ha1 hrows' i
      ((17 / 50 : ℂ) + t.1.2 * Complex.I) (by simp) (by simpa using him)
    simpa only [HighFrontierTargets.positiveGap,
      HighFrontierTargets.sigmaBoundary, HighFrontierTargets.rho,
      deltaGap, boundary, rho0,
      WideCountParameters.toCountParameters_cB,
      WideCountParameters.toCountParameters_kB,
      WideCountParameters.toCountParameters_cH,
      WideCountParameters.toCountParameters_kH] using hs
  have hnonBound := (hnonfloorZ C0 hC0 nonfloors hrowsNonfloor idx grid
    hnonLabels hnonNext hnonCurrent hmom).2
  have hsplit := finiteCentralCubeRows_supported_split F.S F.exclusions F.maximal eta
    rows T hT (fun _ y => (F.w y : ℂ)) Y F.W F.W
    (Z ^ sourceLx) (Z ^ sourceLy) Z D.e grid height
  rw [hsplit] at herror
  have hwithoutFloor := normalized_nonfloor_error
    (HighFrontierTargets.normalizedProbeAt F.modulus ⊤ F.S F.exclusions
      F.maximal D.ell 1 2 (fun _ => F.w) F.W F.W totalE sourceLx sourceLy eta Z * normer)
    (HeckeSignal.signal (eta.excludePrimes F.S F.exclusions.prime)
      (sourceCorrection eta F.S) (-11 / 16) Z)
    (finiteCentralCubeRows F.S F.exclusions F.maximal eta floors T hT
      (fun _ y => (F.w y : ℂ)) Y F.W F.W
      (Z ^ sourceLx) (Z ^ sourceLy) Z D.e (fun _ => 51 / 100) height)
    (finiteCentralCubeRows F.S F.exclusions F.maximal eta nonfloors T hT
      (fun _ y => (F.w y : ℂ)) Y F.W F.W
      (Z ^ sourceLx) (Z ^ sourceLy) Z D.e alpha height)
    normer
    (Ct0 * Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma))
    (Cf * (eta.modulus.absNorm : ℝ) ^ (2 * D.eps) *
      Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma))
    (by simpa only [mul_div_cancel_right₀ _ hnormer, rows, alpha, height, Y, T, hT, normer] using herror)
    (by simpa only [floors, height, Y, T, hT, normer] using hfloorBound)
  -- Normalization is already inferred in the preceding application.
  change ‖HighFrontierTargets.normalizedProbeAt F.modulus ⊤ F.S F.exclusions
      F.maximal D.ell 1 2 (fun _ => F.w) F.W F.W totalE sourceLx sourceLy eta Z -
    HeckeSignal.signal (eta.excludePrimes F.S F.exclusions.prime)
      (sourceCorrection eta F.S) (-11 / 16) Z‖ ≤ _
  calc
    _ = ‖(HighFrontierTargets.normalizedProbeAt F.modulus ⊤ F.S F.exclusions
        F.maximal D.ell 1 2 (fun _ => F.w) F.W F.W totalE sourceLx sourceLy eta Z -
      HeckeSignal.signal (eta.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection eta F.S) (-11 / 16) Z -
      finiteCentralCubeRows F.S F.exclusions F.maximal eta nonfloors T hT
        (fun _ y => (F.w y : ℂ)) Y F.W F.W
        (Z ^ sourceLx) (Z ^ sourceLy) Z D.e alpha height / normer) +
      finiteCentralCubeRows F.S F.exclusions F.maximal eta nonfloors T hT
        (fun _ y => (F.w y : ℂ)) Y F.W F.W
        (Z ^ sourceLx) (Z ^ sourceLy) Z D.e alpha height / normer‖ := by
          congr 1
          ring
    _ ≤ ‖HighFrontierTargets.normalizedProbeAt F.modulus ⊤ F.S F.exclusions
        F.maximal D.ell 1 2 (fun _ => F.w) F.W F.W totalE sourceLx sourceLy eta Z -
      HeckeSignal.signal (eta.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection eta F.S) (-11 / 16) Z -
      finiteCentralCubeRows F.S F.exclusions F.maximal eta nonfloors T hT
        (fun _ y => (F.w y : ℂ)) Y F.W F.W
        (Z ^ sourceLx) (Z ^ sourceLy) Z D.e alpha height / normer‖ +
      ‖finiteCentralCubeRows F.S F.exclusions F.maximal eta nonfloors T hT
        (fun _ y => (F.w y : ℂ)) Y F.W F.W
        (Z ^ sourceLx) (Z ^ sourceLy) Z D.e alpha height / normer‖ :=
      norm_add_le _ _
    _ ≤ (Ct0 + Cf * (eta.modulus.absNorm : ℝ) ^ (2 * D.eps)) *
        Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma) +
      Cn * C0 * (eta.modulus.absNorm : ℝ) ^ (2 * D.eps) *
        Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma) :=
      by
        have hn : normer ≠ 0 := by simpa only [normer, T, Y] using hnormer
        simpa only [mul_div_cancel_right₀ _ hn, add_mul] using add_le_add hwithoutFloor hnonBound
    _ = (Ct + Cn * C0 * (eta.modulus.absNorm : ℝ) ^ (2 * D.eps)) *
        Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma) := by
      dsimp [Ct]
      ring

end SevenEighths.PerturbedHighAssembly

end

end OAI
