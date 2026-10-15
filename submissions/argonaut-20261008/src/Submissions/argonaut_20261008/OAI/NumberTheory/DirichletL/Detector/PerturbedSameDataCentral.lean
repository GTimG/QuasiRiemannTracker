import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedJointSource
import Submissions.argonaut_20261008.PerturbedCentralBridge

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set

namespace SevenEighths.PerturbedSameDataCentral

open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison
open ProbePrincipalResidueActual
open SevenEighths.ProbeHighRowFamily SevenEighths.ProbeFinalAssembly
open SevenEighths.PerturbedCentral SevenEighths.PerturbedCountBridge
open SevenEighths.PerturbedCountProjection
open SevenEighths.PerturbedMomentConstruction
open SevenEighths.HighFrontierTargets
open SevenEighths.Parameters

local notation "O" => HeckeFamily.O

/-! ## Exact height matching -/

/--
For fixed terminal index cap `n`, every actual external height
`(3*i+1) Z^theta`, `i <= n`, is eventually contained in the moment interval
of height `Z^(2*theta)`.
-/
theorem eventually_external_height_le_moment_height
    (n : ℕ) {theta : ℝ} (htheta : 0 < theta) :
    ∀ᶠZ : ℝ in atTop,
      1 ≤ Z ∧ ∀i : ℕ, i ≤ n →
        ((3 * i + 1 : ℕ) : ℝ) * Z ^ theta ≤ Z ^ (2 * theta) := by
  filter_upwards [
      (tendsto_rpow_atTop htheta).eventually
        (eventually_ge_atTop (((3 * n + 1 : ℕ) : ℝ))),
      eventually_ge_atTop (1 : ℝ)] with Z hlarge hZ
  refine ⟨hZ, ?_⟩
  intro i hi
  have hcoeff : (((3 * i + 1 : ℕ) : ℝ)) ≤ (((3 * n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 3 * i + 1 ≤ 3 * n + 1)
  have hcoeff' : (((3 * i + 1 : ℕ) : ℝ)) ≤ Z ^ theta :=
    hcoeff.trans hlarge
  have hpow0 : 0 ≤ Z ^ theta := Real.rpow_nonneg (zero_le_one.trans hZ) _
  calc
    (((3 * i + 1 : ℕ) : ℝ)) * Z ^ theta
        ≤ (Z ^ theta) * (Z ^ theta) :=
      mul_le_mul_of_nonneg_right hcoeff' hpow0
    _ = Z ^ (2 * theta) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hZ)]
      congr 1
      ring

/-- Supply one actual central cell from the global moment capsule. -/
theorem sourceMomentBoundAt_external_cell
    {N : ℕ} {M : Ideal O} [NeZero M] [Finite (O ⧸ M)]
    {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
    {S : Finset (Ideal O)} {hS : SourceExclusions S}
    {hmax : ∀P∈S, P.IsMaximal} {ell : Fin N → ℝ}
    {W : Fin N → ℝ → ℝ}
    {dmin dmax b epsilon rowMargin slotMesh binWidth gamma epsilonM : ℝ}
    {counts : CountParameters M H epsilonM} {eta : Character}
    {Z theta C : ℝ} {n i : ℕ}
    (hbound : SourceMomentBoundAt M H hH S hS hmax ell W
      dmin dmax b epsilon rowMargin slotMesh binWidth gamma epsilonM
      counts eta Z theta C (Z ^ (2 * theta)))
    (henvelope : ∀j : ℕ, j ≤ n →
      (((3 * j + 1 : ℕ) : ℝ)) * Z ^ theta ≤ Z ^ (2 * theta))
    (hi : i ≤ n) (t : ℝ)
    (ht : |t| ≤ ((3 * i + 1 : ℕ) : ℝ) * Z ^ theta)
    (rows : Finset FreeRow) (d a : ℝ)
    (hdmin : dmin ≤ d) (hdmax : d ≤ dmax)
    (ha : (51 / 100 : ℝ) < a) (ha1 : a ≤ 1)
    (hrows : ∀u∈rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val ≠ 0 ∧
      rowNorm u ≤ Z ^ (d - rowMargin)) :
    SourceMomentsAt M H hH S hS.prime eta rows ell
      (fun j y => (W j y : ℂ)) Z d a epsilon theta dmax b
      slotMesh binWidth i ((17 / 50 : ℂ) + t * Complex.I) gamma
      (if 2 * a - 1 ≤ 5 / 6 then counts.cB else counts.cH)
      (if 2 * a - 1 ≤ 5 / 6 then counts.kB else counts.kH)
      C (Z ^ (2 * theta)) epsilonM := by
  apply hbound rows d a hdmin hdmax ha ha1 hrows i
    ((17 / 50 : ℂ) + t * Complex.I)
  · simp
  · have hti : |t| ≤ Z ^ (2 * theta) := ht.trans (henvelope i hi)
    simpa using hti

/-! ## Scalar premises extracted from one and the same f630 datum -/

lemma same_D_overhead_le_three_t
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    {theta : ℝ} (htheta2 : 2 * theta ≤ D.t) :
    D.t + 2 * theta + D.t ≤ 3 * D.t := by
  linarith

lemma same_D_central_hfinal
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    {theta : ℝ} (htheta2 : 2 * theta ≤ D.t) :
    PerturbedCentral.physicalHeight *
        (159 * D.ε + D.t + D.t + 7 * D.t) +
      2 * D.t + (3 / 2) * (2 * D.t) +
      (26 * D.e + (D.N + 8) * D.eps + D.t +
        PerturbedCentral.totalE * D.t) +
      (D.t + 2 * theta + D.t) + D.t +
        15 * PerturbedCentral.rho0 / 8 ≤ 49 / 440640 := by
  have hnew :
      PerturbedCentral.physicalHeight *
          (159 * D.ε + D.t + D.t + 7 * D.t) +
        2 * D.t + (3 / 2) * (2 * D.t) +
        (26 * D.e + (D.N + 8) * D.eps + D.t +
          PerturbedCentral.totalE * D.t) +
        (D.t + D.t + D.t) + D.t < perturbedBv6 / 2 := by
    simpa only [PerturbedCentral.physicalHeight, PerturbedCentral.totalE,
      PerturbedCentral.rho0, perturbedHeight, perturbedTotalE, perturbedRho]
      using D.new_central_budget
  have hresidual :
      perturbedBv6 / 2 + 15 * PerturbedCentral.rho0 / 8 <
        (49 / 440640 : ℝ) := by
    norm_num [perturbedBv6, PerturbedCentral.rho0]
  have hover := same_D_overhead_le_three_t D htheta2
  linarith

lemma same_D_detector_budget
    {Delta : ℝ} (D : HighDataPerturbed Delta) :
    12 * D.e * ((22 : ℝ) + 2) + 8 * D.κ + 2 * D.cost ≤ D.ε / 2 := by
  nlinarith [D.detector_budget]

lemma same_D_phase_budget
    {Delta : ℝ} (D : HighDataPerturbed Delta) :
    8 * D.e * D.t + D.κ ≤ D.ε := D.phase_budget

lemma same_D_slot_lower
    {Delta : ℝ} (D : HighDataPerturbed Delta) :
    ∀j, (7 / 8 : ℝ) * D.rmin ≤ D.ell j :=
  fun j => (D.slots_bounds j).2.1

lemma same_D_slot_upper
    {Delta : ℝ} (D : HighDataPerturbed Delta) :
    ∀j, D.ell j ≤ (1 / 200 : ℝ) * D.t :=
  fun j => (D.slots_bounds j).2.2

lemma same_D_conductor
    {Delta : ℝ} (D : HighDataPerturbed Delta) :
    PerturbedCentral.physicalHeight + D.t + 2 * D.t ≤ 7 / 8 := by
  simpa only [PerturbedCentral.physicalHeight, PerturbedCentral.rho0,
    perturbedHeight, perturbedRho] using D.physical_conductor_cap

lemma same_D_totalE
    {Delta : ℝ} (D : HighDataPerturbed Delta) :
    (∑j, D.ell j) = PerturbedCentral.totalE := by
  simpa only [PerturbedCentral.totalE, PerturbedCentral.rho0,
    perturbedTotalE, perturbedRho] using D.slots_sum

lemma same_D_height_ranges
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    {theta : ℝ} (htheta : 0 < theta)
    (hthetad : theta < (1 / 200 : ℝ) / 2)
    (hthetacost : 4 * theta < (1 / 200 : ℝ) * D.cost)
    (hthetaeps : theta * (2 + 4 * D.eps) < D.t) :
    theta < (1 / 200 : ℝ) / 2 ∧
      2 * theta < (1 / 200 : ℝ) * D.cost ∧
      4 * theta < (1 / 200 : ℝ) * D.cost ∧
      theta * (2 + 4 * D.eps) < D.t ∧
      theta < 2 * theta := by
  refine ⟨hthetad, ?_, hthetacost, hthetaeps, by linarith⟩
  linarith

/-!
`SameDataNonfloorRows` is the exact central6 nonfloor conclusion after all
parameters are instantiated from the same `D`, the PI adapter, the same `F`,
and one wide count package.  Its moment premise has height `Z^(2*theta)` and
moment cost `D.t`.
-/
def SameDataNonfloorRows
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (wide : WideCountParameters.{0, 0, 0, 0} F.modulus ⊤ D.t)
    (theta : ℝ) (n m : ℕ) : Prop :=
  letI : NeZero (∏P∈F.S, P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  ∃C : ℝ, 0 < C ∧
    ∀eta : Character, ∀ᶠZ : ℝ in atTop, ∀C0 : ℝ, 0 ≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z ^ (PerturbedCentral.physicalHeight + D.t)) →
      ∀idx grid : FreeRow → ℕ,
      (∀u∈rows, idx u ≤ n ∧ grid u ≤ m ∧ grid u ≠ 0 ∧
        51 / 100 + D.e * grid u ≤ 1) →
      (∀u∈rows, detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime eta u
          (rayCubeFamily F.modulus ⊤ le_top u))
        (3 * (idx u + 1 : ℕ) * Z ^ theta) <
          51 / 100 + D.e * grid u + 2 * D.e) →
      (∀u∈rows, 51 / 100 + D.e * grid u ≤ detectorMaximum
        (sourceDetectorFamily F.S F.exclusions.prime eta u
          (rayCubeFamily F.modulus ⊤ le_top u))
        ((3 * idx u : ℕ) * Z ^ theta)) →
      (∀k∈ProbeHighRowFamily.smallDyadicIndices
          (Z ^ (PerturbedCentral.physicalHeight + D.t)),
        ∀i∈Finset.range (n + 1), ∀j∈Finset.range (m + 1),
        let rows' := ProbeHighRowFamily.cubeBinRows
          (rows ∩ ProbeHighRowFamily.dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1| ≤ (3 * i + 1 : ℕ) * Z ^ theta ∧
            |t.2| ≤ (3 * i + 1 : ℕ) * Z ^ theta) ∧
          |t.1.2| ≤ (3 * i + 1 : ℕ) * Z ^ theta) →
        SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime eta rows'
          D.ell (fun _ y => (F.w y : ℂ)) Z
          (ProbeHighRowFamily.sourceDyadConductor Z D.t k)
          (51 / 100 + D.e * j) D.ε theta (7 / 8) 2 D.t D.t i
          ((17 / 50 : ℂ) + t.1.2 * Complex.I)
          (PerturbedCentral.deltaGap HeckeZeroSupremum.beta)
          (if 2 * (51 / 100 + D.e * j) - 1 ≤ 5 / 6 then wide.cB else wide.cH)
          (if 2 * (51 / 100 + D.e * j) - 1 ≤ 5 / 6 then wide.kB else wide.kH)
          (C0 * Z ^ D.t) (Z ^ (2 * theta)) D.t) →
      let Y : Fin D.N → ℝ := fun j => Z ^ (D.ell j)
      let T : Fin D.N → Finset ProbePhysical.PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
      let normer := sourceResidueConstant F.W F.W (∏P∈F.S, P) *
        (Probe.principalScalar Finset.univ Z PerturbedCentral.totalE
          (slotMass T (residueWeights (fun _ => F.w) Y)) : ℂ)
      normer ≠ 0 ∧
      ‖finiteCentralCubeRows F.S F.exclusions F.maximal eta rows T
        (ProbeHighRowFamily.nonfloorPoolOutside F.modulus ⊤ F.S D.N 1 2 Y)
        (fun _ y => (F.w y : ℂ)) Y F.W F.W
        (Z ^ PerturbedCentral.sourceLx) (Z ^ PerturbedCentral.sourceLy) Z D.e
        (fun u => 51 / 100 + D.e * grid u)
        (fun u => (3 * idx u + 1 : ℕ) * Z ^ theta) / normer‖ ≤
      C * C0 * (eta.modulus.absNorm : ℝ) ^ (2 * D.eps) *
        Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma)

/-- Instantiate the complete central6 nonfloor consumer from the same datum. -/
theorem same_data_nonfloor_rows
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (wide : WideCountParameters.{0, 0, 0, 0} F.modulus ⊤ D.t)
    (hbeta : HighFrontierTargets.sigmaBoundary < HeckeZeroSupremum.beta)
    {theta : ℝ} (htheta : 0 < theta)
    (hthetad : theta < (1 / 200 : ℝ) / 2)
    (hthetacost : 4 * theta < (1 / 200 : ℝ) * D.cost)
    (htheta2 : 2 * theta ≤ D.t)
    (hthetaeps : theta * (2 + 4 * D.eps) < D.t)
    (n m : ℕ) :
    SameDataNonfloorRows D hfine F wide theta n m := by
  let G := momentGeometryOfPerturbed D hfine
  have hranges := same_D_height_ranges D htheta hthetad hthetacost hthetaeps
  have hraw := PerturbedCentral.actual_nonfloor_rows_saving_perturbed
    F.modulus ⊤ le_top D.N n
    D.e D.eps 1 2 1 D.t (1 / 200) (7 / 8) D.rmin theta
    D.ε D.κ D.cost D.t D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    D.t_pos.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos htheta D.epsilon_pos
    D.kappa_pos D.cost_pos.le D.t_pos
    (same_D_phase_budget D) D.epsilon_gap D.t_pos hranges.2.1 hthetaeps
    F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (same_D_slot_lower D) (same_D_slot_upper D)
    (fun _ => F.w) (fun _ => F.support) (fun _ => F.smooth)
    (fun _ y => F.bounded y) (fun _ => F.compact) (fun _ => F.nonzero)
    (same_D_totalE D) (by norm_num) D.epsilon_small D.kappa_small
    hthetad hthetacost (same_D_detector_budget D)
    F.w F.smooth F.compact F.positive_support (fun y => (F.bounded y).1)
    F.nonzero 1 2 1 (by norm_num) (by norm_num) (by norm_num)
    F.support (fun y => (F.bounded y).2)
    D.t D.t D.t (2 * theta) D.t HeckeZeroSupremum.beta
    D.t_pos D.t_pos D.t_pos hranges.2.2.2.2
    (by simpa only [PerturbedCentral.boundary, PerturbedCentral.rho0,
      HighFrontierTargets.sigmaBoundary, HighFrontierTargets.rho] using hbeta)
    HeckeZeroSupremum.beta_le_one
    D.t (2 * D.t) D.t D.t_pos.le (by linarith [D.t_small]) (mul_nonneg (by norm_num) D.t_pos.le)
    D.count_budget (same_D_central_hfinal D htheta2)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
    F.complex_nonzero F.complex_nonzero (D.t / 8) (div_pos D.t_pos (by norm_num))
    m (D.t / 8) (div_pos D.t_pos (by norm_num)) (by norm_num)
    (same_D_conductor D) (by linarith) wide
  unfold SameDataNonfloorRows
  obtain ⟨C, hC, hbound⟩ := hraw
  refine ⟨C, hC, ?_⟩
  intro eta
  filter_upwards [hbound eta, eventually_ge_atTop (1 : ℝ)] with Z hZbound hZ
  intro C0 hC0 rows hrows idx grid hlabels hnext hcurrent hmom
  obtain ⟨hnormer, hb⟩ := hZbound C0 hC0 rows hrows idx grid hlabels
    hnext hcurrent hmom
  refine ⟨hnormer, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hZ (by
    have hs := D.high_saving
    linarith)

end SevenEighths.PerturbedSameDataCentral

end

end OAI
