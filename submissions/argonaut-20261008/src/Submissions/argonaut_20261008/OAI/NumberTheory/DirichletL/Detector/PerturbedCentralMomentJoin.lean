import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedSameDataCentral

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set

namespace SevenEighths.PerturbedCentralMomentJoin

open HeckeFamily ProbePhysical ProbeMellinBoundary
open HeckeInverseAmplification hiding PrimeIdeal
open ProbeRaySlots
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
open SevenEighths.ProbeHighRowFamily SevenEighths.ProbeFinalAssembly
open SevenEighths.PerturbedCentral SevenEighths.PerturbedCountBridge
open SevenEighths.PerturbedCountProjection
open SevenEighths.PerturbedMomentConstruction
open SevenEighths.PerturbedSameDataCentral
open SevenEighths.HighFrontierTargets hiding totalE
open SevenEighths.Parameters

local notation "O" => HeckeFamily.O

/-!
# Chosen global moments inserted into every actual central cell

This is the height-sensitive join omitted from the raw central6 theorem.  It
uses `height = Z^(2*theta)` exactly.  No monotonicity from that interval to
`Z^D.t` is invoked.
-/

def SameDataClosedNonfloorRows
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (theta : ℝ) (n m : ℕ) : Prop :=
  letI : NeZero (∏P∈F.S, P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  ∃Cc : ℝ, 0 < Cc ∧ ∀eta : Character, ∃Cm : ℝ, 0 < Cm ∧
    ∀ᶠZ : ℝ in atTop,
      ∀rows : Finset FreeRow,
      (∀u∈rows, u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
        (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
        rowNorm u ≤ Z ^ (physicalHeight + D.t)) →
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
      let Y : Fin D.N → ℝ := fun j => Z ^ (D.ell j)
      let T : Fin D.N → Finset PrimeIdeal := fun j =>
        pool (RayQuotient.identityClass F.modulus ⊤) F.S 1 2 (Y j)
      let normer := sourceResidueConstant F.W F.W (∏P∈F.S, P) *
        (Probe.principalScalar Finset.univ Z totalE
          (slotMass T (residueWeights (fun _ => F.w) Y)) : ℂ)
      normer ≠ 0 ∧
      ‖finiteCentralCubeRows F.S F.exclusions F.maximal eta rows T
        (ProbeHighRowFamily.nonfloorPoolOutside F.modulus ⊤ F.S D.N 1 2 Y)
        (fun _ y => (F.w y : ℂ)) Y F.W F.W
        (Z ^ sourceLx) (Z ^ sourceLy) Z D.e
        (fun u => 51 / 100 + D.e * grid u)
        (fun u => (3 * idx u + 1 : ℕ) * Z ^ theta) / normer‖ ≤
      Cc * Cm * (eta.modulus.absNorm : ℝ) ^ (2 * D.eps) *
        Z ^ (HeckeZeroSupremum.beta - 11 / 16 - D.sigma)

/--
Feed the chosen `SourceMomentBoundAt` into every cell required by central6.
The official count record is the projection of `wide`, hence all branch
constants match by rfl.
-/
theorem same_data_closed_nonfloor_rows
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
    (n m : ℕ)
    (hsource : ∀eta : Character, ∃Cm : ℝ, 0 < Cm ∧ ∀ᶠZ : ℝ in atTop,
      SourceMomentBoundAt F.modulus ⊤ le_top F.S F.exclusions F.maximal
        D.ell (fun _ => F.w) (1 / 200) (7 / 8) 2 D.ε D.t D.t D.t
        HighFrontierTargets.positiveGap D.t wide.toCountParameters
        eta Z theta (Cm * Z ^ D.t) (Z ^ (2 * theta))) :
    SameDataClosedNonfloorRows D hfine F theta n m := by
  have hcentral := same_data_nonfloor_rows D hfine F wide hbeta htheta
    hthetad hthetacost htheta2 hthetaeps n m
  unfold SameDataNonfloorRows at hcentral
  obtain ⟨Cc, hCc, hcentral⟩ := hcentral
  unfold SameDataClosedNonfloorRows
  refine ⟨Cc, hCc, ?_⟩
  intro eta
  obtain ⟨Cm, hCm, hsourceEta⟩ := hsource eta
  refine ⟨Cm, hCm, ?_⟩
  filter_upwards [hcentral eta, hsourceEta,
    ProbeHighRowFamily.sourceDyad_geometry_eventually
      (1 / 200) (7 / 8) D.t (physicalHeight + D.t)
      (by norm_num) (by norm_num) D.t_pos (same_D_conductor D),
    eventually_external_height_le_moment_height n htheta,
    eventually_gt_atTop (1 : ℝ)] with Z hcentralZ hsourceZ hgeo hheight hZ
  intro rows hrows idx grid hlabels hnext hcurrent
  have hmom :
      ∀k∈ProbeHighRowFamily.smallDyadicIndices
          (Z ^ (physicalHeight + D.t)),
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
          (Cm * Z ^ D.t) (Z ^ (2 * theta)) D.t := by
    intro k hk i hi j hj
    dsimp only
    intro hne t ht
    let Rk := rows ∩ ProbeHighRowFamily.dyadicRows 1 k
    let Rij := ProbeHighRowFamily.cubeBinRows Rk idx grid i j
    have hsubk : Rij ⊆ Rk := Finset.filter_subset _ _
    have hsub : Rij ⊆ rows := hsubk.trans Finset.inter_subset_left
    have hgeo' := hgeo rows
      (fun u hu => ⟨(hrows u hu).1, (hrows u hu).2.1, (hrows u hu).2.2.2⟩)
      k (hne.mono hsubk)
    obtain ⟨u0, hu0⟩ := hne
    have huj : grid u0 = j :=
      ((ProbeHighRowFamily.mem_cubeBinRows Rk idx grid i j u0).mp hu0).2.2
    have hju : j ≠ 0 := huj ▸ (hlabels u0 (hsub hu0)).2.2.1
    have ha : (51 / 100 : ℝ) < 51 / 100 + D.e * j := by
      have hjpos : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hju
      nlinarith [D.e_pos]
    have ha1 : 51 / 100 + D.e * j ≤ 1 := by
      simpa only [huj] using (hlabels u0 (hsub hu0)).2.2.2
    have hrows' : ∀u∈Rij,
        u.val ≠ 1 ∧ Z ^ (1 / 100 : ℝ) ≤ rowNorm u ∧
          (calibrationForSet F.S F.maximal).residueMonoid u.val ≠ 0 ∧
          rowNorm u ≤ Z ^
            (ProbeHighRowFamily.sourceDyadConductor Z D.t k - D.t) := by
      intro u hu
      exact ⟨(hrows u (hsub hu)).1, (hrows u (hsub hu)).2.1,
        (hrows u (hsub hu)).2.2.1, hgeo'.2.2.2.2.2 u (hsubk hu)⟩
    have hile : i ≤ n := by
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have him : |t.1.2| ≤ Z ^ (2 * theta) :=
      ht.2.trans (hheight.2 i hile)
    have hs := hsourceZ Rij
      (ProbeHighRowFamily.sourceDyadConductor Z D.t k)
      (51 / 100 + D.e * j)
      hgeo'.2.2.1 hgeo'.2.2.2.1 ha ha1 hrows' i
      ((17 / 50 : ℂ) + t.1.2 * Complex.I) (by simp) (by simpa using him)
    simpa only [HighFrontierTargets.positiveGap,
      HighFrontierTargets.sigmaBoundary, HighFrontierTargets.rho,
      PerturbedCentral.deltaGap, PerturbedCentral.boundary, PerturbedCentral.rho0,
      WideCountParameters.toCountParameters_cB,
      WideCountParameters.toCountParameters_kB,
      WideCountParameters.toCountParameters_cH,
      WideCountParameters.toCountParameters_kH] using hs
  have hb := hcentralZ Cm hCm.le rows hrows idx grid hlabels hnext hcurrent hmom
  simpa only [mul_assoc] using hb

end SevenEighths.PerturbedCentralMomentJoin

end

end OAI
