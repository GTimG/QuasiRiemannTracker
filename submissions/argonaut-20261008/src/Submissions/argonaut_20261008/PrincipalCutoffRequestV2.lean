import Submissions.argonaut_20261008.PrincipalSameDataConsumerV2
import Submissions.argonaut_20261008.PerturbedDfirstSource

namespace OAI.SevenEighths.LocalPrincipalCutoffRequestV2
noncomputable section
open scoped Classical BigOperators
open HeckeFamily ProbePhysical Parameters PerturbedMomentConstruction
open PrincipalSignalComparison ProbePrincipalResidueActual
open HighFrontierTargets
open LocalPrincipalCutoffsV2 LocalPrincipalSameDataV2
open LocalPrincipalSameDataGeometryV2
open PerturbedPrincipalPerCharacterInterfaces
open PerturbedCountBridge

/-!
Additive D-first analytic handoff.  Kernel/elaboration status: NOT_RUN.

The request depends only on the already selected `D`.  A dominating finite
cutoff is then inserted before `F`, its modulus, its window, the count
parameters, and all characters.  No analytic estimate is stored in the source
constructor.
-/

/-- Uniform request supplied by the current b0 finite/global principal chain. -/
def principalCutoffRequest
    (_D : HighDataPerturbed HighFrontierTargets.positiveGap) : ℕ :=
  commonCutoff

/-- Coverage for a dominating D-dependent cutoff implies coverage for every
principal cutoff used by the V2 proof. -/
theorem principal_coverage_of_domination
    (D : HighDataPerturbed HighFrontierTargets.positiveGap)
    (N : HighDataPerturbed HighFrontierTargets.positiveGap → ℕ)
    (hN : principalCutoffRequest D ≤ N D)
    (S : Finset (Ideal HeckeFamily.O))
    (hcover : ∀ P : PrimeIdeal,
      P.val.absNorm ≤ N D → P.val ∈ S) :
    ∀ P : PrimeIdeal,
      P.val.absNorm ≤ commonCutoff → P.val ∈ S := by
  intro P hP
  exact hcover P (hP.trans hN)



/-- The uniform request simultaneously supplies the stronger Sigma tail and
the actual same-S source-correction analytic/defect statement. -/
theorem principalCutoffRequest_spec
    (D : HighDataPerturbed HighFrontierTargets.positiveGap)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (hcover : ∀ P : PrimeIdeal,
      P.val.absNorm ≤ principalCutoffRequest D → P.val ∈ F.S)
    (eta : Character) :
    SourceExclusionsSigma F.S ∧
    AnalyticOnNhd ℂ (sourceCorrection eta F.S)
      {s : ℂ | analyticBoundaryB0 < s.re} ∧
    (∀ s : ℂ, analyticBoundaryB0 < s.re →
      ‖sourceCorrection eta F.S s - 1‖ ≤ 1 / 2) := by
  have hcommon : ∀ P : PrimeIdeal,
      P.val.absNorm ≤ commonCutoff → P.val ∈ F.S := by
    simpa only [principalCutoffRequest] using hcover
  exact ⟨same_source_exclusions F.S F.exclusions hcommon,
    same_source_correction F.S F.exclusions hcommon eta⟩

/-- Consume the D-first constructor's finite-coverage clause on exactly its
returned source `F`. -/
theorem euler_raw_of_D_first_cutoff
    (D : HighDataPerturbed HighFrontierTargets.positiveGap)
    (N : HighDataPerturbed HighFrontierTargets.positiveGap → ℕ)
    (hN : principalCutoffRequest D ≤ N D)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (hcover : ∀ P : PrimeIdeal,
      P.val.absNorm ≤ N D → P.val ∈ F.S)
    (hbeta : analyticBoundaryB0 ≤ HeckeZeroSupremum.beta) :
    EulerPrincipalRawPerCharacterAt D hfine F := by
  exact euler_raw_same_data D hfine F
    (principal_coverage_of_domination D N hN F.S hcover) hbeta

/-- The same source receives the exact two-budget saved comparison. -/
theorem euler_comparison_of_D_first_cutoff
    (D : HighDataPerturbed HighFrontierTargets.positiveGap)
    (N : HighDataPerturbed HighFrontierTargets.positiveGap → ℕ)
    (hN : principalCutoffRequest D ≤ N D)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (hcover : ∀ P : PrimeIdeal,
      P.val.absNorm ≤ N D → P.val ∈ F.S)
    (hbeta : analyticBoundaryB0 ≤ HeckeZeroSupremum.beta) :
    EulerPrincipalComparisonPerCharacterAt D hfine F := by
  exact euler_comparison_same_data D hfine F
    (principal_coverage_of_domination D N hN F.S hcover) hbeta

/--
Run the actual D-first source constructor and immediately consume its coverage
clause with the complete principal V2 producer.  The same returned `F` and
`wide` are exposed to the final common-probe consumer.

The existential constants in the Euler outputs remain per character because
the returned conclusions are the unchanged per-character target interfaces.
-/
theorem exists_D_first_same_data_principal_outputs
    (hbeta : HighFrontierTargets.sigmaBoundary <
      HeckeZeroSupremum.beta)
    (N : HighDataPerturbed HighFrontierTargets.positiveGap → ℕ)
    (hN : ∀ D, principalCutoffRequest D ≤ N D) :
    ∃ D : HighDataPerturbed HighFrontierTargets.positiveGap,
      ∃ hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200,
      ∃ F : PerturbedSourceData (momentGeometryOfPerturbed D hfine),
        (∀ P : PrimeIdeal,
          P.val.absNorm ≤ N D → P.val ∈ F.S) ∧
        ∃ wide : WideCountParameters.{0,0,0,0} F.modulus ⊤ D.t,
          EulerPrincipalRawPerCharacterAt D hfine F ∧
          EulerPrincipalComparisonPerCharacterAt D hfine F := by
  obtain ⟨D, hfine, F, hcover, wide, _hheight⟩ :=
    exists_D_first_cutoff_source_counts_chosen_height hbeta N
  have hbetaClosed :
      analyticBoundaryB0 ≤ HeckeZeroSupremum.beta := by
    rw [analyticBoundaryB0_eq_sigmaBoundary]
    exact hbeta.le
  have hraw :=
    euler_raw_of_D_first_cutoff D N (hN D)
      hfine F hcover hbetaClosed
  have hcomparison :=
    euler_comparison_of_D_first_cutoff D N (hN D)
      hfine F hcover hbetaClosed
  exact ⟨D, hfine, F, hcover, wide, hraw, hcomparison⟩

end
end OAI.SevenEighths.LocalPrincipalCutoffRequestV2
