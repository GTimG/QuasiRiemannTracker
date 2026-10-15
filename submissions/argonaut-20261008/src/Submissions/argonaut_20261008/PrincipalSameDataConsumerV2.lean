import Submissions.argonaut_20261008.PrincipalNormalizedPerturbedV2
import Submissions.argonaut_20261008.PrincipalSameDataGeometryV2
import Submissions.argonaut_20261008.OAI.NumberTheory.DirichletL.Detector.PerturbedJointSource

namespace OAI.SevenEighths.LocalPrincipalSameDataV2
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
open HeckeFamily ProbePhysical ProbeHighRowFamily PrincipalSignalComparison
open Parameters PerturbedMomentConstruction
open PerturbedPrincipalPerCharacterInterfaces
open LocalPrincipalGeometryV2 LocalPrincipalCutoffsV2
open LocalPrincipalSameDataGeometryV2

/-!
Actual same-data principal producer.

The source `F` and hence `F.S`, `F.modulus`, `F.w`, and `F.W` are fixed before
`eta`.  The theorem below invokes the full V2 contour/remainder/normalization
proof on those exact objects.  Its conclusion is the existing
`EulerPrincipalRawPerCharacterAt`; no replacement interface is introduced.
Kernel/elaboration status: NOT_RUN.
-/

/-- Reconstruct the exact per-character raw Euler comparison on one already
fixed `D`, `hfine`, and `F`.  The existential constant remains inside the
character quantifier. -/
theorem euler_raw_same_data
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (hcut : ∀ P : PrimeIdeal,
      P.val.absNorm ≤ commonCutoff → P.val ∈ F.S)
    (hbeta : analyticBoundaryB0 ≤ HeckeZeroSupremum.beta) :
    EulerPrincipalRawPerCharacterAt D hfine F := by
  unfold EulerPrincipalRawPerCharacterAt
  intro eta
  have hsum : (∑ j, D.ell j) = E := by
    simpa only [E] using D.slots_sum
  have hmin : 0 < (7 / 8 : ℝ) * D.rmin :=
    mul_pos (by norm_num) D.rmin_pos
  have ha : analyticBoundaryB0 < HeckeZeroSupremum.beta + D.e := by
    linarith [D.e_pos]
  have ha2 : HeckeZeroSupremum.beta + D.e ≤ 2 := by
    linarith [HeckeZeroSupremum.beta_le_one, D.e_small]
  obtain ⟨C, hC, hbound⟩ :=
    LocalPrincipalNormalizedV2.actual_ray_principal_comparison_v2
      F.modulus ⊤ le_top eta F.S F.exclusions hcut
      1 2 1 ((7 / 8 : ℝ) * D.rmin)
      (by norm_num) (by norm_num) (by norm_num) hmin
      D.ell (fun j => (D.slots_bounds j).2.1) D.slots_injective hsum
      (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact)
      (fun _ => F.support) (fun _ y => F.bounded y) (fun _ => F.nonzero)
      F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
      F.complex_support F.complex_support F.real F.real
      F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
      D.e (D.t / 8) D.e_pos D.e_small.le
        (div_pos D.t_pos (by norm_num)) ha ha2
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with Z hZ
  dsimp only at hZ ⊢
  rw [E_eq_central_totalE,
    lx_eq_central_sourceLx,
    ly_eq_central_sourceLy,
    analyticBoundaryB0_eq_central_boundary] at hZ
  simpa only [ProbeHighRowFamily.principalPhysicalPool,
    frontier_totalE_eq_central_totalE] using hZ

/-- The finite common cutoff is fixed before `F`, its window, its modulus, and
all characters. -/
theorem exists_same_source_inputs
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200) :
    ∃ F : PerturbedSourceData (momentGeometryOfPerturbed D hfine),
      (∀ P : PrimeIdeal,
        P.val.absNorm ≤ commonCutoff → P.val ∈ F.S) ∧
      SourceExclusionsSigma F.S := by
  obtain ⟨F, hcut⟩ :=
    exists_perturbed_source_data_with_norm_cutoff
      (momentGeometryOfPerturbed D hfine) commonCutoff
  exact ⟨F, hcut, same_source_exclusions F.S F.exclusions hcut⟩

/-- Pay both actual scalar budgets of the same `D`; in particular the window
term uses `D.window_boundary_budget`. -/
theorem euler_comparison_same_data
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200)
    (F : PerturbedSourceData (momentGeometryOfPerturbed D hfine))
    (hcut : ∀ P : PrimeIdeal,
      P.val.absNorm ≤ commonCutoff → P.val ∈ F.S)
    (hbeta : analyticBoundaryB0 ≤ HeckeZeroSupremum.beta) :
    EulerPrincipalComparisonPerCharacterAt D hfine F := by
  exact eulerPrincipalComparison_per_character_of_raw D hfine F
    (euler_raw_same_data D hfine F hcut hbeta)

/-- One source is fixed after the pure common cutoff and before every
character.  Both target interfaces use that exact source. -/
theorem exists_same_source_euler_outputs
    {Delta : ℝ} (D : HighDataPerturbed Delta)
    (hfine : ∀ j, D.ell j ≤ detectorMesh D.t / 200)
    (hbeta : analyticBoundaryB0 ≤ HeckeZeroSupremum.beta) :
    ∃ F : PerturbedSourceData (momentGeometryOfPerturbed D hfine),
      (∀ P : PrimeIdeal,
        P.val.absNorm ≤ commonCutoff → P.val ∈ F.S) ∧
      SourceExclusionsSigma F.S ∧
      EulerPrincipalRawPerCharacterAt D hfine F ∧
      EulerPrincipalComparisonPerCharacterAt D hfine F := by
  obtain ⟨F, hcut, hSigma⟩ := exists_same_source_inputs D hfine
  exact ⟨F, hcut, hSigma,
    euler_raw_same_data D hfine F hcut hbeta,
    euler_comparison_same_data D hfine F hcut hbeta⟩

end
end OAI.SevenEighths.LocalPrincipalSameDataV2
