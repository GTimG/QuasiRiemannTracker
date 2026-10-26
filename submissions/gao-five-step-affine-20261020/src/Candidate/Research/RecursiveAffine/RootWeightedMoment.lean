/- Actual weighted root moment assembly, with the final mesh fixed before N and every source.
Copyright (c)2026 Zhongpai Gao. Native reductions by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.RootInitialAssembly
import Candidate.Research.RecursiveAffine.SourceContextMesh
import Submissions.akashlevy_20261009_weighted_numerator.WeightedQRH.HighRows.WeightedSourceCellGeometry

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 6000
namespace OAI.SevenEighths.Cycle153RootInitialAssembly
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap ComplexConjugate HeckeNotation
open Filter HeckeFamily CenteredMomentNaturalFixedRaySource
open Cycle153SourceSchedule Cycle63InitialMass CenteredMomentLogDyadic

/-- This minimum precedes the ambient cardinality and the weighted source.
The comparison mesh is a genuine fixed-parent source-reduction requirement. -/
def rootMomentMesh (eps : ℝ) : ℝ :=
  min (originalSlotMesh eps) (Cycle63FirstActual.comparisonMesh 1 1 (eps/2))

theorem rootMomentMesh_pos {eps : ℝ} (heps : 0<eps) : 0<rootMomentMesh eps := by
  unfold rootMomentMesh
  exact lt_min (originalSlotMesh_pos heps)
    (Cycle63FirstActual.comparisonMesh_pos 1 1 (eps/2) (by norm_num) le_rfl (by positivity))

theorem rootMomentMesh_source (eps : ℝ) : rootMomentMesh eps≤originalSlotMesh eps :=
  min_le_left _ _

theorem rootMomentMesh_comparison (eps : ℝ) :
    rootMomentMesh eps≤Cycle63FirstActual.comparisonMesh 1 1 (eps/2) := min_le_right _ _

/-- Convert the actual root live-budget proof to the precise weighted initial
energy estimate used by the final detector. The fixed ideal and seed are
unchanged; no RootMomentFactory instance or requested moment is assumed. -/
theorem weighted_root_initial_from_actual_budget {D : WeightedQRH.MomentData}
    (S : ProbeFinalAssembly.WeightedSourceData D) (eta : Character)
    (eps meshUsed bPhi tau xi : ℝ) (heps : 0<eps) (hmesh : 0 < meshUsed)
    (hmeshUsed : meshUsed≤rootMomentMesh eps) (hbPhi : 2≤bPhi)
    (htau : 0<tau) (hxi : 0<xi)
    (hbeta : 51/100≤HeckeZeroSupremum.beta) (hbetaUpper : HeckeZeroSupremum.beta≤7/8)
    (hbudget : LiteralAffineGeometryBudget (α:=Fin D.N) S.modulus ⊤ le_top
      (fun x=>conj (S.W x))
      (HeckeInverseAmplification.conjugate_profile_smooth _ (S.W.smooth ⊤)).continuous
      (CenteredMomentDetectorPlainSlotProfile.weighted_conjugate_source_support S)
      eta eta (weighted_sourceFixedIdeal S) bPhi meshUsed (eps/4) tau xi) :
    ∃degree : ℕ,∃Sd : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      Cycle153EndpointMoment.InitialAffineAt (α:=Fin D.N) S.modulus ⊤ le_top
        (fun x=>conj (S.W x)) 2 (1/4) (9/4) bPhi meshUsed (33/50) (33/50) 1 1 eps Z
        eta eta (weighted_sourceFixedIdeal S) degree Sd C := by
  exact literal_geometry_initial_affine (α:=Fin D.N) S.modulus ⊤ le_top
    (fun x=>conj (S.W x))
    (HeckeInverseAmplification.conjugate_profile_smooth _ (S.W.smooth ⊤))
    (CenteredMomentDetectorPlainSlotProfile.weighted_conjugate_source_support S)
    eta eta (weighted_sourceFixedIdeal S) bPhi meshUsed eps tau xi
    (by linarith) hmesh heps htau hxi
    (hmeshUsed.trans (rootMomentMesh_comparison eps)) hbeta (by linarith)
    (weighted_sourceFixedIdeal_le_modulus S)
    (internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero S) eta)
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top S) eta)
    (inf_le_left.trans (weighted_sourceFixedIdeal_le_72 S)) logAnnulus_compact logAnnulus_smooth hbudget

end
end OAI.SevenEighths.Cycle153RootInitialAssembly
#print axioms OAI.SevenEighths.Cycle153RootInitialAssembly.rootMomentMesh_pos
#print axioms OAI.SevenEighths.Cycle153RootInitialAssembly.weighted_root_initial_from_actual_budget
