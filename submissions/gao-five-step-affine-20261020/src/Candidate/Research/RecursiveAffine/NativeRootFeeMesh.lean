/- Exact bare-root native fee at the external detector mesh.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualRootNativeFee

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open Cycle63InitialMass Cycle153SourceSchedule Cycle153.RegionalSchedule Cycle153RootStep
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}

/-- All source fields are literal. Only the detector mesh is supplied by
its actual root caller; the enlarged inner-context mesh is not substituted. -/
def actualRootNativeFeeAtMesh (C : SourceContext (α:=alpha) M H)(s : Input alpha)
    (eps : ℝ)(budget : ℕ)(Rdel : Finset alpha)
    (mesh : ℝ)(hmesh : 0 ≤ mesh)
    (hdeleted : (∑i∈Rdel,C.originalWeight i) ≤ rootDetectorDeletion C.originalWeight+mesh) : NativePathFee where
  driverDelta:=nativeDriverRate budget
  driverError:=oldLoss eps
  coefficientError:=postDictionaryRate C.Bnorm budget
  shellCost:=130*postDictionaryRate C.Bnorm budget
  sourcePad:=actualRootSourcePad C s
  slotLoss:=2*nativeDriverRate budget*31*(Fintype.card alpha:ℝ)
  junction:=Cycle153Geometry.Coordinates.q0
  actualDeletion:=∑i∈Rdel,C.originalWeight i
  nativeTargetDeletion:=rootDetectorDeletion C.originalWeight
  modelDeletion:=rootSourceDeletion C.originalWeight
  primeMesh:=mesh
  primeMesh_nonneg:=hmesh
  deletion_upper:=hdeleted
  roundingError:=1/(10:ℝ)^20
  roundingError_nonneg:=by positivity
  target_eq:=by unfold rootDetectorDeletion;norm_num


/-- Comparison is used only for the fine budget; the actual edge continues
to carry the smaller exact fee, with its own mesh and deletion proof. -/
theorem actual_root_native_fee_at_mesh_le
    (s : Input alpha)(eps : ℝ)(budget : ℕ)(Rdel : Finset alpha)
    (mesh : ℝ)(hmesh : 0 ≤ mesh)(hmeshCap : mesh ≤ C.slotMesh)
    (hdeleted : (∑i∈Rdel,C.originalWeight i) ≤ rootDetectorDeletion C.originalWeight+mesh) :
    (actualRootNativeFeeAtMesh C s eps budget Rdel mesh hmesh hdeleted).amount ≤
      (actualRootNativeFee C s eps budget Rdel (hdeleted.trans (add_le_add le_rfl hmeshCap))).amount :=by
  have hq : 0 ≤ Cycle153Geometry.Coordinates.q0 :=by norm_num [Cycle153Geometry.Coordinates.q0]
  have hh:=mul_le_mul_of_nonneg_left hmeshCap hq
  dsimp only [actualRootNativeFeeAtMesh,actualRootNativeFee,NativePathFee.amount]
  linarith only [hh]

/-- Fixed native threshold, fine fee and proper-source coarse remainder at
EVERY actual external mesh. Constants precede moving contexts, deletions,
inputs and meshes. No fee or coarse remainder is assumed. -/
theorem eventually_actual_root_native_fee_at_mesh
    (eps : ℝ)(heps : 0<eps)(budget : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(C : SourceContext (α:=alpha) M H)(s : Input alpha),C.globalBase=Z→
      s.b₁=(9/4:ℝ)→s.b₂=(9/4:ℝ)→C.slotMesh ≤ localSlotMesh eps→Fintype.card alpha ≤ budget→
    ∀(mesh : ℝ)(hmesh : 0 ≤ mesh)(hmeshCap : mesh ≤ C.slotMesh)
      (Rdel : Finset alpha)
      (hdeleted : (∑i∈Rdel,C.originalWeight i) ≤ rootDetectorDeletion C.originalWeight+mesh),
    Real.logb C.globalBase 128+actualRootSourcePad C s ≤ 1/(10:ℝ)^20 ∧
      (actualRootNativeFeeAtMesh C s eps budget Rdel mesh hmesh hdeleted).amount ≤ 1/(10:ℝ)^15 ∧
      ((rootDetectorDeletion C.originalWeight ≤ ∑i∈Rdel,C.originalWeight i)→
      (@Cycle63.AffineLedger.PlainWindow Cycle153.Root.rootLedger
        (CenteredMomentEnergyBands.length C.globalBase s.X₁)
        (CenteredMomentEnergyBands.length C.globalBase s.X₂) (∑i,C.originalWeight i))→
      (actualRootNativeFeeAtMesh C s eps budget Rdel mesh hmesh hdeleted).junction*
        (actualRootNativeFeeAtMesh C s eps budget Rdel mesh hmesh hdeleted).modelDeletion+
        (actualRootNativeFeeAtMesh C s eps budget Rdel mesh hmesh hdeleted).amount ≤ 2) :=by
  filter_upwards [eventually_actual_root_native_fee (alpha:=alpha) (M:=M) (H:=H) eps heps budget] with Z hz
  refine ⟨hz.1,?_⟩
  intro C s hbase hb1 hb2 hcontext hcard mesh hmesh hmeshCap Rdel hdeleted
  have hdelContext:=hdeleted.trans (add_le_add le_rfl hmeshCap)
  have hb:=hz.2 C s hbase hb1 hb2 hcontext hcard Rdel hdelContext
  have hcompare:=actual_root_native_fee_at_mesh_le s eps budget Rdel mesh hmesh hmeshCap hdeleted
  refine ⟨hb.1,hcompare.trans hb.2.1,?_⟩
  intro hcover hwindow
  have hrest:=hb.2.2 hcover hwindow
  change Cycle153Geometry.Coordinates.q0*rootSourceDeletion C.originalWeight+_ ≤ 2 at hrest ⊢
  linarith only [hrest,hcompare]

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_native_fee_at_mesh_le
#print axioms OAI.SevenEighths.Cycle153Reachable.eventually_actual_root_native_fee_at_mesh
