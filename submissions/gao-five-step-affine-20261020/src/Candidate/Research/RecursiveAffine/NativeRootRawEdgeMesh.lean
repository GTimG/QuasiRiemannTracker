/- Exact selected root raw edge at its ACTUAL root mesh. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootFeeMesh
import Candidate.Research.RecursiveAffine.NativeRootPaidSource
import Candidate.Research.RecursiveAffine.NativeLengthLift

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63InitialMass Cycle153JointCount Cycle153RegionalLow Cycle153RootStep
open Cycle153SourceSchedule Cycle153.RegionalSchedule
open CenteredMomentAmplificationChildInput CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentCommonRadialData CenteredMomentSectorLocalization Cycle63Moment
variable {alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}

/-- Exact raw remaining fee from the actual root source. The bin mass
loss is kept separately in the source's shifted outside coefficient. -/
def actualRootRemainingFeesAtMesh (C : SourceContext (α:=alpha) M H)(s : Input alpha)(epsilon : ℝ)(budget : ℕ)(mesh : ℝ) : ℝ :=
  3*nativeDriverRate budget+oldLoss epsilon+postDictionaryRate C.Bnorm budget+
    130*postDictionaryRate C.Bnorm budget+actualRootSourcePad C s+
    2*nativeDriverRate budget*31*(Fintype.card alpha:ℝ)+Cycle153Geometry.Coordinates.q0*mesh

/-- The literal raw root weight and historical missing radical agree
with the SAME native paid node/fee after the compensated length lift.
There is no inequality, energy or future-source premise in this identity. -/
theorem actual_root_paid_edge_identity_at_mesh
    (s : Input alpha)(reflected second : Bool)(firstHeight : ℝ)(budget : ℕ)
    (key : ℤ×(Fin 5→ℤ))(hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key)
    (massLoss sideError : ℝ)
    (hside : ∀l,massLoss+lowLabelSide reflected C.globalBase (Real.logb C.globalBase (volume s))
      (geometryFirstLabel s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val) ≤ sideError)
    (r : NativeLowRows reflected s 1 1 C.globalBase 1 (rootSourceAmp C.originalWeight)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2 firstIndex)
    (epsilon : ℝ)(Rdel : Finset alpha)(mesh : ℝ)(hmesh : 0 ≤ mesh)
    (hdeleted : (∑i∈Rdel,C.originalWeight i) ≤ rootDetectorDeletion C.originalWeight+mesh) :
    let praw:=actualRootSelectedPaidNode C.globalBase C.globalBase_gt_one reflected second s 1 1 1
      (rootSourceAmp C.originalWeight) (nativeMu/64) (nativeMu/8) (nativeDriverRate budget) (9/4)
      firstHeight (Fintype.card alpha) key hz1 hz2 firstIndex massLoss sideError hside r
    let fee:=actualRootNativeFeeAtMesh C s epsilon budget Rdel mesh hmesh hdeleted
    let lifted:=praw.lengthLift (rootSourceLength C.originalWeight-praw.length)
    C.globalBase^(1+actualHighCoordinates reflected (!reflected) second praw.first praw.C praw.D praw.inactive
        C.globalBase 1 (Real.logb C.globalBase (volume s)) (rootSourceAmp C.originalWeight)
        (nativeMu/64) (nativeMu/8) (nativeDriverRate budget) 0+
      Cycle153Geometry.Coordinates.q0*(∑i∈Rdel,C.originalWeight i)+massLoss+
        actualRootRemainingFeesAtMesh C s epsilon budget mesh)=
      C.globalBase^(lifted.scale+lifted.shiftedOutside+fee.junction*fee.modelDeletion+fee.amount) ∧
    lifted.coordinate 1=Real.logb C.globalBase ((firstSourceMissing (!reflected) praw.first).absNorm:ℝ) :=by
  intro praw fee lifted
  constructor
  · rw [NativePaidPathNode.lengthLift_scale,NativePaidPathNode.lengthLift_shiftedOutside]
    have hraw:=actual_root_selected_raw_edge C.globalBase C.globalBase_gt_one reflected second s 1 1 1
      (rootSourceAmp C.originalWeight) (nativeMu/64) (nativeMu/8) (nativeDriverRate budget) (9/4)
      firstHeight (Fintype.card alpha) key hz1 hz2 firstIndex massLoss sideError hside r
      Cycle153Geometry.Coordinates.q0 (∑i∈Rdel,C.originalWeight i) (rootSourceDeletion C.originalWeight)
      (actualRootRemainingFeesAtMesh C s epsilon budget mesh)
    apply hraw.trans
    congr 1
    dsimp only [fee,actualRootNativeFeeAtMesh,NativePathFee.amount,actualRootRemainingFeesAtMesh]
    ring
  · rw [NativePaidPathNode.lengthLift_coordinate_one]
    change (1:ℝ)*Real.logb (C.globalBase^1) ((firstSourceMissing (!reflected) praw.first).absNorm:ℝ)=_
    rw [Real.rpow_one,one_mul]
end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_paid_edge_identity_at_mesh
