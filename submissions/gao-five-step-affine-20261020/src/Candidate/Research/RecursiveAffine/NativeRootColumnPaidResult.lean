/- A single actual ROOT column returns one paid source family.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootFeeMesh
import Candidate.Research.RecursiveAffine.NativeRootRawEdgeMesh
import Candidate.Research.RecursiveAffine.NativeRootColumnEdge
import Candidate.Research.RecursiveAffine.NativeLengthLift
import Candidate.Research.RecursiveAffine.NativeCommonForest
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153Reachable Cycle153JointCount Cycle153RegionalLow Cycle153RootStep Cycle153Geometry
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput Cycle153SourceReturn
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M≤H}
variable (C : SourceContext (α:=alpha) M H)(s : Input alpha)

/-- The unshifted native coefficient uses the actual deletion and the
actual external mesh. The compensated volume changes no raw coefficient. -/
def rootNativePaidCoefficient (paid : NativePaidPathNode C.globalBase)
    (eps : ℝ)(budget : ℕ)(mesh : ℝ)(R : Finset alpha) : ℝ :=
  C.globalBase^(paid.scale+paid.shiftedOutside+Coordinates.q0*(∑i∈R,C.originalWeight i)+
    actualRootRemainingFeesAtMesh C s eps budget mesh)

theorem root_native_paid_coefficient_eq
    (paid : NativePaidPathNode C.globalBase)(eps : ℝ)(budget : ℕ)
    (mesh : ℝ)(hmesh : 0≤ mesh)(R : Finset alpha)
    (hdeleted : (∑i∈R,C.originalWeight i)≤rootDetectorDeletion C.originalWeight+mesh) :
    let p:=paid.lengthLift (rootSourceLength C.originalWeight-paid.length)
    let fee:=actualRootNativeFeeAtMesh C s eps budget R mesh hmesh hdeleted
    rootNativePaidCoefficient C s paid eps budget mesh R=
      C.globalBase^(p.scale+p.shiftedOutside+fee.junction*fee.modelDeletion+fee.amount) :=by
  intro p fee
  unfold rootNativePaidCoefficient
  rw [NativePaidPathNode.lengthLift_scale,NativePaidPathNode.lengthLift_shiftedOutside]
  congr 1
  dsimp only [fee,actualRootNativeFeeAtMesh,NativePathFee.amount,actualRootRemainingFeesAtMesh]
  ring

/-- A concrete result of one real native Column call. It keeps one actual
family and SAME chosen NodeOutput/paid edge. No childAt/daughter carrier,
energy hypothesis, class payment or returned-count bound is stored as an
input. The native analytic estimate is the output field `energy_bound`. -/
structure RootColumnPaidResult
    (paid : NativePaidPathNode C.globalBase)(epsNode : ℝ)(budget : ℕ)
    (mesh : ℝ)(hmesh : 0≤ mesh)(root : O)
    (constant epsilon Bsrc : ℝ)(control : Finset (ℕ×ℕ))(degree : ℕ)
    (boxes : ℕ→Finset (Fin 4→ℤ))
    (sourceEnergy fixedFactor oldTerm : ℝ)(returnedCoefficient : Finset alpha→ℝ) where
  deleted : Finset alpha
  family : SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz root
  choice : family=emptyReturnedForest ∨
    ∃(chosen : ReachableNode C 0)
      (out : NodeOutput hH chosen constant epsilon Bsrc control degree boxes)
      (hdeleted : (∑i∈deleted,C.originalWeight i)≤rootDetectorDeletion C.originalWeight+mesh)
      (edge : RootTraceEdge (C:=C) chosen.coordinates (chosen.unit*chosen.state.rowWidth)
        (chosen.unit*Real.logb chosen.localBase (volume (chosen.input hH)))
        (Real.logb C.globalBase ((Ideal.span {chosen.presentation.mult}).absNorm:ℝ))),
      chosen.presentation.mult=root ∧
      edge.node=paid.lengthLift (rootSourceLength C.originalWeight-paid.length) ∧
      edge.fee=actualRootNativeFeeAtMesh C s epsNode budget deleted mesh hmesh hdeleted ∧
      rootNativePaidCoefficient C s paid epsNode budget mesh deleted=
        C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
          edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount) ∧
      edge.node.coordinate 1=paid.coordinate 1 ∧family.value=out.family.value
  energy_bound : sourceEnergy≤fixedFactor*(oldTerm+returnedCoefficient deleted*family.value)
end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.root_native_paid_coefficient_eq
