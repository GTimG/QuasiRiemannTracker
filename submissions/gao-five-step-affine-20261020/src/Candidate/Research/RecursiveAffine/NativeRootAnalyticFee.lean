/- Literal ROOT analytic fee agrees with its actual paid source receipt.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootPaidRowsResidual

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open CenteredMomentCommonRadialData
open HeckeFamily CenteredMomentAmplificationChildInput Cycle153Reachable Cycle153SourceSchedule
open Cycle63InitialMass Cycle153JointCount Cycle153RootStep
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable (C : SourceContext (α:=alpha) M H)(s : Input alpha)
noncomputable local instance rootAnalyticFeeLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger

/-- Driver, dictionary, shell and actual external-mesh costs are each
present once. The SAME chosen mass-bin loss is kept outside the source
fee. No energy, path or count estimate is used in this identity. -/
theorem actual_root_analytic_fee_eq
    (g : GeometryAffineLowSchedule)(epsNode epsV epsShell mesh sideLower : ℝ)(budget : ℕ)
    (hdelta : g.δ=nativeDriverRate budget)
    (hV : epsV=postDictionaryRate C.Bnorm budget)
    (hShell : epsShell=postDictionaryRate C.Bnorm budget) :
    3*g.δ-sideLower+3*g.δ+oldLoss epsNode+epsV+130*epsShell+actualRootSourcePad C s+
      2*g.δ*31*(Fintype.card alpha:ℝ)+Cycle63.AffineLedger.q*mesh=
      (3*nativeDriverRate budget-sideLower)+actualRootRemainingFeesAtMesh C s epsNode budget mesh :=by
  rw [hdelta,hV,hShell]
  unfold actualRootRemainingFeesAtMesh
  change 3*nativeDriverRate budget-sideLower+3*nativeDriverRate budget+oldLoss epsNode+
      postDictionaryRate C.Bnorm budget+130*postDictionaryRate C.Bnorm budget+actualRootSourcePad C s+
      2*nativeDriverRate budget*31*(Fintype.card alpha:ℝ)+Cycle153Geometry.Coordinates.q0*mesh=_
  ring
end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_root_analytic_fee_eq
