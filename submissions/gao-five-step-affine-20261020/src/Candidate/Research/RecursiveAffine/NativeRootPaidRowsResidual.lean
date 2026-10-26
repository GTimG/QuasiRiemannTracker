/- The actual ROOT paid-column outputs are summed with their original native coefficients.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootPaidRowsJoined
import Candidate.Research.RecursiveAffine.NativeSelectedRawColumnsSum
import Candidate.Research.RecursiveAffine.NativeSelectedScalarLabels
import Candidate.Research.RecursiveAffine.NativeSelectedFamilyResidual
import Candidate.Research.RecursiveAffine.NativeRootColumnPaidResult
import Candidate.Research.RecursiveAffine.NativeRootPaidSource

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass Cycle63FinalLow Cycle63FinalCapacity
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentCommonProfile CenteredMomentFiniteProfileExceptional Cycle153Geometry Cycle153JointCount
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondCanonicalScalar CenteredMomentEnergyState CenteredMomentFirstAmplificationChoice
open Cycle153RegionalLow Cycle153SourceSchedule Cycle153Reachable Cycle153RootStep Cycle153ActualSourceGates
variable {alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M≤H}{C : SourceContext (α:=alpha) M H}
noncomputable local instance rootPaidRowsResidualLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger

/-- Transport the literal ROOT paid results to the SAME ordinary-datum
residual shell. Varying first ray characters are retained row by row.
The source bound comes only from each actual paid result. -/
def actualRootPaidRowsResidual
    (s : Input alpha)(p : Profiles (1/4) (9/4))(Cs : ℝ)
    (caps : GeometryAffineLowSourceGates s p Cs C.globalBase)
    (budget : ℕ)(hcard : Fintype.card alpha≤budget)
    (g : GeometryAffineLowSchedule)(epsNode epsShell epsV : ℝ)
    (hepsShell : 0≤epsShell)(hepsV : 0<epsV)
    (hlarge : actualSelectedScalarThreshold budget epsV hepsV≤C.globalBase)
    (reflected second : Bool)(firstHeight : ℝ)(key : ℤ×(Fin 5→ℤ))
    (hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key)
    (hf1 : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val)
      1 s.ν s.W s.P≠0)
    (Psi : 𝓢(ℝ,ℂ))(sideLower : ℝ)
    (hside : ∀l,sideLower≤geometryHighSide reflected (Real.logb C.globalBase (volume s))
      (geometryExponents s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (nativeMu/64) (firstIndex l).1.val.1.val))
    (mesh : ℝ)(hmesh : 0 ≤ mesh)(feeBudget : ℕ)
    (Cg fixed : ℝ)(hCg : 0≤Cg)(hfixed : 0≤fixed)
    (constant epsilon Bsrc : ℝ)(control : Finset (ℕ×ℕ))(degree : ℕ)
    (boxes : ℕ→Finset (Fin 4→ℤ)) :=
  let Z:=C.globalBase
  let amp:=rootSourceAmp C.originalWeight
  let Rows:=NativeLowRows reflected s 1 1 Z 1 amp (nativeMu/64) (nativeMu/8) (9/4)
    firstHeight (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2 firstIndex
  let selected:=actualCanonicalSelectedFamily reflected second s 1 1 Z 1 amp (nativeMu/64)
    (nativeMu/8) (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2 firstIndex
  let ch:=selected.chain reflected second s 1 1 Z 1 amp (nativeMu/64) (nativeMu/8) (9/4)
    firstHeight (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2 firstIndex
  let gg:=selected.geometry reflected second s 1 1 Z 1 amp (nativeMu/64) (nativeMu/8) (9/4)
    firstHeight (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2 firstIndex hf1
  let datum:=fun r : Rows=>geometryLowSecondDatum reflected s 1 1 Z 1 amp (nativeMu/64) (nativeMu/8)
    (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2
  fun (Ds : Finset (Ideal O))(zs : Rows→Finset O)
    (hE : ∀r : Rows,Supported (if second then (datum r).D else (datum r).C))
    (chi0 : Rows→RayFourExpansion.RayCharacter)(Q : Ideal O)(m : O)
    (ray : RayFourExpansion.RayCharacter)(sourceHeight : ℝ)=>
  let mass:=fun l=>geometryFirstHighMass reflected s 1 1 Psi 1 Z (nativeMu/64) g.δ
    (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val
  let energy:=fun r : Rows=>∑D∈Ds,∑z∈zs r,(1:ℝ)*‖CenteredMomentCommonPairedSource.normalizedColumn
    (withHeight (ch r).first ((gg r).datum.τ ray) sourceHeight)
    (ch r).E₂ (hE r) (ch r).R₂ (datum r).seed D z‖^2
  let outer:=1+3*g.δ-amp+oldLoss epsNode
  let consume:=actual_root_paid_rows_joined (hH:=hH) s p Cs caps budget hcard g epsNode epsShell epsV
    hepsShell hepsV hlarge reflected second firstHeight key hz1 hz2 firstIndex hf1 Psi sideLower hside
    mesh hmesh feeBudget Cg fixed hCg hfixed constant epsilon Bsrc control degree boxes
  fun (rawRoot : Rows→O)(paid : Rows→NativePaidPathNode Z) result=>
  let actualBound:=consume rawRoot paid energy result
  let identity:=selected.actualUnitWeightedResidualIdentity reflected second s 1 1 Z 1 amp
    (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one
    key hz1 hz2 firstIndex hf1 hE chi0 Q m mass ray sourceHeight zs Ds outer
  identity.le.trans actualBound
end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualRootPaidRowsResidual
