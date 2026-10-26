/- Actual root native LOW edge with a compensated volume majorant. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootPhysicalEdge
import Candidate.Research.RecursiveAffine.ActualTraceTerminal
import Candidate.Research.RecursiveAffine.NativeLengthLift
import Candidate.Research.RecursiveAffine.RootCoordinates
import Candidate.Research.RecursiveAffine.RootReturnedPayment

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 8000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153JointCount Cycle153RootStep Cycle153RegionalLow Cycle153Geometry
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentDivisorAllocation
open CenteredMomentCommonProfile CenteredMomentEnergyBands CenteredMomentDivisorRetained
open CenteredMomentDivisorRaw CenteredMomentSourceLiveColumn CenteredMomentSectorLocalization
open Cycle63FinalLow Cycle63InitialMass CenteredMomentEnergyInputParentCapacity

variable {α : Type} [Fintype α] [DecidableEq α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {C : SourceContext (α:=α) M H}
  {hH : RayOrthogonality.globalUnits M ≤ H}

/-- The literal root source, genuine plane and actual detector produce
one physical edge. The volume-majorant compensation preserves the raw
outside coefficient exactly, while licensing the model's real Red
recurrence. No root energy, returned-count or final payment is assumed. -/
theorem actual_root_column_edge_at_chosen
    (s : Input α) (ch : Chain s) (chi : Character) (t : ℝ)
    (budget : ℕ) (b Mrow omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch C.globalBase Mrow (rootSourceAmp C.originalWeight) omega xi b budget)
    (hb : 1 ≤ b) (hcard : Fintype.card α ≤ budget)
    (hs : s.upper ≤ b) (hlower : 1 ≤ s.lower)
    (hscale : ∀i,s.P i=C.globalBase^(C.originalWeight i))
    (hwindow : @Cycle63.AffineLedger.PlainWindow Cycle153.Root.rootLedger
      (length C.globalBase s.X₁) (length C.globalBase s.X₂) (∑i,C.originalWeight i))
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (row : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final chi t).toSource second L alloc row≠0)
    (Rdel : Finset α) (hRdel : Rdel ⊆ ch.indices L alloc) (hproper : Rdel≠ch.indices L alloc)
    (hcover : Rdel=ch.indices L alloc ∨ rootDetectorDeletion C.originalWeight ≤ ∑i∈Rdel,C.originalWeight i)
    (hdelmesh : (∑i∈Rdel,C.originalWeight i) ≤ rootDetectorDeletion C.originalWeight+mesh)
    (homega : omega=frequencyLoss C.globalBase 32 xi+reserve*1)
    (hR2 : ch.R₂=(1:Ideal O)*ch.C₁) (hPuncture : ch.R₂*ch.E₂≠0)
    (hfinite : Real.logb C.globalBase 128+(2*(budget:ℝ)*Real.logb C.globalBase b+
      Real.logb C.globalBase (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000)
    (praw : NativePaidPathNode C.globalBase)
    (hunit : praw.unit=1) (hrow : praw.scale ≤ 1)
    (hlength : praw.length=Real.logb C.globalBase (volume s))
    (hamp : praw.amplification=rootSourceAmp C.originalWeight)
    (hcommon : praw.commonLog=Real.logb C.globalBase (ch.C₁.absNorm:ℝ)+
      Real.logb C.globalBase (ch.E₂.absNorm:ℝ))
    (source : praw.SourceGates) (fine : praw.FineSourceGates)
    (fee : NativePathFee) (hfee : fee.amount ≤ 1/1000000000000)
    (hremaining : fee.junction*fee.modelDeletion+fee.amount ≤ 2)
    (hq : fee.junction=Coordinates.q0)
    (hD : fee.modelDeletion=rootSourceDeletion C.originalWeight)
    (chosen : ReachableNode C 0)
    (hcoordinates :
      let r:=nativeRootStepValues s ch chi t C.globalBase budget b Mrow omega xi reserve C.originalWeight
        g second L alloc Rdel
      chosen.coordinates=rootCoordinates r.b r.rootSlack r.V r.Red r.ell)
    (scalePad : ℝ)(hscaleFine : scalePad ≤ 1/1000000000000)
    (hrelative : chosen.unit*chosen.state.rowWidth+
      Real.logb C.globalBase ((Ideal.span {chosen.presentation.mult}).absNorm:ℝ)≤praw.coordinate 2+scalePad) :
    ∃edge : RootTraceEdge (C:=C) chosen.coordinates (chosen.unit*chosen.state.rowWidth)
      (chosen.unit*Real.logb chosen.localBase (volume (chosen.input hH)))
      (Real.logb C.globalBase ((Ideal.span {chosen.presentation.mult}).absNorm:ℝ)),
      edge.node=praw.lengthLift (rootSourceLength C.originalWeight-praw.length) ∧ edge.fee=fee :=by
  let r:=nativeRootStepValues s ch chi t C.globalBase budget b Mrow omega xi reserve C.originalWeight
    g second L alloc Rdel
  let x:=rootCoordinates r.b r.rootSlack r.V r.Red r.ell
  let edge:=actual_root_native_trace_edge (C:=C) s ch chi t budget b Mrow omega xi reserve mesh
    g hb hcard hs hlower hscale hwindow second L alloc row hne Rdel hRdel hproper hcover hdelmesh
    homega hR2 hPuncture hfinite praw hunit hrow hlength hamp hcommon source fine fee hfee hremaining hq hD
    (chosen.unit*chosen.state.rowWidth)
    (Real.logb C.globalBase ((Ideal.span {chosen.presentation.mult}).absNorm:ℝ)) scalePad hscaleFine hrelative
  have facts:=actual_outer_native_root_step s ch chi t C.globalBase C.globalBase_gt_one budget b Mrow
    omega xi reserve mesh C.originalWeight g hb hcard hs hlower C.originalWeight_nonneg hscale hwindow
    second L alloc row hne Rdel hRdel hproper hcover hdelmesh homega hR2 hPuncture hfinite
  have hA:=facts.2.2.2.2.2.2.2.2.2.2.1
  have hxb : Coordinates.b x=rootSourceCell C.originalWeight:=rfl
  have hxs : Coordinates.rootSlack x=rootSourceSlack C.originalWeight:=rfl
  have hlen:=root_length_model_alias C.originalWeight x hxb hxs
  have hdel:=root_deletion_model_alias C.originalWeight x hxb
  have hAmodel : r.childA=modelLength (0:Fin 4) x:=by
    change r.childA=Coordinates.A0 x-Coordinates.d0 x-r.V-r.Red
    rw [←hlen.1,←hdel]
    exact hA
  have hvolume : chosen.unit*Real.logb chosen.localBase (volume (chosen.input hH))=r.childA:=by
    rw [chosen.volume_model,hcoordinates]
    exact hAmodel.symm
  refine ⟨{
    node:=edge.node,unit_eq:=edge.unit_eq,fee:=edge.fee,sourceGates:=edge.sourceGates,fineSource:=edge.fineSource,
    fineFee:=edge.fineFee,remainingFee:=edge.remainingFee,V:=edge.V,Red:=edge.Red,
    residualF:=edge.residualF,residualF_nonneg:=edge.residualF_nonneg,
    capacityPad:=edge.capacityPad,scalePad:=edge.scalePad,
    root_scale:=edge.root_scale,
    root_length:=by rw [hcoordinates];exact edge.root_length,
    relative_scale:=edge.relative_scale,
    length_step:=by rw [hvolume];exact edge.length_step,
    capacity:=by rw [hvolume];exact edge.capacity,
    junction_model:=edge.junction_model,
    deletion_model:=by rw [hcoordinates];exact edge.deletion_model,
    missing_model:=by rw [hcoordinates];exact edge.missing_model,
    reduction_model:=by rw [hcoordinates];exact edge.reduction_model,
    amplifierError:=edge.amplifierError,amplifierError_nonneg:=edge.amplifierError_nonneg,
    fineAmplifierError:=edge.fineAmplifierError,fineScalePad:=edge.fineScalePad,
    fineCapacityPad:=edge.fineCapacityPad,
    amplifier_model:=by rw [hcoordinates];exact edge.amplifier_model },rfl,rfl⟩

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_column_edge_at_chosen
