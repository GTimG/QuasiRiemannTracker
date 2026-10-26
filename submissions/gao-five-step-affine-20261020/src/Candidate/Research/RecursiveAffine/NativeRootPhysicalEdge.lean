/- Actual root native LOW edge with a compensated volume majorant. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootEdgeCapacity
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

/-- The original plane majorizes the actual raw source log volume. -/
theorem actual_root_volume_majorant
    (s : Input α) (hscale : ∀i,s.P i=C.globalBase^(C.originalWeight i))
    (hwindow : @Cycle63.AffineLedger.PlainWindow Cycle153.Root.rootLedger
      (length C.globalBase s.X₁) (length C.globalBase s.X₂) (∑i,C.originalWeight i)) :
    Real.logb C.globalBase (volume s)≤rootSourceLength C.originalWeight := by
  have hp:=(actual_root_cell_slack s C.globalBase C.originalWeight hwindow).2.2.2.2.1
  have h1:=raw_log_le_length C.globalBase s.X₁ C.globalBase_gt_one s.X₁_pos
  have h2:=raw_log_le_length C.globalBase s.X₂ C.globalBase_gt_one s.X₂_pos
  have hs : (∑i,Real.logb C.globalBase (s.P i))=∑i,C.originalWeight i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hscale,Real.logb_rpow (zero_lt_one.trans C.globalBase_gt_one) C.globalBase_gt_one.ne']
  rw [input_volume_log,hs]
  linarith only [hp,h1,h2]

/-- The literal root source, genuine plane and actual detector produce
one physical edge. The volume-majorant compensation preserves the raw
outside coefficient exactly, while licensing the model's real Red
recurrence. No root energy, returned-count or final payment is assumed. -/
def actual_root_native_trace_edge
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
    (childScale childPrefix scalePad : ℝ) (hscaleFine : scalePad ≤ 1/1000000000000)
    (hrelative : childScale+childPrefix ≤ praw.coordinate 2+scalePad) :
    let r:=nativeRootStepValues s ch chi t C.globalBase budget b Mrow omega xi reserve C.originalWeight
      g second L alloc Rdel
    let x:=rootCoordinates r.b r.rootSlack r.V r.Red r.ell
    RootTraceEdge (C:=C) x childScale r.childA childPrefix := by
  intro r x
  have hn:=actual_outer_native_root_step s ch chi t C.globalBase C.globalBase_gt_one budget b Mrow
    omega xi reserve mesh C.originalWeight g hb hcard hs hlower C.originalWeight_nonneg hscale hwindow
    second L alloc row hne Rdel hRdel hproper hcover hdelmesh homega hR2 hPuncture hfinite
  have hc:=actual_root_trace_capacity s ch chi t C.globalBase C.globalBase_gt_one budget b hb hcard
    hs C.originalWeight C.originalWeight_nonneg hscale hwindow g.first_nonzero g.second_nonzero
    second L alloc row hne Rdel hRdel hproper hcover
  let a:=rootSourceLength C.originalWeight-praw.length
  let p:=praw.lengthLift a
  have ha : 0 ≤ a := by
    dsimp only [a]
    rw [hlength]
    exact sub_nonneg.mpr (actual_root_volume_majorant s hscale hwindow)
  have hAone : rootSourceLength C.originalWeight ≤ 1 := by
    have hz : 0 ≤ ∑i,C.originalWeight i := Finset.sum_nonneg (fun i _=>C.originalWeight_nonneg i)
    have hlam : 0 ≤ Coordinates.outerLambda-1 := by norm_num [Coordinates.outerLambda]
    have hbnd : Coordinates.outerB ≤ 1 := by norm_num [Coordinates.outerB]
    dsimp only [rootSourceLength]
    nlinarith only [mul_nonneg hlam hz,hbnd]
  have hpA : p.volumeLength=rootSourceLength C.originalWeight := by
    rw [NativePaidPathNode.lengthLift_volumeLength]
    dsimp only [NativePaidPathNode.volumeLength]
    rw [hunit]
    dsimp only [a]
    ring
  have hpA4 : praw.length+a ≤ 4 := by dsimp only [a];linarith only [hAone]
  have hcap : r.childA ≤ p.volumeLength-fee.modelDeletion-p.commonLog-
      Real.logb C.globalBase (formalReductionFactor L alloc (ch.final chi t).P)+r.pad := by
    rw [hpA,hD,NativePaidPathNode.lengthLift_commonLog,hcommon]
    exact hc.2
  have hbmodel : Coordinates.b x=rootSourceCell C.originalWeight := rfl
  have hsmodel : Coordinates.rootSlack x=rootSourceSlack C.originalWeight := rfl
  have hAmodel:=root_length_model_alias C.originalWeight x hbmodel hsmodel
  refine {
    node:=p,unit_eq:=hunit,fee:=fee
    sourceGates:=praw.lengthLift_sourceGates a ha hpA4 source
    fineSource:=praw.lengthLift_fineSourceGates a fine
    fineFee:=hfee,remainingFee:=hremaining
    V:=r.V,Red:=r.Red
    residualF:=Real.logb C.globalBase (formalReductionFactor L alloc (ch.final chi t).P)
    residualF_nonneg:=hc.1,capacityPad:=r.pad,scalePad:=scalePad
    root_scale:=hrow,root_length:=?_,relative_scale:=?_,length_step:=?_,capacity:=hcap
    junction_model:=hq,deletion_model:=(hD.trans (root_deletion_model_alias C.originalWeight x hbmodel))
    missing_model:=rfl,reduction_model:=rfl
    amplifierError:=0,amplifierError_nonneg:=le_rfl,fineAmplifierError:=by norm_num
    fineScalePad:=hscaleFine
    fineCapacityPad:=by linarith only [hn.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
    amplifier_model:=?_ }
  · rw [hpA,hAmodel.1]
    have hslack : Coordinates.rootSlack x ≤ Coordinates.mesh := hn.2.2.2.1
    have hlam : 0 ≤ Coordinates.outerLambda-1 := by norm_num [Coordinates.outerLambda]
    dsimp only [Coordinates.A0,Coordinates.upperRootLength1]
    nlinarith only [mul_nonneg hlam (sub_nonneg.mpr hslack)]
  · rw [NativePaidPathNode.lengthLift_coordinate_two]
    exact hrelative
  · rw [hpA,hD]
    exact hn.2.2.2.2.2.2.2.2.2.2.1
  · rw [NativePaidPathNode.lengthLift_amplification,hamp,root_amp_model_alias C.originalWeight x hbmodel]
    simp only [add_zero,le_refl]

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_root_native_trace_edge
