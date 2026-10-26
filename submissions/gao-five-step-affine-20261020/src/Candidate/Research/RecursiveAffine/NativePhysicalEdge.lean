/- Actual native physical LOW source to a full priced trace edge. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeEdgeCapacity
import Candidate.Research.RecursiveAffine.PhysicalStepCoordinates
import Candidate.Research.RecursiveAffine.ActualTraceTransport

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153JointCount Cycle153RegionalLow Cycle153Geometry Cycle153ReachableGeometry
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentDivisorAllocation
open CenteredMomentCommonProfile CenteredMomentEnergyBands CenteredMomentDivisorRetained
open CenteredMomentDivisorRaw CenteredMomentSourceLiveColumn CenteredMomentSectorLocalization
open Cycle63FinalLow Cycle63InitialMass

/-- A literal update changes future data only; the current actual source
unit, volume, deletion and amplifier remain the same. Its new V and Red
are precisely the physical next-step data. -/
theorem physical_current_models (j : Fin 4) (hj : j.val < 3) (x : Fin 14→ℝ)
    (V Red ell : ℝ) :
    let y:=extendCoordinates x (nextInner j hj) V Red ell
    modelUnit j y=modelUnit j x ∧ modelLength j y=modelLength j x ∧
      pathDeletion j.val y=pathDeletion j.val x ∧
      modelAmplification j y=modelAmplification j x ∧ pathV j.val y=V ∧ pathRed j.val y=Red := by
  fin_cases j <;> norm_num at hj
  all_goals simp [nextInner,extendCoordinates,modelUnit,modelLength,modelSlots,pathV,pathRed,
    modelAmplification,pathDeletion,pathStage,Coordinates.b, Coordinates.rootSlack, Coordinates.V0, Coordinates.V1, Coordinates.V2, Coordinates.V3, Coordinates.Red0, Coordinates.Red1, Coordinates.Red2, Coordinates.Red3, Coordinates.ell0, Coordinates.ell1, Coordinates.ell2, Coordinates.ell3, Coordinates.U0, Coordinates.U1, Coordinates.U2, Coordinates.U3, Coordinates.U4, Coordinates.A0, Coordinates.A1, Coordinates.A2, Coordinates.A3, Coordinates.A4, Coordinates.z0, Coordinates.z1, Coordinates.z2, Coordinates.z3, Coordinates.z4, Coordinates.capA0, Coordinates.capA1, Coordinates.capA2, Coordinates.capA3, Coordinates.capA4, Coordinates.gap0, Coordinates.gap1, Coordinates.gap2, Coordinates.gap3, Coordinates.gap4, Coordinates.a0, Coordinates.a1, Coordinates.a2, Coordinates.a3, Coordinates.a4, Coordinates.d0, Coordinates.d1, Coordinates.d2, Coordinates.d3, Coordinates.d4]

variable {α : Type} [Fintype α] [DecidableEq α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {hH : RayOrthogonality.globalUnits M ≤ H}
  {C : SourceContext (α:=α) M H} {j : Fin 4}

/-- Construct the edge from the SAME actual source chain, selected
residual allocation and detector deletion. Native arithmetic supplies F
and the full source capacity; the literal prefix presentation supplies
the relative scale. The remaining inputs are scheduled primitive source
facts and definitional bindings of the actual paid node. No energy,
count, final class payment or daughter-capacity bound is an input. -/
def actual_inner_native_trace_edge
    (N : ReachableNode C j) (hj : j.val < 3)
    (s : Input N.slots) (ch : Chain s) (chi : Character) (t : ℝ)
    (budget : ℕ) (b Mrow omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch N.localBase Mrow (nodeSourceAmp N) omega xi b budget)
    (hb : 1 ≤ b) (hcard : Fintype.card N.slots ≤ budget)
    (hs : s.upper ≤ b) (hlower : 1 ≤ s.lower)
    (hX1 : s.X₁=N.X1) (hX2 : s.X₂=N.X2)
    (hscale : ∀i,s.P i=N.localBase^(C.originalWeight i/N.unit))
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (row : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final chi t).toSource second L alloc row≠0)
    (Rdel : Finset N.slots) (hRdel : Rdel⊆ch.indices L alloc) (hproper : Rdel≠ch.indices L alloc)
    (hcover : Rdel=ch.indices L alloc ∨ nodeDetectorDeletion N ≤ ∑i∈Rdel,C.originalWeight i/N.unit)
    (hdelmesh : (∑i∈Rdel,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+mesh)
    (homega : omega=frequencyLoss N.localBase 32 xi+reserve*1)
    (hR2 : ch.R₂=N.state.puncture*ch.C₁) (hPuncture : ch.R₂*ch.E₂≠0)
    (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
      (2*(budget:ℝ)*Real.logb N.localBase b+
        Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000)
    (p : NativePaidPathNode C.globalBase)
    (hunit : p.unit=N.unit) (hrow : p.scale=N.unit*N.state.rowWidth)
    (hvolume : p.volumeLength=N.unit*Real.logb N.localBase (volume (N.input hH)))
    (hamp : p.amplification=N.unit*nodeSourceAmp N)
    (hcommon : p.commonLog=N.unit*(Real.logb N.localBase (ch.C₁.absNorm:ℝ)+
      Real.logb N.localBase (ch.E₂.absNorm:ℝ)))
    (source : p.SourceGates) (fine : p.FineSourceGates)
    (fee : NativePathFee) (hfee : fee.amount ≤ 1/1000000000000)
    (hremaining : fee.junction*fee.modelDeletion+fee.amount ≤ 2)
    (hq : fee.junction=(innerStage j.val).q)
    (hD : fee.modelDeletion=pathDeletion j.val N.coordinates)
    (childScale childPrefix scalePad : ℝ)
    (hscaleFine : scalePad ≤ 1/1000000000000)
    (hrelative : childScale+childPrefix-
      Real.logb C.globalBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ) ≤ p.coordinate 2+scalePad)
    (hgrid : (1/C.gridDenominator:ℝ) ≤ 1/10000000000000000000000000000000000000000) :
    let r:=nativeNodeStepValues N s ch chi t budget b Mrow omega xi reserve g second L alloc Rdel
    NativeTraceEdge (hH:=hH) N
      (extendCoordinates N.coordinates (nextInner j hj) r.V r.Red r.ell)
      childScale r.childA childPrefix := by
  intro r
  have hn:=actual_inner_native_node_step N s ch chi t budget b Mrow omega xi reserve mesh g hb hcard
    hs hlower hX1 hX2 hscale second L alloc row hne Rdel hRdel hproper hcover hdelmesh homega hR2 hPuncture hfinite
  have hc:=actual_inner_trace_capacity (hH:=hH) N s ch chi t budget b hb hcard hs hX1 hX2 hscale
    g.first_nonzero g.second_nonzero second L alloc row hne Rdel hRdel hproper hcover
  let F:=N.unit*Real.logb N.localBase (formalReductionFactor L alloc (ch.final chi t).P)
  have hcap : r.childA ≤ p.volumeLength-fee.modelDeletion-p.commonLog-F+r.pad := by
    rw [hvolume,hD,hcommon]
    exact hc.2
  have hmodels:=physical_current_models j hj N.coordinates r.V r.Red r.ell
  have hstage : pathStage j.val=j := by fin_cases j <;> rfl
  have hmodelAmp : modelAmplification j N.coordinates ≤ p.amplification ∧
      p.amplification ≤ modelAmplification j N.coordinates+42*N.unit*(1/C.gridDenominator) := by
    have ha:=nodeSourceAmp_bounds N
    have hlo:=mul_le_mul_of_nonneg_left ha.1 N.unit_pos.le
    have hhi:=mul_le_mul_of_nonneg_left ha.2 N.unit_pos.le
    rw [mul_div_cancel₀ _ N.unit_pos.ne'] at hlo
    rw [mul_add,mul_div_cancel₀ _ N.unit_pos.ne'] at hhi
    rw [hamp]
    constructor <;> nlinarith only [hlo,hhi]
  refine {
    node:=p, fee:=fee, sourceGates:=source, fineSource:=fine
    fineFee:=hfee,remainingFee:=hremaining
    V:=r.V,Red:=r.Red,residualF:=F,residualF_nonneg:=hc.1
    capacityPad:=r.pad,scalePad:=scalePad
    amplifierError:=42*N.unit*(1/C.gridDenominator)
    amplifierError_nonneg:=mul_nonneg (mul_nonneg (by norm_num) N.unit_pos.le)
      (one_div_nonneg.mpr (Nat.cast_nonneg _))
    fineAmplifierError:=by nlinarith [N.unit_le_one,N.unit_pos]
    fineScalePad:=hscaleFine
    fineCapacityPad:=by linarith only [hn.2.2.2.2.2.2.2.2]
    root_scale:=hrow,root_length:=hvolume,relative_scale:=hrelative
    length_step:=?_,capacity:=hcap
    prefix_preserved:=physical_next_prefix_preserved j hj N.coordinates r.V r.Red r.ell
    length_model:=?_,unit_model:=?_,junction_model:=hq,deletion_model:=?_
    missing_model:=hmodels.2.2.2.2.1.symm
    reduction_model:=hmodels.2.2.2.2.2.symm
    amplifier_model:=?_ }
  · rw [hvolume,hD,N.volume_model]
    exact hn.2.2.2.2.2.1
  · rw [hvolume,N.volume_model,hstage,hmodels.2.1]
  · rw [hunit,hstage,hmodels.1]
    exact N.unit_eq
  · rw [hD,hmodels.2.2.1]
  · change p.amplification ≤ modelAmplification (pathStage j.val)
      (extendCoordinates N.coordinates (nextInner j hj) r.V r.Red r.ell)+_
    rw [hstage,hmodels.2.2.2.1]
    exact hmodelAmp.2

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_inner_native_trace_edge
