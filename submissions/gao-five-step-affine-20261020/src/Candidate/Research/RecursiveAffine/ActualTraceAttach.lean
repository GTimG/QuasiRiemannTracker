/- Prepend one literal native physical LOW edge to a selected path. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualTraceRebase

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153JointCount

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=α) M H} {j k : Fin 4}

/-- Arithmetic of the actual first edge, before it is joined to any
terminal count. Every field is a native source identity or physical
inequality. No returned-count, energy or final-payment bound occurs. -/
structure NativeTraceEdge (N : ReachableNode C j) (x : Fin 14 → ℝ)
    (childScale childLength childPrefix : ℝ) where
  node : NativePaidPathNode C.globalBase
  fee : NativePathFee
  sourceGates : node.SourceGates
  fineSource : node.FineSourceGates
  fineFee : fee.amount ≤ 1/1000000000000
  remainingFee : fee.junction*fee.modelDeletion+fee.amount ≤ 2
  V : ℝ
  Red : ℝ
  residualF : ℝ
  residualF_nonneg : 0 ≤ residualF
  capacityPad : ℝ
  scalePad : ℝ
  amplifierError : ℝ
  amplifierError_nonneg : 0 ≤ amplifierError
  fineAmplifierError : amplifierError ≤ 1/1000000000000
  fineScalePad : scalePad ≤ 1/1000000000000
  fineCapacityPad : capacityPad ≤ 1/1000000000000
  root_scale : node.scale = N.unit*N.state.rowWidth
  root_length : node.volumeLength = N.unit*Real.logb N.localBase
    (CenteredMomentAmplificationChildInput.volume (N.input hH))
  relative_scale : childScale+childPrefix-
    Real.logb C.globalBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ) ≤ node.coordinate 2+scalePad
  length_step : childLength = node.volumeLength-fee.modelDeletion-V-Red
  capacity : childLength ≤ node.volumeLength-fee.modelDeletion-node.commonLog-residualF+capacityPad
  prefix_preserved : ∀ i, prefixCoordinate (j.val+1) i → x i=N.coordinates i
  length_model : node.volumeLength = modelLength (pathStage j.val) x
  unit_model : node.unit = modelUnit (pathStage j.val) x
  junction_model : fee.junction = (innerStage j.val).q
  deletion_model : fee.modelDeletion = pathDeletion j.val x
  missing_model : V = pathV j.val x
  reduction_model : Red = pathRed j.val x
  amplifier_model : node.amplification ≤
    ![Cycle153Geometry.Coordinates.a1 x,Cycle153Geometry.Coordinates.a2 x,
      Cycle153Geometry.Coordinates.a3 x,Cycle153Geometry.Coordinates.a4 x] (pathStage j.val)+amplifierError

def prependArray {β : Type} (head : β) (tail : ℕ → β) : ℕ → β
  | 0 => head
  | n+1 => tail n

/-- The caller binds these identities by the actual native forest
attachment. Its selected HIGH part and source weight are not reselected. -/
structure AttachedPathBinding (N : ReachableNode C j) (child : ReachableNode C k)
    (F : N.Family hH)
    (Fc : SuffixFamily (hH:=hH) k.val (4-k.val) C.etaSeed N.localBase C.Bnorm C.Tz child.presentation.mult)
    (d : SuffixDepth (4-j.val)) (p : F.Prefix d)
    (dc : SuffixDepth (4-k.val)) (pc : Fc.Prefix dc)
    {x : Fin 14 → ℝ} {childScale childLength childPrefix : ℝ}
    (edge : NativeTraceEdge (hH:=hH) N x childScale childLength childPrefix) : Prop where
  offset : suffixOffset (4-j.val) d = suffixOffset (4-k.val) dc+1
  terminal_scale : (F.part d p).scale = (Fc.part dc pc).scale
  terminal_length : (F.part d p).length = (Fc.part dc pc).length
  terminal_amp : (F.part d p).amp = (Fc.part dc pc).amp
  terminal_multiplier : F.multiplier d p = Fc.multiplier dc pc
  weight : F.weight d p = C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
    edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount)*Fc.weight dc pc
  missing : N.unit*F.historyMissing d p = edge.node.coordinate 1+N.unit*Fc.historyMissing dc pc

/-- Construct the longer literal trace from the SAME actual child
trace and first physical source edge. The only attachment hypotheses are
identities of the native attached carrier; source arithmetic stays on
NativeTraceEdge, not on a desired terminal inequality. -/
def ActualPathTrace.prepend
    {N : ReachableNode C j} {child : ReachableNode C k} (hstage : k.val=j.val+1)
    {F : N.Family hH}
    {Fc : SuffixFamily (hH:=hH) k.val (4-k.val) C.etaSeed N.localBase C.Bnorm C.Tz child.presentation.mult}
    {d : SuffixDepth (4-j.val)} {p : F.Prefix d}
    {dc : SuffixDepth (4-k.val)} {pc : Fc.Prefix dc}
    (trace : ActualPathTrace hH child N.unit Fc dc pc)
    (edge : NativeTraceEdge (hH:=hH) N trace.coordinates
      (trace.scale 0) (trace.volumeLength 0) (trace.prefixLog 0))
    (binding : AttachedPathBinding (hH:=hH) N child F Fc d p dc pc edge) :
    ActualPathTrace hH N N.unit F d p where
  representedBase_eq := N.localBase_eq
  representedUnit_pos := N.unit_pos
  count := trace.count+1
  count_eq := by rw [binding.offset,←trace.count_eq]
  node := prependArray edge.node trace.node
  scale := prependArray edge.node.scale trace.scale
  volumeLength := prependArray edge.node.volumeLength trace.volumeLength
  amplification := prependArray edge.node.amplification trace.amplification
  prefixLog := prependArray
    (Real.logb C.globalBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ)) trace.prefixLog
  fee := prependArray edge.fee trace.fee
  missingCoordinate := prependArray edge.V trace.missingCoordinate
  reductionCoordinate := prependArray edge.Red trace.reductionCoordinate
  residualF := prependArray edge.residualF trace.residualF
  capacityPad := prependArray edge.capacityPad trace.capacityPad
  scalePad := prependArray edge.scalePad trace.scalePad
  sourceGates := by
    intro i hi
    cases i with
    | zero => exact edge.sourceGates
    | succ i => exact trace.sourceGates i (by omega)
  fineSource := by
    intro i hi
    cases i with
    | zero => exact edge.fineSource
    | succ i => exact trace.fineSource i (by omega)
  fineFee := by
    intro i hi
    cases i with
    | zero => exact edge.fineFee
    | succ i => exact trace.fineFee i (by omega)
  fineScalePad := by
    intro i hi
    cases i with
    | zero => exact edge.fineScalePad
    | succ i => exact trace.fineScalePad i (by omega)
  fineCapacityPad := by
    intro i hi
    cases i with
    | zero => exact edge.fineCapacityPad
    | succ i => exact trace.fineCapacityPad i (by omega)
  remainingFee := by
    intro i hi
    cases i with
    | zero => exact edge.remainingFee
    | succ i => exact trace.remainingFee i (by omega)
  node_eq := by
    intro i hi
    cases i with
    | zero => exact ⟨rfl,rfl,rfl⟩
    | succ i => exact trace.node_eq i (by omega)
  root_scale := edge.root_scale
  root_length := edge.root_length
  root_prefix := rfl
  terminal_scale := trace.terminal_scale.trans (congrArg (fun a : ℝ => N.unit*a) binding.terminal_scale.symm)
  terminal_length := trace.terminal_length.trans (congrArg (fun a : ℝ => N.unit*a) binding.terminal_length.symm)
  terminal_amp := trace.terminal_amp.trans (congrArg (fun a : ℝ => N.unit*a) binding.terminal_amp.symm)
  terminal_prefix := trace.terminal_prefix.trans
    (congrArg (fun v : O => Real.logb C.globalBase ((Ideal.span {v}).absNorm:ℝ)) binding.terminal_multiplier.symm)
  relative_scale := by
    intro i hi
    cases i with
    | zero => exact edge.relative_scale
    | succ i => exact trace.relative_scale i (by omega)
  length_step := by
    intro i hi
    cases i with
    | zero => exact edge.length_step
    | succ i => exact trace.length_step i (by omega)
  residualF_nonneg := by
    intro i hi
    cases i with
    | zero => exact edge.residualF_nonneg
    | succ i => exact trace.residualF_nonneg i (by omega)
  capacity := by
    intro i hi
    cases i with
    | zero => exact edge.capacity
    | succ i => exact trace.capacity i (by omega)
  weight := by
    rw [Finset.prod_range_succ']
    simp only [prependArray]
    rw [←trace.weight]
    simpa only [mul_comm] using binding.weight
  missing := by
    rw [Finset.sum_range_succ']
    simp only [prependArray]
    rw [←trace.missing]
    simpa only [add_comm] using binding.missing
  coordinates := trace.coordinates
  physical_prefix := by
    convert trace.physical_prefix using 1 <;> omega
  prefix_preserved := edge.prefix_preserved
  length_model := by
    intro i hi
    cases i with
    | zero => exact edge.length_model
    | succ i =>
      have h := trace.length_model i (by omega)
      simpa only [prependArray,hstage,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  unit_model := by
    intro i hi
    cases i with
    | zero => exact edge.unit_model
    | succ i =>
      have h := trace.unit_model i (by omega)
      simpa only [prependArray,hstage,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  junction_model := by
    intro i hi
    cases i with
    | zero => exact edge.junction_model
    | succ i =>
      have h := trace.junction_model i (by omega)
      simpa only [prependArray,hstage,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  deletion_model := by
    intro i hi
    cases i with
    | zero => exact edge.deletion_model
    | succ i =>
      have h := trace.deletion_model i (by omega)
      simpa only [prependArray,hstage,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  missing_model := by
    intro i hi
    cases i with
    | zero => exact edge.missing_model
    | succ i =>
      have h := trace.missing_model i (by omega)
      simpa only [prependArray,hstage,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  reduction_model := by
    intro i hi
    cases i with
    | zero => exact edge.reduction_model
    | succ i =>
      have h := trace.reduction_model i (by omega)
      simpa only [prependArray,hstage,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
  amplifierError := prependArray edge.amplifierError trace.amplifierError
  amplifierError_nonneg := by
    intro i hi
    cases i with
    | zero => exact edge.amplifierError_nonneg
    | succ i => exact trace.amplifierError_nonneg i (by omega)
  fineAmplifierError := by
    intro i hi
    cases i with
    | zero => exact edge.fineAmplifierError
    | succ i => exact trace.fineAmplifierError i (by omega)
  amplifier_model := by
    intro i hi
    cases i with
    | zero => exact edge.amplifier_model
    | succ i =>
      have h := trace.amplifier_model i (by omega)
      simpa only [prependArray,hstage,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.ActualPathTrace.prepend
