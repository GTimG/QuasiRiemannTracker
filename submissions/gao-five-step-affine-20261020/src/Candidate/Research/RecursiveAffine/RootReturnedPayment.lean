/- Final physical prefix certificates used by the actual root returned forest. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualTraceAttach
import Candidate.Research.RecursiveAffine.NativeClassPathPayment
import Candidate.Research.RecursiveAffine.CorrectedPhysicalCoordinates
import Candidate.Research.RecursiveAffine.LiteralFamilyReturnedBound

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153JointCount Cycle153Geometry Cycle153ReachableGeometry

/-- The terminal stage 1 uses only the actually constructed physical
prefix. No constraints on future continuations are supplied. -/
theorem root_paidAt1_prefix (x : Fin 14→ℝ) (q : ℝ)
    (hq : Coordinates.q1≤q) (hqhi : q≤3/4)
    (hV : -(1/1000000000000:ℝ)≤Coordinates.historicalMissing1 x)
    (hRed : -(1/1000000000000:ℝ)≤Coordinates.historicalReduction1 x)
    (hp : PrefixRows 1 x) : (1/10000000:ℝ)<Cycle153.paidAt1 q x := by
  have hj:=CorrectedCertificate1.robust_lower x (1/1000000000000000) le_rfl (fun i=>
    hp (CorrectedCertificate1.selected i) (by
      have hi:=CorrectedCertificate1.prefix_admissible i
      omega))
  have hw:=prefix_gate hp (14:Fin 62) (by norm_num [gateDepth])
  have hg:=prefix_gate hp (15:Fin 62) (by norm_num [gateDepth])
  change (1568511/1000000000000000:ℝ)<Coordinates.outgoing1 x at hw
  change (1568511/1000000000000000:ℝ)<Coordinates.allBinGrowth1 x at hg
  have hW : 0≤Coordinates.outgoing1 x := by linarith only [hw]
  have hG : 0≤((50/3)/(5-2*Coordinates.q1)^2)*Coordinates.outgoing1 x-
      Coordinates.returnedLength1 x := by
    change 0≤Coordinates.allBinGrowth1 x
    linarith only [hg]
  rw [←Cycle153.paidAt1_junction] at hj
  exact Cycle153.corrected_all_bins_with_robust_missing (by norm_num [Coordinates.q1])
    hq hqhi hW hV hRed hG hj

/-- The terminal stage 2 uses only the actually constructed physical
prefix. No constraints on future continuations are supplied. -/
theorem root_paidAt2_prefix (x : Fin 14→ℝ) (q : ℝ)
    (hq : Coordinates.q2≤q) (hqhi : q≤3/4)
    (hV : -(1/1000000000000:ℝ)≤Coordinates.historicalMissing2 x)
    (hRed : -(1/1000000000000:ℝ)≤Coordinates.historicalReduction2 x)
    (hp : PrefixRows 2 x) : (1/10000000:ℝ)<Cycle153.paidAt2 q x := by
  have hj:=CorrectedCertificate2.robust_lower x (1/1000000000000000) le_rfl (fun i=>
    hp (CorrectedCertificate2.selected i) (by
      have hi:=CorrectedCertificate2.prefix_admissible i
      omega))
  have hw:=prefix_gate hp (30:Fin 62) (by norm_num [gateDepth])
  have hg:=prefix_gate hp (31:Fin 62) (by norm_num [gateDepth])
  change (1568511/1000000000000000:ℝ)<Coordinates.outgoing2 x at hw
  change (1568511/1000000000000000:ℝ)<Coordinates.allBinGrowth2 x at hg
  have hW : 0≤Coordinates.outgoing2 x := by linarith only [hw]
  have hG : 0≤((50/3)/(5-2*Coordinates.q2)^2)*Coordinates.outgoing2 x-
      Coordinates.returnedLength2 x := by
    change 0≤Coordinates.allBinGrowth2 x
    linarith only [hg]
  rw [←Cycle153.paidAt2_junction] at hj
  exact Cycle153.corrected_all_bins_with_robust_missing (by norm_num [Coordinates.q2])
    hq hqhi hW hV hRed hG hj

/-- The terminal stage 3 uses only the actually constructed physical
prefix. No constraints on future continuations are supplied. -/
theorem root_paidAt3_prefix (x : Fin 14→ℝ) (q : ℝ)
    (hq : Coordinates.q3≤q) (hqhi : q≤3/4)
    (hV : -(1/1000000000000:ℝ)≤Coordinates.historicalMissing3 x)
    (hRed : -(1/1000000000000:ℝ)≤Coordinates.historicalReduction3 x)
    (hp : PrefixRows 3 x) : (1/10000000:ℝ)<Cycle153.paidAt3 q x := by
  have hj:=CorrectedCertificate3.robust_lower x (1/1000000000000000) le_rfl (fun i=>
    hp (CorrectedCertificate3.selected i) (by
      have hi:=CorrectedCertificate3.prefix_admissible i
      omega))
  have hw:=prefix_gate hp (46:Fin 62) (by norm_num [gateDepth])
  have hg:=prefix_gate hp (47:Fin 62) (by norm_num [gateDepth])
  change (1568511/1000000000000000:ℝ)<Coordinates.outgoing3 x at hw
  change (1568511/1000000000000000:ℝ)<Coordinates.allBinGrowth3 x at hg
  have hW : 0≤Coordinates.outgoing3 x := by linarith only [hw]
  have hG : 0≤((50/3)/(5-2*Coordinates.q3)^2)*Coordinates.outgoing3 x-
      Coordinates.returnedLength3 x := by
    change 0≤Coordinates.allBinGrowth3 x
    linarith only [hg]
  rw [←Cycle153.paidAt3_junction] at hj
  exact Cycle153.corrected_all_bins_with_robust_missing (by norm_num [Coordinates.q3])
    hq hqhi hW hV hRed hG hj

/-- The terminal stage 4 uses only the actually constructed physical
prefix. No constraints on future continuations are supplied. -/
theorem root_paidAt4_prefix (x : Fin 14→ℝ) (q : ℝ)
    (hq : Coordinates.q4≤q) (hqhi : q≤3/4)
    (hV : -(1/1000000000000:ℝ)≤Coordinates.historicalMissing4 x)
    (hRed : -(1/1000000000000:ℝ)≤Coordinates.historicalReduction4 x)
    (hp : PrefixRows 4 x) : (1/10000000:ℝ)<Cycle153.paidAt4 q x := by
  have hj:=CorrectedCertificate4.robust_lower x (1/1000000000000000) le_rfl (fun i=>
    hp (CorrectedCertificate4.selected i) (by
      have hi:=CorrectedCertificate4.prefix_admissible i
      omega))
  have hw:=prefix_gate hp (60:Fin 62) (by norm_num [gateDepth])
  have hg:=prefix_gate hp (61:Fin 62) (by norm_num [gateDepth])
  change (1568511/1000000000000000:ℝ)<Coordinates.outgoing4 x at hw
  change (1568511/1000000000000000:ℝ)<Coordinates.allBinGrowth4 x at hg
  have hW : 0≤Coordinates.outgoing4 x := by linarith only [hw]
  have hG : 0≤((50/3)/(5-2*Coordinates.q4)^2)*Coordinates.outgoing4 x-
      Coordinates.returnedLength4 x := by
    change 0≤Coordinates.allBinGrowth4 x
    linarith only [hg]
  rw [←Cycle153.paidAt4_junction] at hj
  exact Cycle153.corrected_all_bins_with_robust_missing (by norm_num [Coordinates.q4])
    hq hqhi hW hV hRed hG hj

def rootTerminalQ (j : Fin 4) : ℝ :=
  ![Coordinates.q1,Coordinates.q2,Coordinates.q3,Coordinates.q4] j

def rootModelAmp (j : Fin 4) (x : Fin 14→ℝ) : ℝ :=
  ![Coordinates.totalAmplification1 x,Coordinates.totalAmplification2 x,
    Coordinates.totalAmplification3 x,Coordinates.totalAmplification4 x] j

def rootHistoricalV (j : Fin 4) (x : Fin 14→ℝ) : ℝ :=
  ![Coordinates.historicalMissing1 x,Coordinates.historicalMissing2 x,
    Coordinates.historicalMissing3 x,Coordinates.historicalMissing4 x] j

def rootHistoricalRed (j : Fin 4) (x : Fin 14→ℝ) : ℝ :=
  ![Coordinates.historicalReduction1 x,Coordinates.historicalReduction2 x,
    Coordinates.historicalReduction3 x,Coordinates.historicalReduction4 x] j

def rootTotalD (j : Fin 4) (x : Fin 14→ℝ) : ℝ :=
  ![Coordinates.totalDeletion1 x,Coordinates.totalDeletion2 x,
    Coordinates.totalDeletion3 x,Coordinates.totalDeletion4 x] j

def rootPrevious (j : Fin 4) (x : Fin 14→ℝ) : ℝ :=
  ![Cycle153.previousPayment1 x,Cycle153.previousPayment2 x,
    Cycle153.previousPayment3 x,Cycle153.previousPayment4 x] j

def rootPaid (j : Fin 4) (q : ℝ) (x : Fin 14→ℝ) : ℝ :=
  ![Cycle153.paidAt1 q x,Cycle153.paidAt2 q x,
    Cycle153.paidAt3 q x,Cycle153.paidAt4 q x] j

theorem root_paid_prefix (j : Fin 4) (x : Fin 14→ℝ) (q : ℝ)
    (hq : rootTerminalQ j≤q) (hqhi : q≤3/4)
    (hV : -(1/1000000000000:ℝ)≤rootHistoricalV j x)
    (hRed : -(1/1000000000000:ℝ)≤rootHistoricalRed j x)
    (hp : PrefixRows (j.val+1) x) : (1/10000000:ℝ)<rootPaid j q x := by
  fin_cases j
  · exact root_paidAt1_prefix x q hq hqhi hV hRed hp
  · exact root_paidAt2_prefix x q hq hqhi hV hRed hp
  · exact root_paidAt3_prefix x q hq hqhi hV hRed hp
  · exact root_paidAt4_prefix x q hq hqhi hV hRed hp

theorem rootPaid_identity (j : Fin 4) (q : ℝ) (x : Fin 14→ℝ) :
    rootPaid j q x=Cycle153.correctedJointBudget q
      (1-rootHistoricalV j x-6*rootModelAmp j x)
      (Coordinates.upperRootLength1 x-rootHistoricalV j x-rootHistoricalRed j x-rootTotalD j x)
      (rootModelAmp j x) (rootPrevious j x) (rootHistoricalV j x) (rootHistoricalRed j x) := by
  fin_cases j <;>
    simp [rootPaid,rootHistoricalV,rootHistoricalRed,rootTotalD,rootModelAmp,rootPrevious,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.head_fin_const,
      Cycle153.paidAt1,Cycle153.paidAt2,Cycle153.paidAt3,Cycle153.paidAt4,
      Coordinates.outgoing1,Coordinates.outgoing2,Coordinates.outgoing3,Coordinates.outgoing4,
      Coordinates.returnedLength1,Coordinates.returnedLength2,Coordinates.returnedLength3,Coordinates.returnedLength4,
      Coordinates.upperRootLength1,Coordinates.upperRootLength2,Coordinates.upperRootLength3,Coordinates.upperRootLength4]

theorem suffixJunction_four (d : SuffixDepth 4) : suffixJunction 0 4 d=
    rootTerminalQ ⟨suffixOffset 4 d,suffixOffset_lt 4 d⟩ := by
  cases d with
  | none => rfl
  | some d => cases d with
    | none => rfl
    | some d => cases d with
      | none => rfl
      | some d => cases d with
        | none => rfl
        | some d => nomatch d

def innerModelAmp (i : ℕ) (x : Fin 14→ℝ) : ℝ :=
  ![Coordinates.a1 x,Coordinates.a2 x,Coordinates.a3 x,Coordinates.a4 x] (pathStage i)

/-- Finite identities of the literal five-stage schedule. They translate
the actually retained path coordinates into the corrected certificate. -/
theorem root_model_aggregates (n : ℕ) (hn : n<4) (x : Fin 14→ℝ) :
    (Coordinates.a0 x+(∑i∈Finset.range n,innerModelAmp i x)+innerModelAmp n x=
      rootModelAmp ⟨n,hn⟩ x) ∧
    (Coordinates.V0 x+(∑i∈Finset.range n,pathV i x)=rootHistoricalV ⟨n,hn⟩ x) ∧
    (Coordinates.Red0 x+(∑i∈Finset.range n,pathRed i x)=rootHistoricalRed ⟨n,hn⟩ x) ∧
    (Coordinates.d0 x+(∑i∈Finset.range n,pathDeletion i x)=rootTotalD ⟨n,hn⟩ x) ∧
    (Coordinates.q0*Coordinates.d0 x+
      (∑i∈Finset.range n,(innerStage i).q*pathDeletion i x)=rootPrevious ⟨n,hn⟩ x) := by
  interval_cases n <;>
    norm_num [Finset.sum_range_succ,innerModelAmp,pathStage,pathV,pathRed,pathDeletion,
      rootModelAmp,rootHistoricalV,rootHistoricalRed,rootTotalD,rootPrevious,
      Coordinates.totalAmplification1,Coordinates.totalAmplification2,
      Coordinates.totalAmplification3,Coordinates.totalAmplification4,
      Coordinates.historicalMissing1,Coordinates.historicalMissing2,
      Coordinates.historicalMissing3,Coordinates.historicalMissing4,
      Coordinates.historicalReduction1,Coordinates.historicalReduction2,
      Coordinates.historicalReduction3,Coordinates.historicalReduction4,
      Coordinates.totalDeletion1,Coordinates.totalDeletion2,Coordinates.totalDeletion3,Coordinates.totalDeletion4,
      Cycle153.previousPayment1,Cycle153.previousPayment2,Cycle153.previousPayment3,Cycle153.previousPayment4,
      innerStage,Cycle153.FixedStages.stage1,Cycle153.FixedStages.stage2,Cycle153.FixedStages.stage3,
      Coordinates.q1,Coordinates.q2,Coordinates.q3] <;> (try ring) <;> simp

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {C : SourceContext (α:=α) M H}

/-- The actual first LOW edge starts at the original source, whose
multiplier is one. Child arithmetic and the original source labels supply
these data before any returned class is considered. -/
structure RootTraceEdge (x : Fin 14→ℝ) (childScale childLength childPrefix : ℝ) where
  node : NativePaidPathNode C.globalBase
  unit_eq : node.unit=1
  fee : NativePathFee
  sourceGates : node.SourceGates
  fineSource : node.FineSourceGates
  fineFee : fee.amount ≤ 1/1000000000000
  remainingFee : fee.junction*fee.modelDeletion+fee.amount ≤ 2
  V : ℝ
  Red : ℝ
  residualF : ℝ
  residualF_nonneg : 0≤residualF
  capacityPad : ℝ
  scalePad : ℝ
  root_scale : node.scale≤1
  root_length : node.volumeLength≤Coordinates.upperRootLength1 x
  relative_scale : childScale+childPrefix≤node.coordinate 2+scalePad
  length_step : childLength=node.volumeLength-fee.modelDeletion-V-Red
  capacity : childLength≤node.volumeLength-fee.modelDeletion-node.commonLog-residualF+capacityPad
  junction_model : fee.junction=Coordinates.q0
  deletion_model : fee.modelDeletion=Coordinates.d0 x
  missing_model : V=Coordinates.V0 x
  reduction_model : Red=Coordinates.Red0 x
  amplifierError : ℝ
  amplifierError_nonneg : 0≤amplifierError
  fineAmplifierError : amplifierError ≤ 1/1000000000000
  fineScalePad : scalePad ≤ 1/1000000000000
  fineCapacityPad : capacityPad ≤ 1/1000000000000
  amplifier_model : node.amplification≤Coordinates.a0 x+amplifierError

theorem rootTerminalQ_floor (j : Fin 4) : (3/5:ℝ)≤rootTerminalQ j := by
  fin_cases j <;> norm_num [rootTerminalQ,Coordinates.q1,Coordinates.q2,Coordinates.q3,Coordinates.q4]

theorem rootTerminalQ_native (j : Fin 4) : Cycle63.Arithmetic.q0≤rootTerminalQ j := by
  have hq:=Cycle63.Arithmetic.q0_bounds.2
  fin_cases j <;>
    norm_num [rootTerminalQ,Coordinates.q1,Coordinates.q2,Coordinates.q3,Coordinates.q4] <;>
    linarith only [hq]

/-- The actual native first edge and the selected child's full path pay
one terminal HIGH class. Every raw normalizer and historical missing
radical is included. The fixed corrected certificate is derived from the
same path's physical prefix, rather than supplied as a count bound. -/
theorem root_trace_class_payment
    (N : ReachableNode C (0:Fin 4))
    (F : SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz N.presentation.mult)
    (d : SuffixDepth 4) (p : F.Prefix d)
    (trace : ActualPathTrace hH N 1 F d p)
    (edge : RootTraceEdge (C:=C) trace.coordinates
      (trace.scale 0) (trace.volumeLength 0) (trace.prefixLog 0))
    (b : Bool) (c : ((F.part d p).record b).Class)
    (error : ℝ)
    (hV : -(1/1000000000000:ℝ)≤rootHistoricalV ⟨trace.count,by rw [trace.count_eq]; exact suffixOffset_lt 4 d⟩ trace.coordinates)
    (hRed : -(1/1000000000000:ℝ)≤rootHistoricalRed
      ⟨trace.count,by rw [trace.count_eq]; exact suffixOffset_lt 4 d⟩ trace.coordinates)
    (herror : let n:=trace.count
      let delta:=2*((F.part d p).record b).zeroBin c-1
      (F.part d p).loss+5*(edge.amplifierError+
        (∑i∈Finset.range n,trace.amplifierError i)+trace.amplifierError n)+
      (∑i∈Finset.range (n+1),
        ((prependArray edge.node trace.node i).small delta+
        prependArray edge.fee.amount (fun i=>(trace.fee i).amount) i+
        LocalMoment.unmarkedDensity delta*prependArray edge.scalePad trace.scalePad i+
        Cycle153.commonLoss delta*prependArray edge.capacityPad trace.capacityPad i))≤error) :
    (C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
      edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount)*F.weight d p)*
      C.globalBase^(((F.part d p).record b).exponent c+((F.part d p).record b).missExp c+
        LocalMoment.unmarkedDensity (2*((F.part d p).record b).zeroBin c-1)*((F.part d p).record b).rowExp c+
        (edge.node.coordinate 1+F.historyMissing d p))≤C.globalBase^(1-1/10000000+error) := by
  let n:=trace.count
  have hn : n<4 := by dsimp only [n]; rw [trace.count_eq]; exact suffixOffset_lt 4 d
  let k : Fin 4:=⟨n,hn⟩
  let x:=trace.coordinates
  let R:=(F.part d p).record b
  let delta:=2*R.zeroBin c-1
  let nodes:=prependArray edge.node trace.node
  let m:=prependArray edge.node.scale trace.scale
  let A:=prependArray edge.node.volumeLength trace.volumeLength
  let amp:=prependArray edge.node.amplification trace.amplification
  let prefixLog:=prependArray (0:ℝ) trace.prefixLog
  let D:=prependArray edge.fee.modelDeletion (fun i=>(trace.fee i).modelDeletion)
  let V:=prependArray edge.V trace.missingCoordinate
  let Red:=prependArray edge.Red trace.reductionCoordinate
  let Fextra:=prependArray edge.residualF trace.residualF
  let pad:=prependArray edge.capacityPad trace.capacityPad
  let scalePad:=prependArray edge.scalePad trace.scalePad
  let q:=prependArray edge.fee.junction (fun i=>(trace.fee i).junction)
  let fees:=prependArray edge.fee.amount (fun i=>(trace.fee i).amount)
  let ampError:=edge.amplifierError+(∑i∈Finset.range n,trace.amplifierError i)+trace.amplifierError n
  have hk : (⟨suffixOffset 4 d,suffixOffset_lt 4 d⟩:Fin 4)=k := by
    apply Fin.ext
    exact trace.count_eq.symm
  have hqeq : suffixJunction 0 4 d=rootTerminalQ k := by rw [suffixJunction_four,hk]
  have hpays : R.Pays (rootTerminalQ k) (m (n+1)) (A (n+1)) (amp (n+1)) (F.part d p).loss := by
    dsimp only [m,A,amp,prependArray]
    rw [trace.terminal_scale,trace.terminal_length,trace.terminal_amp,one_mul,one_mul,one_mul,←hqeq]
    exact (F.part d p).pays b
  have hb:=hpays c
  have hqlo := rootTerminalQ_floor k
  have hzero : ((0:Fin 4):ℕ)=0 := rfl
  have hcert:=root_paid_prefix k x delta hb.1 hb.2.1 hV hRed
    (by simpa only [k,n,x,Fin.val_mk,hzero,Nat.zero_add] using trace.physical_prefix)
  have hmAmp : (∑i∈Finset.range (n+1),amp i)+amp (n+1)≤rootModelAmp k x+ampError := by
    have hs:=Finset.sum_le_sum (s:=Finset.range n) (fun i hi=>trace.amplifier_model i
      (Finset.mem_range.mp hi).le)
    have ht:=trace.amplifier_model n le_rfl
    simp only [hzero,Nat.zero_add] at hs ht
    have hi:=(root_model_aggregates n hn x).1
    change Coordinates.a0 x+(∑i∈Finset.range n,innerModelAmp i x)+innerModelAmp n x=_ at hi
    dsimp only [amp,prependArray]
    rw [Finset.sum_range_succ']
    simp only [prependArray] at *
    change (∑i∈Finset.range n,trace.amplification i)+edge.node.amplification+trace.amplification n≤_
    change (∑i∈Finset.range n,trace.amplification i)≤
      ∑i∈Finset.range n,(innerModelAmp i x+trace.amplifierError i) at hs
    change trace.amplification n ≤ innerModelAmp n x+trace.amplifierError n at ht
    rw [Finset.sum_add_distrib] at hs
    dsimp only [ampError]
    linarith only [hs,ht,edge.amplifier_model,hi]
  have hVm : (∑i∈Finset.range (n+1),V i)=rootHistoricalV k x := by
    dsimp only [V]
    rw [Finset.sum_range_succ']
    simp only [prependArray]
    have hs : (∑i∈Finset.range n,trace.missingCoordinate i)=∑i∈Finset.range n,pathV i x := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [hzero,Nat.zero_add] using trace.missing_model i (Finset.mem_range.mp hi)
    rw [hs,edge.missing_model]
    linarith only [(root_model_aggregates n hn x).2.1]
  have hRedm : (∑i∈Finset.range (n+1),Red i)=rootHistoricalRed k x := by
    dsimp only [Red]
    rw [Finset.sum_range_succ']
    simp only [prependArray]
    have hs : (∑i∈Finset.range n,trace.reductionCoordinate i)=∑i∈Finset.range n,pathRed i x := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [hzero,Nat.zero_add] using trace.reduction_model i (Finset.mem_range.mp hi)
    rw [hs,edge.reduction_model]
    linarith only [(root_model_aggregates n hn x).2.2.1]
  have hDm : (∑i∈Finset.range (n+1),D i)=rootTotalD k x := by
    dsimp only [D]
    rw [Finset.sum_range_succ']
    simp only [prependArray]
    have hs : (∑i∈Finset.range n,(trace.fee i).modelDeletion)=∑i∈Finset.range n,pathDeletion i x := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [hzero,Nat.zero_add] using trace.deletion_model i (Finset.mem_range.mp hi)
    rw [hs,edge.deletion_model]
    linarith only [(root_model_aggregates n hn x).2.2.2.1]
  have hPm : (∑i∈Finset.range (n+1),q i*D i)=rootPrevious k x := by
    dsimp only [q,D]
    rw [Finset.sum_range_succ']
    simp only [prependArray]
    have hs : (∑i∈Finset.range n,(trace.fee i).junction*(trace.fee i).modelDeletion)=
        ∑i∈Finset.range n,(innerStage i).q*pathDeletion i x := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [trace.junction_model i (Finset.mem_range.mp hi),trace.deletion_model i (Finset.mem_range.mp hi)]
      simp only [hzero,Nat.zero_add,x]
    rw [hs,edge.junction_model,edge.deletion_model]
    linarith only [(root_model_aggregates n hn x).2.2.2.2]
  apply native_class_path_payment R c (n+1) nodes m A amp prefixLog D V Red Fextra pad scalePad q fees
    (rootTerminalQ k) (F.part d p).loss (Coordinates.upperRootLength1 x) (rootModelAmp k x) ampError
    error (1/10000000) _ _ C.globalBase_gt_one hqlo (rootTerminalQ_native k) hpays
  · intro i hi
    cases i with
    | zero => exact ⟨rfl,rfl,rfl⟩
    | succ i => exact trace.node_eq i (by omega)
  · exact trace.terminal_prefix
  · rfl
  · intro i hi
    cases i with
    | zero => simpa only [m,prefixLog,nodes,scalePad,prependArray,sub_zero] using edge.relative_scale
    | succ i => exact trace.relative_scale i (by omega)
  · intro i hi
    cases i with
    | zero => exact edge.length_step
    | succ i => exact trace.length_step i (by omega)
  · intro i hi
    cases i with
    | zero => exact edge.residualF_nonneg
    | succ i => exact trace.residualF_nonneg i (by omega)
  · intro i hi
    cases i with
    | zero => exact edge.capacity
    | succ i => exact trace.capacity i (by omega)
  · exact edge.root_scale
  · exact edge.root_length
  · exact add_nonneg (add_nonneg edge.amplifierError_nonneg
      (Finset.sum_nonneg (fun i hi=>trace.amplifierError_nonneg i (Finset.mem_range.mp hi).le)))
      (trace.amplifierError_nonneg n le_rfl)
  · exact hmAmp
  · dsimp only [m,nodes,q,D,fees]
    rw [Finset.prod_range_succ']
    simp only [prependArray]
    rw [trace.weight]
    ring
  · dsimp only [nodes]
    rw [Finset.sum_range_succ']
    simp only [prependArray]
    have hm:=trace.missing
    simp only [one_mul] at hm
    rw [hm]
    ring
  · exact herror
  · rw [hVm,hRedm,hDm,hPm,←rootPaid_identity]
    exact hcert.le

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.root_paidAt4_prefix

#print axioms OAI.SevenEighths.Cycle153Reachable.root_trace_class_payment
