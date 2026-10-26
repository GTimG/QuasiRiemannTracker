/- Actual scheduled errors in the finite source path. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.RootReturnedPayment

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153JointCount CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentCanonicalFirst CenteredMomentFirstScale CenteredMomentSectorLocalization Cycle63HighGeometry

private theorem density_fee_bounds {delta : ℝ} (hlo : 3/5≤delta) (hhi : delta≤3/4) :
    0≤LocalMoment.unmarkedDensity delta ∧ LocalMoment.unmarkedDensity delta≤1 ∧
    0≤Cycle153.commonLoss delta ∧ Cycle153.commonLoss delta≤1 := by
  have hd : 0<3*(5-2*delta) := by linarith only [hhi]
  have hquot : (1/2:ℝ)≤10*delta/(3*(5-2*delta)) := by
    apply (le_div_iff₀ hd).mpr
    linarith only [hlo]
  have hrlo:=LocalMoment.unmarkedDensity_ge_two_sevenths hhi
  have hrhi : LocalMoment.unmarkedDensity delta≤1/2 := by
    dsimp only [LocalMoment.unmarkedDensity]
    linarith only [hquot]
  have hr : 0≤LocalMoment.unmarkedDensity delta := by linarith only [hrlo]
  have hcommon : Cycle153.commonLoss delta=
      max (3/19) (4*LocalMoment.unmarkedDensity delta-5/4) := rfl
  refine ⟨hr,by linarith only [hrhi],?_,?_⟩
  · rw [hcommon]
    exact le_trans (by norm_num) (le_max_left _ _)
  · rw [hcommon]
    exact max_le (by norm_num) (by linarith only [hrhi])

theorem NativePaidPathNode.fine_small {Z : ℝ} (node : NativePaidPathNode Z)
    (source : node.SourceGates) (fine : node.FineSourceGates)
    {delta : ℝ} (hlo : 3/5≤delta) (hhi : delta≤3/4) :
    node.small delta≤1/1000000000000 := by
  obtain ⟨hr,hr1,_,_⟩:=density_fee_bounds hlo hhi
  have h1 := mul_le_mul_of_nonneg_left fine.loss_le (sub_nonneg.mpr hr1)
  have h2 := mul_le_mul_of_nonneg_left fine.eps_le hr
  have hsum : node.sideError+(1-LocalMoment.unmarkedDensity delta)*
      (frequencyLoss (Z^node.unit) 32 node.xi+node.reserve)+
      LocalMoment.unmarkedDensity delta*node.eps≤3/1000000000000000 := by
    nlinarith only [h1,h2,fine.side_le,hr,hr1]
  have hm:=mul_le_mul_of_nonneg_left hsum node.unit_pos.le
  change node.unit*(node.sideError+(1-LocalMoment.unmarkedDensity delta)*
    (frequencyLoss (Z^node.unit) 32 node.xi+node.reserve)+
      LocalMoment.unmarkedDensity delta*node.eps)≤1/1000000000000
  nlinarith only [hm,source.unit_le_one]

variable {α : Type} [Fintype α]
  {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {hH : RayOrthogonality.globalUnits M≤H}
  {C : SourceContext (α:=α) M H}

/-- All final path errors are paid from retained actual schedule
receipts. The terminal loss is the SAME record's actual loss after
operator shifts and exact rebase. No weighted class bound is assumed. -/
theorem root_trace_fine_error
    (N : ReachableNode C (0:Fin 4))
    (F : SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz N.presentation.mult)
    (d : SuffixDepth 4) (p : F.Prefix d)
    (trace : ActualPathTrace hH N 1 F d p)
    (edge : RootTraceEdge (C:=C) trace.coordinates
      (trace.scale 0) (trace.volumeLength 0) (trace.prefixLog 0))
    (delta : ℝ) (hlo : 3/5≤delta) (hhi : delta≤3/4)
    (hloss : (F.part d p).loss≤6/1000000000000) :
    (F.part d p).loss+5*(edge.amplifierError+
      (∑i∈Finset.range trace.count,trace.amplifierError i)+trace.amplifierError trace.count)+
      (∑i∈Finset.range (trace.count+1),
        ((prependArray edge.node trace.node i).small delta+
        prependArray edge.fee.amount (fun i=>(trace.fee i).amount) i+
        LocalMoment.unmarkedDensity delta*prependArray edge.scalePad trace.scalePad i+
        Cycle153.commonLoss delta*prependArray edge.capacityPad trace.capacityPad i))≤
      1/10000000000 := by
  have hn : trace.count≤3 := by
    have hn:=suffixOffset_lt 4 d
    have hc : trace.count=suffixOffset 4 d:=trace.count_eq
    omega
  have hnR : (trace.count:ℝ)≤3 := by exact_mod_cast hn
  obtain ⟨hr,hr1,hc,hc1⟩:=density_fee_bounds hlo hhi
  have hsumamp : (∑i∈Finset.range trace.count,trace.amplifierError i)≤
      (trace.count:ℝ)/1000000000000 := by
    calc
      _ ≤∑i∈Finset.range trace.count,(1/1000000000000:ℝ) :=
        Finset.sum_le_sum (fun i hi=>trace.fineAmplifierError i (Finset.mem_range.mp hi).le)
      _ =_ := by simp <;>ring
  have hpads (s t : ℝ) (hs : s≤1/1000000000000) (ht : t≤1/1000000000000) :
      LocalMoment.unmarkedDensity delta*s+Cycle153.commonLoss delta*t≤2/1000000000000 := by
    have h1:=mul_le_mul_of_nonneg_left hs hr
    have h2:=mul_le_mul_of_nonneg_left ht hc
    nlinarith only [h1,h2,hr1,hc1]
  have hstep (i : ℕ) (hi : i<trace.count+1) :
      (prependArray edge.node trace.node i).small delta+
        prependArray edge.fee.amount (fun i=>(trace.fee i).amount) i+
        LocalMoment.unmarkedDensity delta*prependArray edge.scalePad trace.scalePad i+
        Cycle153.commonLoss delta*prependArray edge.capacityPad trace.capacityPad i≤
          4/1000000000000 := by
    cases i with
    | zero =>
      have hsmall:=NativePaidPathNode.fine_small edge.node edge.sourceGates edge.fineSource hlo hhi
      have hpad:=hpads edge.scalePad edge.capacityPad edge.fineScalePad edge.fineCapacityPad
      simp only [prependArray]
      linarith only [hsmall,hpad,edge.fineFee]
    | succ i =>
      have hi' : i<trace.count := by omega
      have hsmall:=NativePaidPathNode.fine_small (trace.node i) (trace.sourceGates i hi')
        (trace.fineSource i hi') hlo hhi
      have hpad:=hpads (trace.scalePad i) (trace.capacityPad i)
        (trace.fineScalePad i hi') (trace.fineCapacityPad i hi')
      simp only [prependArray]
      linarith only [hsmall,hpad,trace.fineFee i hi']
  have hsumstep : (∑i∈Finset.range (trace.count+1),
      ((prependArray edge.node trace.node i).small delta+
        prependArray edge.fee.amount (fun i=>(trace.fee i).amount) i+
        LocalMoment.unmarkedDensity delta*prependArray edge.scalePad trace.scalePad i+
        Cycle153.commonLoss delta*prependArray edge.capacityPad trace.capacityPad i))≤
          ((trace.count:ℝ)+1)*(4/1000000000000) := by
    calc
      _ ≤∑i∈Finset.range (trace.count+1),(4/1000000000000:ℝ) :=
        Finset.sum_le_sum (fun i hi=>hstep i (Finset.mem_range.mp hi))
      _ =_ := by simp <;>ring
  linarith only [hloss,edge.fineAmplifierError,hsumamp,
    trace.fineAmplifierError trace.count le_rfl,hsumstep,hnR]


/-- The actual class payment with its finite error discharged by the
retained native schedule. The corrected scalar certificate is obtained
from the SAME actual physical prefix by root_trace_class_payment. -/
theorem root_trace_class_payment_scheduled
    (N : ReachableNode C (0:Fin 4))
    (F : SuffixFamily (hH:=hH) 0 4 C.etaSeed C.globalBase C.Bnorm C.Tz N.presentation.mult)
    (d : SuffixDepth 4) (p : F.Prefix d)
    (trace : ActualPathTrace hH N 1 F d p)
    (edge : RootTraceEdge (C:=C) trace.coordinates
      (trace.scale 0) (trace.volumeLength 0) (trace.prefixLog 0))
    (b : Bool) (c : ((F.part d p).record b).Class)
    (hV : -(1/1000000000000:ℝ)≤rootHistoricalV ⟨trace.count,by
      have hc : trace.count=suffixOffset 4 d:=trace.count_eq
      rw [hc];exact suffixOffset_lt 4 d⟩ trace.coordinates)
    (hRed : -(1/1000000000000:ℝ)≤rootHistoricalRed ⟨trace.count,by
      have hc : trace.count=suffixOffset 4 d:=trace.count_eq
      rw [hc];exact suffixOffset_lt 4 d⟩ trace.coordinates)
    (hloss : (F.part d p).loss≤6/1000000000000) :
    (C.globalBase^(edge.node.scale+edge.node.shiftedOutside+
      edge.fee.junction*edge.fee.modelDeletion+edge.fee.amount)*F.weight d p)*
      C.globalBase^(((F.part d p).record b).exponent c+((F.part d p).record b).missExp c+
        LocalMoment.unmarkedDensity (2*((F.part d p).record b).zeroBin c-1)*((F.part d p).record b).rowExp c+
        (edge.node.coordinate 1+F.historyMissing d p))≤
      C.globalBase^((1:ℝ)-1/10000000+1/10000000000) := by
  apply root_trace_class_payment N F d p trace edge b c (1/10000000000) hV hRed
  have hb:=((F.part d p).pays b) c
  let k : Fin 4:=⟨trace.count,by
    have hc : trace.count=suffixOffset 4 d:=trace.count_eq
    rw [hc];exact suffixOffset_lt 4 d⟩
  have hk : (⟨suffixOffset 4 d,suffixOffset_lt 4 d⟩:Fin 4)=k := by
    apply Fin.ext
    exact trace.count_eq.symm
  have hq : suffixJunction 0 4 d=rootTerminalQ k := by rw [suffixJunction_four,hk]
  have hlow : 3/5≤2*((F.part d p).record b).zeroBin c-1 := by
    have hj:=rootTerminalQ_floor k
    have hbin:=hb.1
    linarith only [hj,hbin,hq]
  exact root_trace_fine_error N F d p trace edge _ hlow hb.2.1 hloss

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.root_trace_fine_error
#print axioms OAI.SevenEighths.Cycle153Reachable.root_trace_class_payment_scheduled
