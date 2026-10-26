/- The actual bare-root scalar source gates, without a fictitious node.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootStep
import Candidate.Research.RecursiveAffine.SourceContextMesh

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle153RootStep
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Cycle153SourceSchedule
noncomputable local instance rootSourceGatesLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]

/-- Actual original weights choose the root cell. The native reserve
identity proves both source and detector deletions nonnegative and pays
the unchanged source deletion exactly. No energy or child is assumed. -/
theorem actual_root_canonical_scalar_gates (w : alpha→ℝ)
    (hslots : Cycle63.AffineLedger.slotFloor≤∑i,w i ∧
      (∑i,w i)≤Cycle63.AffineLedger.slotTop) :
    Cycle63.AffineLedger.lowReserve≤rootSourceAmp w ∧
      0≤rootSourceAmp w ∧ 0≤rootSourceDeletion w ∧ 0≤rootDetectorDeletion w ∧
      Cycle63.AffineLedger.q*rootSourceDeletion w=
        rootSourceAmp w-Cycle63.AffineLedger.lowReserve :=by
  have hcell:=Cycle63.AffineLedger.cellUpper_bounds
    ((Cycle63.AffineLedger.originalCell_mem hslots).1)
    ((Cycle63.AffineLedger.originalCell_mem hslots).2.1)
  have hbounds:=(Cycle63.AffineLedger.amp_bounds hcell).1
  have ha0 : 0≤rootSourceAmp w:=(Cycle63.AffineLedger.amp_pos hcell).le
  have ha : Cycle63.AffineLedger.lowReserve≤rootSourceAmp w:=by
    have hr:=native_reserve_lt_half_amplifier
    change Cycle63.AffineLedger.amplifierFloor≤rootSourceAmp w at hbounds
    linarith only [hr,hbounds,ha0]
  have hpaid : Cycle63.AffineLedger.q*rootSourceDeletion w=
      rootSourceAmp w-Cycle63.AffineLedger.lowReserve:=by
    change Cycle63.AffineLedger.q*((Cycle63.AffineLedger.regionGap (rootSourceCell w)+
      6*Cycle63.AffineLedger.intercept*Cycle63.AffineLedger.amp (rootSourceCell w))/
      (6*Cycle63.AffineLedger.price))=Cycle63.AffineLedger.amp (rootSourceCell w)-_
    rw [←Cycle63.AffineLedger.low_reserve (rootSourceCell w)]
    unfold Cycle63.AffineLedger.lowRate
    field_simp [Cycle63.AffineLedger.price_pos.ne']
    <;> ring
  have hd : 0≤rootSourceDeletion w:=by
    by_contra hn
    have hh:=mul_neg_of_pos_of_neg Cycle63.AffineLedger.q_pos (lt_of_not_ge hn)
    linarith only [hh,hpaid,ha]
  refine ⟨ha,ha0,hd,?_,hpaid⟩
  dsimp only [rootDetectorDeletion]
  linarith only [hd]

end
end OAI.SevenEighths.Cycle153RootStep
#print axioms OAI.SevenEighths.Cycle153RootStep.actual_root_canonical_scalar_gates
