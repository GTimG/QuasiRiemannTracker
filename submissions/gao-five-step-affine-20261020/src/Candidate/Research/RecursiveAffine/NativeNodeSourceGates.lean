/- Actual regional cell gates for the canonical LOW source. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeNodeStep
import Candidate.Research.RecursiveAffine.SourceContextMesh

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63.Optimization Cycle153 Cycle153SourceSchedule
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

/-- The actual source amplifier pays its ledger reserve, and the SAME
detector's deletion is nonnegative at every reachable rounded cell.
These are source gates, independent of every energy or future output. -/
theorem actual_node_canonical_scalar_gates (N : ReachableNode C j) :
    letI : Cycle63.AffineLedger:=N.ledger
    Cycle63.AffineLedger.lowReserve≤nodeSourceAmp N ∧
      0≤nodeSourceAmp N ∧ 0≤nodeDetectorDeletion N :=by
  letI : Cycle63.AffineLedger:=N.ledger
  let cell:=Cycle63.AffineLedger.cellUpper
    (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit))
  have hcell:=Cycle63.AffineLedger.cellUpper_bounds
    ((Cycle63.AffineLedger.originalCell_mem ⟨N.window.slots_ge,N.window.slots_le⟩).1)
    ((Cycle63.AffineLedger.originalCell_mem ⟨N.window.slots_ge,N.window.slots_le⟩).2.1)
  have hbounds:=Cycle63.AffineLedger.amp_bounds hcell
  have ha0:=(Cycle63.AffineLedger.amp_pos hcell).le
  have ha : Cycle63.AffineLedger.lowReserve≤Cycle63.AffineLedger.amp cell:=by
    have hr:=native_reserve_lt_half_amplifier
    linarith only [hr,hbounds.1,ha0]
  have hsame : nodeRoundedDeletion N=
      (Cycle63.AffineLedger.regionGap cell+6*Cycle63.AffineLedger.intercept*
        Cycle63.AffineLedger.amp cell)/(6*Cycle63.AffineLedger.price):=by
    dsimp only [cell]
    rw [regional_actual_cell N.positionFacts ⟨N.window.slots_ge,N.window.slots_le⟩]
    rfl
  have hpaid : Cycle63.AffineLedger.q*nodeRoundedDeletion N=
      Cycle63.AffineLedger.amp cell-Cycle63.AffineLedger.lowReserve:=by
    rw [hsame,←Cycle63.AffineLedger.low_reserve cell]
    unfold Cycle63.AffineLedger.lowRate
    field_simp [Cycle63.AffineLedger.price_pos.ne']
    <;> ring
  have hd : 0≤nodeRoundedDeletion N:=by
    have hq:=Cycle63.AffineLedger.q_pos
    by_contra hn
    have hn':nodeRoundedDeletion N<0:=lt_of_not_ge hn
    have hh:=mul_neg_of_pos_of_neg hq hn'
    linarith only [hh,hpaid,ha]
  refine ⟨?_,?_,?_⟩
  · rw [←nodeSourceAmp_eq_native N]
    exact ha
  · rw [←nodeSourceAmp_eq_native N]
    exact ha0
  · dsimp only [nodeDetectorDeletion]
    linarith only [hd]

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_node_canonical_scalar_gates
