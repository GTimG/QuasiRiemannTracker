/- Literal sparse forest at the actual own-HIGH source. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.TerminalSourceReceipt

set_option autoImplicit false
set_option maxHeartbeats 650000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle153JointCount Cycle153SourceReturn

variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
  {hH : RayOrthogonality.globalUnits M≤H}

private def ownSuffixHistory {start : ℕ} (count : ℕ) (hcount : 0<count)
    {eta : Character} {Z B T : ℝ} {root : O}
    (part : ReturnedPartAt M H hH (innerStage start).q
      (prefixDictionary (start+1)) eta Z B T root) :
    (d : SuffixDepth count)→(ownSuffixFamily count hcount part).Prefix d→
      History (suffixOffset count d) :=
  match count,hcount with
  | 0,h => False.elim (Nat.not_lt_zero _ h)
  | n+1,_ => fun d p=>match d with
    | none => ()
    | some _ => nomatch p.1

private theorem ownSuffix_properties {start : ℕ} (count : ℕ) (hcount : 0<count)
    {eta : Character} {Z B T : ℝ} {root : O}
    (part : ReturnedPartAt M H hH (innerStage start).q
      (prefixDictionary (start+1)) eta Z B T root) :
    ∀d (p : (ownSuffixFamily count hcount part).Prefix d),
      suffixOffset count d=0 ∧
      (ownSuffixFamily count hcount part).multiplier d p=root ∧
      (ownSuffixFamily count hcount part).weight d p=1 ∧
      (ownSuffixFamily count hcount part).historyMissing d p=0 ∧
      ((ownSuffixFamily count hcount part).part d p).scale=part.scale ∧
      ((ownSuffixFamily count hcount part).part d p).length=part.length ∧
      ((ownSuffixFamily count hcount part).part d p).amp=part.amp ∧
      ((ownSuffixFamily count hcount part).part d p).loss=part.loss := by
  cases count with
  | zero => exact False.elim (Nat.not_lt_zero _ hcount)
  | succ n =>
    intro d p
    cases d with
    | none => exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    | some d => exact nomatch p.1

variable {α : Type} [Fintype α] [DecidableEq α]
  {C : SourceContext (α:=α) M H} {j : Fin 4}

/-- The native own-HIGH family has exactly its empty continuing history.
All deeper carriers are literally empty; no fibre or density assertion is
needed to make its chronology. -/
def ownHighChronology (N : ReachableNode C j)
    (part : ReturnedPartAt M H hH (innerStage j.val).q
      (prefixDictionary (j.val+1)) C.etaSeed N.localBase C.Bnorm C.Tz N.presentation.mult)
    (Bsrc : ℝ) (boxes : ℕ→Finset (Fin 4→ℤ)) :
    ForestChronology hH N (ownSuffixFamily (4-j.val) (by omega) part) Bsrc boxes where
  word := fun _ _ _=>false
  word_padding := by intro d p k hk;rfl
  units := fun _ _ _ _=>1
  code := ownSuffixHistory _ _ part
  injective := by
    intro d p p' heq
    fin_cases j <;> cases d with
    | none =>
      change @Eq Unit p p'
      exact @Subsingleton.elim Unit inferInstance p p'
    | some d => exact nomatch p.1
  multiplier := by
    intro d p
    fin_cases j <;> cases d with
    | none => rfl
    | some d => exact nomatch p.1
  missing := by
    intro d p
    fin_cases j <;> cases d with
    | none => rfl
    | some d => exact nomatch p.1
  facts := by
    intro d p
    fin_cases j <;> cases d with
    | none => trivial
    | some d => exact nomatch p.1

/-- The empty-history path is attached to the SAME actual native own
record. The amplifier discrepancy is the actual rounded-source error. -/
def ownHighForest_paths (N : ReachableNode C j)
    (part : ReturnedPartAt M H hH (innerStage j.val).q
      (prefixDictionary (j.val+1)) C.etaSeed N.localBase C.Bnorm C.Tz N.presentation.mult)
    (hm : part.scale=N.state.rowWidth)
    (hA : part.length=Real.logb N.localBase (CenteredMomentAmplificationChildInput.volume (N.input hH)))
    (ampError : ℝ) (hampError : 0≤ampError) (hfineAmp : ampError≤1/1000000000000)
    (hamp : N.unit*part.amp≤
      ![Cycle153Geometry.Coordinates.a1 N.coordinates,Cycle153Geometry.Coordinates.a2 N.coordinates,
        Cycle153Geometry.Coordinates.a3 N.coordinates,Cycle153Geometry.Coordinates.a4 N.coordinates] j+ampError) :
    let F : N.Family hH:=ownSuffixFamily (4-j.val) (by omega) part
    ∀d p,ActualPathTrace hH N N.unit F d p := by
  intro F d p
  have hp:=ownSuffix_properties (4-j.val) (by omega) part d p
  apply ActualPathTrace.terminal N hp.1 (hp.2.2.2.2.1.trans hm)
    (hp.2.2.2.2.2.1.trans hA) hp.2.1 hp.2.2.1 hp.2.2.2.1
    ampError hampError hfineAmp
  change N.unit*((ownSuffixFamily (4-j.val) (by omega) part).part d p).amp≤_
  rw [hp.2.2.2.2.2.2.1]
  exact hamp

/-- Bind the actual own-HIGH physical equalities to every (necessarily
own) part of the sparse family, retaining the exact terminal loss and
class cap. These are source outputs for the backward stage assembly. -/
theorem ownHighForest_source_receipts (N : ReachableNode C j)
    (part : ReturnedPartAt M H hH (innerStage j.val).q
      (prefixDictionary (j.val+1)) C.etaSeed N.localBase C.Bnorm C.Tz N.presentation.mult)
    (hm : part.scale=N.state.rowWidth)
    (hA : part.length=Real.logb N.localBase (CenteredMomentAmplificationChildInput.volume (N.input hH)))
    (ha : letI : Cycle63.AffineLedger:=N.ledger
      part.amp=Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit))))
    (hloss : part.loss≤terminalLossCap j)
    (hclass : ∀b,(Fintype.card (part.record b).Class:ℝ)≤C.highClassCap) :
    let F : N.Family hH:=ownSuffixFamily (4-j.val) (by omega) part
    (∀d p,TerminalSourceCaps (F.part d p).scale (F.part d p).length (F.part d p).amp
      (Real.logb N.localBase ((Ideal.span {F.multiplier d p}).absNorm:ℝ))) ∧
    (∀d p,(F.part d p).loss≤terminalLossCap j) ∧
    (∀d p b,(Fintype.card ((F.part d p).record b).Class:ℝ)≤C.highClassCap) := by
  let F : N.Family hH:=ownSuffixFamily (4-j.val) (by omega) part
  have hcaps:=actual_own_terminal_source_caps N part hm hA ha
  refine ⟨?_,?_,?_⟩
  · intro d p
    have hp:=ownSuffix_properties (4-j.val) (by omega) part d p
    simpa only [F,hp.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2.1,hp.2.2.2.2.2.2.1] using hcaps
  · intro d p
    have hp:=ownSuffix_properties (4-j.val) (by omega) part d p
    simpa only [F,hp.2.2.2.2.2.2.2] using hloss
  · intro d p b
    fin_cases j <;> cases d with
    | none => exact hclass b
    | some d => exact nomatch p.1

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.ownHighChronology
#print axioms OAI.SevenEighths.Cycle153Reachable.ownHighForest_source_receipts
#print axioms OAI.SevenEighths.Cycle153Reachable.ownHighForest_paths
