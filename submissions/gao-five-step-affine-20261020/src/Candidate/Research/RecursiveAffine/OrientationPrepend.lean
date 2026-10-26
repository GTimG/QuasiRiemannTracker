/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ReachableNode
import Candidate.Research.RecursiveAffine.HistoryPrepend

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical HeckeNotation
open HeckeFamily Cycle63Moment Cycle153JointCount

/-- Prepend the actual current reflection and retain the three possible
future choices. Unused positions are supplied by the source padding. -/
def prependOrientation (left : Bool) (word : OrientationWord) : OrientationWord :=
  ![left,word 0,word 1,word 2]

def tailOrientation (word : OrientationWord) : OrientationWord :=
  ![word 1,word 2,word 3,false]

theorem tail_prepend_orientation (left : Bool) (word : OrientationWord)
    (hpad : word 3=false) : tailOrientation (prependOrientation left word)=word := by
  funext i
  fin_cases i <;> simp [tailOrientation,prependOrientation,hpad]

theorem prepend_orientation_injective (left : Bool) (word word' : OrientationWord)
    (hpad : word 3=false) (hpad' : word' 3=false)
    (h : prependOrientation left word=prependOrientation left word') : word=word' := by
  have ht := congrArg tailOrientation h
  simpa only [tail_prepend_orientation left word hpad,tail_prepend_orientation left word' hpad'] using ht

theorem prepend_orientation_padding (left : Bool) (word : OrientationWord) (n : ℕ)
    (hpad : ∀i : Fin 4,n≤ i.val → word i=false) :
    ∀i : Fin 4,n+1≤ i.val → prependOrientation left word i=false := by
  intro i hi
  fin_cases i
  · change n+1≤0 at hi
    omega
  · exact hpad 0 (by change n+1≤1 at hi;change n≤0;omega)
  · exact hpad 1 (by change n+1≤2 at hi;change n≤1;omega)
  · exact hpad 2 (by change n+1≤3 at hi;change n≤2;omega)

@[simp] theorem wordLeft_prepend_zero (left : Bool) (word : OrientationWord) :
    wordLeft (prependOrientation left word) 0=left := rfl

theorem wordLeft_prepend_shift (left : Bool) (word : OrientationWord) (k : ℕ) (hk : k<3) :
    wordLeft (prependOrientation left word) (k+1)=wordLeft word k := by
  interval_cases k <;> rfl

theorem wordLeft_tail_prefix (word : OrientationWord) (k : ℕ) (hk : k<3) :
    wordLeft (tailOrientation word) k=wordLeft word (k+1) := by
  interval_cases k <;> rfl

/-- Only actual earlier reflection bits enter the multiplier of a finite
history. A periodic extension beyond that history has no effect. -/
theorem historyMultiplier_left_prefix
    (units : ∀k,History k→FirstSourceLabel→O) (left right : ℕ→Bool) (root : O) :
    ∀n,(∀k,k<n → left k=right k) →
      ∀p : History n,historyMultiplier units left root n p=historyMultiplier units right root n p := by
  intro n
  induction n with
  | zero => intro _ p;rfl
  | succ n ih =>
    intro h p
    have hp : historyMultiplier units left root n=historyMultiplier units right root n := by
      funext q
      exact ih (fun k hk=>h k (by omega)) q
    simp only [historyMultiplier,hp,h n (by omega)]

theorem historyMissing_left_prefix (left right : ℕ→Bool) (Z : ℝ) :
    ∀n,(∀k,k<n → left k=right k) →
      ∀p : History n,historyMissing left Z n p=historyMissing right Z n p := by
  intro n
  induction n with
  | zero => intro _ p;rfl
  | succ n ih =>
    intro h p
    simp only [historyMissing,ih (fun k hk=>h k (by omega)),h n (by omega)]

theorem historyFacts_left_prefix
    (units : ∀k,History k→FirstSourceLabel→O) (left right : ℕ→Bool)
    (root : O) (Z B : ℝ) (boxes : ℕ→Finset (Fin 4→ℤ)) :
    ∀n,(∀k,k<n → left k=right k) → ∀p : History n,
      HistoryFacts units left root Z B boxes n p ↔ HistoryFacts units right root Z B boxes n p := by
  intro n
  induction n with
  | zero => intro _ p;rfl
  | succ n ih =>
    intro h p
    have hp : historyMultiplier units left root n=historyMultiplier units right root n := by
      funext q
      exact historyMultiplier_left_prefix units left right root n (fun k hk=>h k (by omega)) q
    simp only [HistoryFacts,ih (fun k hk=>h k (by omega)),hp,h n (by omega)]

/-- A zero-filled tail agrees with the shifted parent word throughout
every possible actual child history. There is no assertion at later bits. -/
theorem historyMultiplier_tail_orientation
    (units : ∀k,History k→FirstSourceLabel→O) (word : OrientationWord)
    (root : O) (n : ℕ) (hn : n≤3) (p : History n) :
    historyMultiplier units (wordLeft (tailOrientation word)) root n p=
      historyMultiplier units (fun k=>wordLeft word (k+1)) root n p :=
  historyMultiplier_left_prefix units _ _ root n
    (fun k hk=>wordLeft_tail_prefix word k (by omega)) p

theorem historyMissing_tail_orientation (word : OrientationWord) (Z : ℝ)
    (n : ℕ) (hn : n≤3) (p : History n) :
    historyMissing (wordLeft (tailOrientation word)) Z n p=
      historyMissing (fun k=>wordLeft word (k+1)) Z n p :=
  historyMissing_left_prefix _ _ Z n
    (fun k hk=>wordLeft_tail_prefix word k (by omega)) p

theorem historyFacts_tail_orientation
    (units : ∀k,History k→FirstSourceLabel→O) (word : OrientationWord)
    (root : O) (Z B : ℝ) (boxes : ℕ→Finset (Fin 4→ℤ))
    (n : ℕ) (hn : n≤3) (p : History n) :
    HistoryFacts units (wordLeft (tailOrientation word)) root Z B boxes n p ↔
      HistoryFacts units (fun k=>wordLeft word (k+1)) root Z B boxes n p :=
  historyFacts_left_prefix units _ _ root Z B boxes n
    (fun k hk=>wordLeft_tail_prefix word k (by omega)) p

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.historyFacts_tail_orientation
#print axioms OAI.SevenEighths.Cycle153Reachable.historyMultiplier_tail_orientation
