/- Prepend an actual parent source key to the literal history of a strictly
 deeper daughter. This matches NativeForestAttach's dependent sum. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.DecoratedHistory
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open HeckeFamily Cycle63Moment

/-- Source trees attach their immediate row before the daughter's history;
the counting history uses the same chronological keys, associated left. -/
def prependHistory : (n : ℕ)→DecoratedPrefix→History n→History (n+1)
  | 0, d, _ => ((),d)
  | n+1, d, p => (prependHistory n d p.1,p.2)

theorem prependHistory_pair_injective : ∀n,
    Function.Injective (fun x : DecoratedPrefix×History n=>prependHistory n x.1 x.2) := by
  intro n
  induction n with
  | zero =>
    rintro ⟨d,⟨⟩⟩ ⟨d',⟨⟩⟩ h
    exact Prod.ext (congrArg Prod.snd h) rfl
  | succ n ih =>
    rintro ⟨d,p⟩ ⟨d',p'⟩ h
    have hp := @ih (d,p.1) (d',p'.1) (congrArg Prod.fst h)
    have hd : d=d' := congrArg (fun x : DecoratedPrefix×History n=>x.1) hp
    have hprev : p.1=p'.1 := congrArg (fun x : DecoratedPrefix×History n=>x.2) hp
    have hlast : p.2=p'.2 := congrArg (fun x : History (n+2)=>x.2) h
    exact Prod.ext hd (Prod.ext hprev hlast)

/-- The missing radical of the immediate actual source is inserted once;
the daughter's complete history is retained. -/
theorem historyMissing_prepend (lefts : ℕ→Bool) (Z : ℝ) (d : DecoratedPrefix) :
    ∀n (p : History n),
    historyMissing lefts Z (n+1) (prependHistory n d p)=
      stepMissing (lefts 0) Z d.1+historyMissing (fun k=>lefts (k+1)) Z n p := by
  intro n
  induction n with
  | zero => intro p;simp only [prependHistory,historyMissing,zero_add,add_zero]
  | succ n ih =>
    intro p
    change historyMissing lefts Z (n+1) (prependHistory n d p.1)+
        stepMissing (lefts (n+1)) Z p.2.1=
      stepMissing (lefts 0) Z d.1+
        (historyMissing (fun k=>lefts (k+1)) Z n p.1+stepMissing (lefts (n+1)) Z p.2.1)
    rw [ih]
    exact add_assoc _ _ _

/-- Actual global multipliers agree after attachment. The daughter's
units are the restrictions of the same full-prefix unit function. -/
theorem historyMultiplier_prepend
    (units : ∀k,History k→FirstSourceLabel→HeckeFamily.O)
    (lefts : ℕ→Bool) (root : HeckeFamily.O) (d : DecoratedPrefix) :
    ∀n (p : History n),
    historyMultiplier units lefts root (n+1) (prependHistory n d p)=
      historyMultiplier (fun k p=>units (k+1) (prependHistory k d p))
        (fun k=>lefts (k+1))
        (childMultiplier (lefts 0) root (units 0 ()) d.1) n p := by
  intro n
  induction n with
  | zero => intro p;rfl
  | succ n ih =>
    intro p
    change childMultiplier (lefts (n+1))
      (historyMultiplier units lefts root (n+1) (prependHistory n d p.1))
      (units (n+1) (prependHistory n d p.1)) p.2.1=
      childMultiplier (lefts (n+1))
      (historyMultiplier (fun k p=>units (k+1) (prependHistory k d p))
        (fun k=>lefts (k+1)) (childMultiplier (lefts 0) root (units 0 ()) d.1) n p.1)
      (units (n+1) (prependHistory n d p.1)) p.2.1
    rw [ih]
end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.prependHistory_pair_injective
#print axioms OAI.SevenEighths.Cycle153JointCount.historyMultiplier_prepend
