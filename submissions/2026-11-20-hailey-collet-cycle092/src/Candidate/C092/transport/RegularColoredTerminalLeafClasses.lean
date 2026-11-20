/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Supported witnesses are restricted to genuine original finite ticket classes.
All band/cutoff casts preserve the actual label, zero and integer dyads.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafWindows
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open QRH.Cycle092.TerminalActualRow

/-- Transport proof parameters only; every physical witness datum is retained. -/
def terminalCastWitness {Label : Type} [Fintype Label] {χ : Label→Character}
    {U a a' epsilon cutoff cutoff' T allowance : ℝ} {i i' : ℕ}
    (ha : a=a') (hc : cutoff=cutoff') (hi : i=i')
    (w : SupportedWitness χ U a epsilon cutoff T allowance i) :
    SupportedWitness χ U a' epsilon cutoff' T allowance i' := by
  cases ha;cases hc;cases hi;exact w

theorem terminalCastWitness_fields {Label : Type} [Fintype Label] {χ : Label→Character}
    {U a a' epsilon cutoff cutoff' T allowance : ℝ} {i i' : ℕ}
    (ha : a=a') (hc : cutoff=cutoff') (hi : i=i')
    (w : SupportedWitness χ U a epsilon cutoff T allowance i) :
    (terminalCastWitness ha hc hi w).label=w.label ∧
    (terminalCastWitness ha hc hi w).left=w.left ∧
    (terminalCastWitness ha hc hi w).right=w.right ∧
    (terminalCastWitness ha hc hi w).r=w.r ∧
    (terminalCastWitness ha hc hi w).m=w.m ∧
    (terminalCastWitness ha hc hi w).zero=w.zero := by
  cases ha;cases hc;cases hi;exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Every nonempty or empty genuine class carries fixed band, level,
recorded cutoff, label and both dyads. No new witness is chosen on the class. -/
theorem terminal_witness_class {Label : Type} [Fintype Label] [DecidableEq Label]
    {I K Je Jν : ℕ} (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
    (U d dmax tau epsilon ez : ℝ) (hUd : 1< U^d)
    (level : rows→Fin (I+1)) (band : rows→Fin (K+1)) (window : rows→Fin Je×Fin Jν)
    (cutoff : Fin Je×Fin Jν→ℝ)
    (ws : ∀u : rows,SupportedWitness (χ u.val) (U^d) ((51/100:ℝ)+ez*(band u).val) epsilon
      (cutoff (window u)) (U^tau) ((U^d)^(tau/(2*dmax))) (level u).val)
    (tag : Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×Label×Fin (dyadicLength (U^d))×Fin (dyadicLength (U^d))) :
    let key := terminalWitnessKey level band window cutoff ws
    ∃ wc : ∀u : classRows rows key tag,
      SupportedWitness (χ u.val) (U^d) ((51/100:ℝ)+ez*tag.2.1.val) epsilon
        (cutoff tag.2.2.1) (U^tau) ((U^d)^(tau/(2*dmax))) tag.1.val,
      ∀u,(wc u).label=tag.2.2.2.1 ∧ (wc u).left=tag.2.2.2.2.1 ∧
        (wc u).right=tag.2.2.2.2.2 ∧
        (wc u).r=Real.logb (U^d) ((2:ℝ)^tag.2.2.2.2.1.val) ∧
        (wc u).m=Real.logb (U^d) ((2:ℝ)^tag.2.2.2.2.2.val) := by
  classical
  let key := terminalWitnessKey level band window cutoff ws
  let F := classRows rows key tag
  let parent : F → rows := fun u=>⟨u.val,classRows_subset rows key tag u.property⟩
  have hk (u : F) : key (parent u)=tag := by
    obtain ⟨hu,he⟩ := (classRows_mem rows key tag u.val).mp u.property
    exact he
  have hf (u : F) : level (parent u)=tag.1 ∧ band (parent u)=tag.2.1 ∧
      window (parent u)=tag.2.2.1 ∧ (ws (parent u)).label=tag.2.2.2.1 ∧
      (ws (parent u)).left=tag.2.2.2.2.1 ∧ (ws (parent u)).right=tag.2.2.2.2.2 := by
    have h := hk u
    simpa only [key,terminalWitnessKey,Prod.ext_iff] using h
  let wc := fun u : F=> terminalCastWitness
    (congrArg (fun k : Fin (K+1)=>(51/100:ℝ)+ez*k.val) (hf u).2.1)
    (congrArg cutoff (hf u).2.2.1) (congrArg Fin.val (hf u).1) (ws (parent u))
  refine ⟨wc,?_⟩
  intro u
  have hcast := terminalCastWitness_fields
    (congrArg (fun k : Fin (K+1)=>(51/100:ℝ)+ez*k.val) (hf u).2.1)
    (congrArg cutoff (hf u).2.2.1) (congrArg Fin.val (hf u).1) (ws (parent u))
  have hleft := (hf u).2.2.2.2.1
  have hright := (hf u).2.2.2.2.2
  refine ⟨hcast.1.trans (hf u).2.2.2.1,hcast.2.1.trans hleft,hcast.2.2.1.trans hright,?_,?_⟩
  · exact hcast.2.2.2.1.trans ((ws (parent u)).toWitness.left_exponent hUd |>.trans (by rw [hleft]))
  · exact hcast.2.2.2.2.1.trans ((ws (parent u)).toWitness.right_exponent hUd |>.trans (by rw [hright]))

#print axioms terminalCastWitness_fields
#print axioms terminal_witness_class
end
end QRH.Cycle092.RegularColoredForward
