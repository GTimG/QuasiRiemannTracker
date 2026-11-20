/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal class guards for the same original row tickets and witnesses.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafClasses
set_option autoImplicit false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open QRH.Cycle092.TerminalActualRow

/-- The original ticket key freezes its parameters and physical data. -/
theorem terminal_key_fields {Label : Type} [Fintype Label] [DecidableEq Label]
    {I K Je Jν : ℕ} (rows : Finset FreeRow) (χ : FreeRow → Label → Character)
    (U d dmax tau epsilon ez : ℝ)
    (level : rows → Fin (I+1)) (band : rows → Fin (K+1)) (window : rows → Fin Je×Fin Jν)
    (cutoff : Fin Je×Fin Jν → ℝ)
    (ws : ∀ u : rows,SupportedWitness (χ u.val) (U^d) ((51/100:ℝ)+ez*(band u).val) epsilon
      (cutoff (window u)) (U^tau) ((U^d)^(tau/(2*dmax))) (level u).val)
    (tag : Fin (I+1)×Fin (K+1)×(Fin Je×Fin Jν)×Label×Fin (dyadicLength (U^d))×Fin (dyadicLength (U^d)))
    (u : classRows rows (terminalWitnessKey level band window cutoff ws) tag) :
    let parent : rows := ⟨u.val,classRows_subset rows _ tag u.property⟩
    level parent=tag.1 ∧ band parent=tag.2.1 ∧ window parent=tag.2.2.1 ∧
      (ws parent).label=tag.2.2.2.1 ∧ (ws parent).left=tag.2.2.2.2.1 ∧
      (ws parent).right=tag.2.2.2.2.2 := by
  obtain ⟨hu,he⟩ := (classRows_mem rows _ tag u.val).mp u.property
  simpa only [terminalWitnessKey,Prod.ext_iff] using he

/-- Guards on actual rows restrict to the literal class; its a and window
are the original ones, rather than independently selected substitutes. -/
theorem terminal_class_guards {A B : Type} [Fintype A] [DecidableEq A]
    (rows : Finset FreeRow) (key : rows → A) (tag : A)
    (band : rows → ℝ) (window : rows → B) (a : ℝ) (b : B)
    (hkey : ∀ u : rows,key u=tag → band u=a ∧ window u=b)
    (next response : FreeRow → ℝ) (lower upper : B → ℝ) (price : ℝ)
    (hn : ∀ u : rows,next u.val < band u+price)
    (hr : ∀ u : rows,lower (window u)≤response u.val ∧ response u.val<upper (window u)) :
    ∀ u∈classRows rows key tag,next u<a+price ∧ lower b≤response u ∧ response u<upper b := by
  intro u hu
  obtain ⟨hmem,hclass⟩ := (classRows_mem rows key tag u).mp hu
  have h := hkey ⟨u,hmem⟩ hclass
  have hn' := hn ⟨u,hmem⟩
  have hr' := hr ⟨u,hmem⟩
  simpa only [h.1,h.2] using And.intro hn' hr'

#print axioms terminal_key_fields
#print axioms terminal_class_guards
end
end QRH.Cycle092.RegularColoredForward
