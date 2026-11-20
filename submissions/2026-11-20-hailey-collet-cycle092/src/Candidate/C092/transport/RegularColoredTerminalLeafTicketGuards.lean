/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The actual ticket's zero bands and ceiling restrict to its exact finite key.
-/
import Candidate.C092.transport.RegularColoredTerminalLeafGuards
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open QRH.Cycle092.TerminalActualRow

/-- No band guard is assumed anew on a class: it is read from the actual
original row ticket, retaining its family and its original measured ceiling. -/
theorem terminal_actual_ticket_class_guards {Label : Type} [Fintype Label] [DecidableEq Label]
    {I Je Jν : ℕ} (rows : Finset FreeRow) (χ : FreeRow  →  Label  →  Character)
    (hn : ∀u : rows,∀j,(χ u.val j).residue≠1)
    (U d dmax tau epsilon ez price : ℝ) (response : FreeRow  →  ℝ)
    (ticket : ∀u : rows,RowTicket (χ u.val) (hn u) U d dmax tau epsilon ez price (response u.val) I)
    (window : rows  →  Fin Je×Fin Jν) (cutoff : Fin Je×Fin Jν  →  ℝ)
    (ws : ∀u : rows,SupportedWitness (χ u.val) (U^d) ((51/100:ℝ)+ez*(ticket u).level.val) epsilon
      (cutoff (window u)) (U^tau) ((U^d)^(tau/(2*dmax))) (ticket u).band.val)
    (tag : Fin (I+1)×Fin (⌊(73/200:ℝ)/ez⌋₊+1)×(Fin Je×Fin Jν)×Label×Fin (dyadicLength (U^d))×Fin (dyadicLength (U^d))) :
    let key := terminalWitnessKey (fun u=>(ticket u).band) (fun u=>(ticket u).level) window cutoff ws;
    ∀u : classRows rows key tag,
    let parent : rows := ⟨u.val,classRows_subset rows key tag u.property⟩;
      1 ≤ tag.1.val ∧ (51/100:ℝ) < (51/100:ℝ)+ez*tag.2.1.val ∧
      (51/100:ℝ)+ez*tag.2.1.val ≤ 7/8 ∧
      zeroMaximum (χ u.val) (hn parent) (3*(tag.1.val+1:ℕ)*U^tau) < (51/100:ℝ)+ez*tag.2.1.val+2*ez ∧
      (51/100:ℝ)+ez*tag.2.1.val ≤ zeroMaximum (χ u.val) (hn parent) ((3*tag.1.val:ℕ)*U^tau) ∧
      response u.val ≤ (2*((51/100:ℝ)+ez*tag.2.1.val)-1)+price := by
  intro key u parent
  have hf := terminal_key_fields rows χ U d dmax tau epsilon ez
    (fun u=>(ticket u).band) (fun u=>(ticket u).level) window cutoff ws tag u
  change (ticket parent).band=tag.1 ∧ (ticket parent).level=tag.2.1 ∧ _ at hf
  have hb := congrArg Fin.val hf.1
  have hl := congrArg Fin.val hf.2.1
  have hpos := (ticket parent).band_pos
  have hlo := (ticket parent).lower
  have hup := (ticket parent).upper
  have hnext := (ticket parent).next
  have hcurrent := (ticket parent).current
  have hceil := (ticket parent).ceiling
  rw [hb] at hpos hnext hcurrent
  rw [hl] at hlo hup hnext hcurrent hceil
  exact ⟨hpos,hlo,hup,hnext,hcurrent,hceil⟩

#print axioms terminal_actual_ticket_class_guards
end
end QRH.Cycle092.RegularColoredForward
