/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite tickets retain the original rows, their actual response and the SAME
attaining zero through all later ordinary/inverse cutoffs. -/
import Candidate.C092.transport.TerminalActualRowPartition
set_option autoImplicit false
namespace QRH.Cycle092.TerminalActualRow
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification HeckeDetectorZeros
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows

/-- A provider ticket contains geometry and the measured ceiling only.
The genuine P4/P6 sources are applied after this data is chosen. -/
structure RowTicket {Label : Type*} [Fintype Label]
    (chi : Label→Character) (hn : ∀j,(chi j).residue≠1)
    (U d dmax tau epsilon ez price response : ℝ) (I : ℕ) where
  band : Fin (I+1)
  band_pos : 1≤ band.val
  level : Fin (⌊(73/200:ℝ)/ez⌋₊+1)
  lower : 51/100< 51/100+ez*level.val
  upper : 51/100+ez*level.val≤7/8
  next : zeroMaximum chi hn (3*(band.val+1:ℕ)*U^tau)<51/100+ez*level.val+2*ez
  current : 51/100+ez*level.val≤ zeroMaximum chi hn ((3*band.val:ℕ)*U^tau)
  ceiling : response≤(2*(51/100+ez*level.val)-1)+price
  shared : SameZero chi hn U d dmax tau (51/100+ez*level.val) epsilon band.val

/-- Direct conversion of the proven actual provider output, without adding
an analytic premise or changing the underlying response. -/
theorem rowTicket_of_provider {Label : Type*} [Fintype Label]
    (chi : Label→Character) (hn : ∀j,(chi j).residue≠1)
    (U d dmax tau epsilon ez price response : ℝ) (I : ℕ)
    (h : ∃i k : ℕ,1≤ i ∧ i≤ I ∧ k≤⌊(73/200:ℝ)/ez⌋₊ ∧
      let a : ℝ:=51/100+ez*k
      51/100< a ∧ a≤7/8 ∧
      zeroMaximum chi hn (3*(i+1:ℕ)*U^tau)< a+2*ez ∧
      a≤ zeroMaximum chi hn ((3*i:ℕ)*U^tau) ∧
      response≤(2*a-1)+price ∧ Nonempty (SameZero chi hn U d dmax tau a epsilon i)) :
    Nonempty (RowTicket chi hn U d dmax tau epsilon ez price response I) := by
  obtain ⟨i,k,hi,hiI,hk,ha,ha',hnext,hcurrent,hresponse,⟨shared⟩⟩:=h
  exact ⟨⟨⟨i,Nat.lt_succ_iff.mpr hiI⟩,hi,⟨k,Nat.lt_succ_iff.mpr hk⟩,
    ha,ha',hnext,hcurrent,hresponse,shared⟩⟩

/-- Selection over the literal finite retained set. The input is precisely
`rowTicket_of_provider` on each actual row, not a moment inequality. -/
theorem select_original_row_tickets {Label : Type*} [Fintype Label]
    (rows : Finset FreeRow) (chi : ∀u : rows,Label→Character)
    (hn : ∀u j,(chi u j).residue≠1)
    (U d dmax tau epsilon ez price : ℝ) (response : FreeRow→ℝ) (I : ℕ)
    (h : ∀u : rows,Nonempty (RowTicket (chi u) (hn u) U d dmax tau epsilon ez price (response u.val) I)) :
    Nonempty (∀u : rows,RowTicket (chi u) (hn u) U d dmax tau epsilon ez price (response u.val) I) := by
  exact ⟨fun u=> Classical.choice (h u)⟩

/-- Finite dictionary at a later admitted cutoff. All labels and dyads are
read from the real supported witness and use the native dyadicLength. -/
def rowTicketKey {Label : Type*} [Fintype Label]
    {chi : Label→Character} {hn : ∀j,(chi j).residue≠1}
    {U d dmax tau epsilon ez price response : ℝ} {I : ℕ}
    (ticket : RowTicket chi hn U d dmax tau epsilon ez price response I)
    (cutoff : ℝ) (h0 : 1≤ cutoff) (h1 : cutoff≤3/2) :
    TicketKey Label I ⌊(73/200:ℝ)/ez⌋₊ (dyadicLength (U^d)) :=
  (ticket.band,ticket.level,(ticket.shared.witness cutoff h0 h1).label,
    (ticket.shared.witness cutoff h0 h1).left,(ticket.shared.witness cutoff h0 h1).right)

/-- The row response and the original union zero band are unchanged; one
attainer works simultaneously for all later admitted cutoff witnesses. -/
theorem row_ticket_attainer {Label : Type*} [Fintype Label]
    {chi : Label→Character} {hn : ∀j,(chi j).residue≠1}
    {U d dmax tau epsilon ez price response : ℝ} {I : ℕ}
    (ticket : RowTicket chi hn U d dmax tau epsilon ez price response I) :
    LFunction (chi ticket.shared.label) ticket.shared.zero=0 ∧
    ticket.shared.zero.re=zeroMaximum chi hn ((3*ticket.band.val:ℕ)*U^tau) ∧
    ∀cutoff h0 h1,(ticket.shared.witness cutoff h0 h1).label=ticket.shared.label ∧
      (ticket.shared.witness cutoff h0 h1).zero=ticket.shared.zero := by
  exact ⟨ticket.shared.is_zero,ticket.shared.maximum,
    fun cutoff h0 h1=>⟨ticket.shared.same_label cutoff h0 h1,ticket.shared.same_zero cutoff h0 h1⟩⟩

end
end QRH.Cycle092.TerminalActualRow
#print axioms QRH.Cycle092.TerminalActualRow.rowTicket_of_provider
#print axioms QRH.Cycle092.TerminalActualRow.select_original_row_tickets
#print axioms QRH.Cycle092.TerminalActualRow.row_ticket_attainer
