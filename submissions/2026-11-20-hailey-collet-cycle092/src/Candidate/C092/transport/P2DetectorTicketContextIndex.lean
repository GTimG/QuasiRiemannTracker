/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
import Candidate.C092.transport.P2DetectorTicketContextSelect
import Candidate.C092.transport.RegularColoredTerminalLeafContext
import Candidate.C092.transport.P2CommonSourceMetadataFinal
import Candidate.C092.transport.RegularColoredTerminalLeafOccupied
import Candidate.C092.transport.RegularColoredTerminalLeafLengths
import Candidate.C092.transport.RegularColoredTerminalLeafHomogeneous
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros
open ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_P2DetectorTicketContextIndex_fb10dda41492fb60_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- The response is identified by the true fixed-character equality;
only the finite index proof is enlarged. Every zero and dictionary datum
is copied literally, including the original measured-response ceiling. -/
def terminal_lift_response_ticket {Label : Type} [Fintype Label]
    {χ : Label→Character} {hn : ∀j,(χ j).residue≠1}
    {U d dmax τ ε ez price response0 response1 : ℝ} {Ilocal I : ℕ}
    (hIJ : Ilocal ≤ I) (hresponse : response0=response1)
    (ticket : RowTicket χ hn U d dmax τ ε ez price response0 Ilocal) :
    RowTicket χ hn U d dmax τ ε ez price response1 I where
  band := ⟨ticket.band.val,by have h:=ticket.band.isLt;omega⟩
  band_pos := ticket.band_pos
  level := ticket.level
  lower := ticket.lower
  upper := ticket.upper
  next := ticket.next
  current := ticket.current
  ceiling := by rw [←hresponse];exact ticket.ceiling
  shared := ticket.shared

theorem terminal_lift_response_ticket_fields {Label : Type} [Fintype Label]
    {χ : Label→Character} {hn : ∀j,(χ j).residue≠1}
    {U d dmax τ ε ez price response0 response1 : ℝ} {Ilocal I : ℕ}
    (hIJ : Ilocal ≤ I) (hresponse : response0=response1)
    (ticket : RowTicket χ hn U d dmax τ ε ez price response0 Ilocal) :
    let lifted := terminal_lift_response_ticket hIJ hresponse ticket;
      lifted.band.val=ticket.band.val ∧ lifted.level=ticket.level ∧
      lifted.shared.label=ticket.shared.label ∧ lifted.shared.zero=ticket.shared.zero := by
  exact ⟨rfl,rfl,rfl,rfl⟩


/-- Lift the entire dependent packet over abstract dictionaries first. The
later large native context copies these opaque, already aligned fields. -/
def liftDetectorTicketSelection {Label : Type} [Fintype Label]
    {rows : Finset FreeRow} {χ : ∀z : rows,Label→Character}
    {hn : ∀z j,(χ z j).residue≠1}
    {U d dmax τ ε ez price y step : ℝ} {response0 response1 : FreeRow→ℝ}
    {Ilocal I : ℕ} {cell : Cell} {table : TerminalResponseTable y step cell}
    (hIJ : Ilocal ≤ I) (hresponse : ∀z : rows,response0 z.val=response1 z.val)
    (S : DetectorTicketSelection rows χ hn U d dmax τ ε ez price y step response0 Ilocal table) :
    DetectorTicketSelection rows χ hn U d dmax τ ε ez price y step response1 I table := by
  let ticket := fun z : rows=>terminal_lift_response_ticket hIJ (hresponse z) (S.ticket z)
  have hlevel (z : rows) : (ticket z).level=(S.ticket z).level := rfl
  exact {
    ticket:=ticket,window:=S.window,witness:=S.witness,
    window_bound:=(by intro z;rw [hlevel z,←hresponse z];exact S.window_bound z),
    same:=S.same }

theorem liftDetectorTicketSelection_fields {Label : Type} [Fintype Label]
    {rows : Finset FreeRow} {χ : ∀z : rows,Label→Character}
    {hn : ∀z j,(χ z j).residue≠1}
    {U d dmax τ ε ez price y step : ℝ} {response0 response1 : FreeRow→ℝ}
    {Ilocal I : ℕ} {cell : Cell} {table : TerminalResponseTable y step cell}
    (hIJ : Ilocal ≤ I) (hresponse : ∀z : rows,response0 z.val=response1 z.val)
    (S : DetectorTicketSelection rows χ hn U d dmax τ ε ez price y step response0 Ilocal table) :
    let L := liftDetectorTicketSelection hIJ hresponse S;
      L.window=S.window ∧ ∀z : rows,
        (L.ticket z).band.val=(S.ticket z).band.val ∧ (L.ticket z).level=(S.ticket z).level ∧
        (L.witness z).label=(S.witness z).label ∧ (L.witness z).zero=(S.witness z).zero := by
  exact ⟨rfl,fun _=>⟨rfl,rfl,rfl,rfl⟩⟩

#print axioms terminal_lift_response_ticket_fields
#print axioms liftDetectorTicketSelection_fields
end
end QRH.Cycle092.RegularColoredForward
