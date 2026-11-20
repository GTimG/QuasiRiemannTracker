/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
import Candidate.C092.transport.P2DetectorTicketContextBuilder
import Candidate.C092.transport.P2DetectorTicketContextGeometry
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
local instance c092LocalInst_Candidate_C092_transport_P2DetectorTicketContextCore_c1448900896bc619_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem terminal_ticket_context_from_geometry
    {Slot : Type} [Fintype Slot] [DecidableEq Slot] {M : Ideal O} [NeZero M] (A : Arithmetic M)
    {dmin dmax : ℝ} {dBank : Finset ℝ} (G : LateGeometry dmin dmax dBank) (db : dBank)
    {n y mesh buffer price U V Cslot step : ℝ} {Ilocal I : ℕ} {cell : Cell}
    (table : TerminalResponseTable y step cell)
    (hDetector : DetectorAt Slot M A buffer price dmin dmax y step cell table dBank G db Ilocal Cslot U)
    (hIJ : Ilocal ≤ I)
    (B : TerminalRowGeometry Slot M A G db n y mesh buffer price U V Cslot table)
    (hwd : ∀j,B.w j/db.val ≤ 22)
    (hmedium : ∀z∈B.rows,(cell.threshold:ℝ) ≤ measured M A.Hr A.hHr A.ηShort A.baseShort A.W U
      (Cslot*U^buffer) B.theta B.w B.v B.tShort z ∧ measured M A.Hr A.hHr A.ηShort A.baseShort A.W U
      (Cslot*U^buffer) B.theta B.w B.v B.tShort z ≤ (responseUpper:ℝ)) :
    ∃D : TerminalTicketContext Slot M A G db n y mesh buffer price U V Cslot I table,
      D.rows=B.rows ∧ D.state=B.state ∧ D.physical=B.physical ∧ D.X=B.X ∧ D.Y=B.Y ∧
      D.tLong=B.tLong ∧ D.tShort=B.tShort ∧ D.theta=B.theta ∧ D.thetaLong=B.thetaLong ∧
      D.w=B.w ∧ D.v=B.v ∧ D.vLong=B.vLong ∧ D.height=B.height ∧
      ∀z : D.rows,(D.witness z).label=(D.ticket z).shared.label ∧
        (D.witness z).zero=(D.ticket z).shared.zero := by
  classical
  have hmask : B.state.mask=fixedBadMask*idealGenerator 1 := by simp only [NaturalState.mask,B.puncture]
  have hheightShort : |B.tShort|+B.height ≤ U^G.τ := by linarith only [B.native_height,B.height_nonneg,abs_nonneg B.tLong]
  have hmedium' : ∀z∈B.rows,(cell.threshold:ℝ) ≤ measured M A.Hr A.hHr B.state.character A.baseShort A.W U
      (Cslot*U^buffer) B.theta B.w B.v B.tShort z ∧ measured M A.Hr A.hHr B.state.character A.baseShort A.W U
      (Cslot*U^buffer) B.theta B.w B.v B.tShort z ≤ (responseUpper:ℝ) := by simpa only [B.character] using hmedium
  let selected := Classical.choice (detector_ticket_selection_at A G db table hDetector B.state B.width_bound hmask B.modulus_ray B.modulus_base
    B.theta B.w B.v B.tShort B.height B.width_nonneg hwd B.pitch hheightShort B.rows B.keep B.plateau hmedium')
  exact ⟨ticketContextOfSelection A G db table hIJ B selected,
    ticketContextOfSelection_matches A G db table hIJ B selected⟩

#print axioms terminal_ticket_context_from_geometry
end
end QRH.Cycle092.RegularColoredForward
