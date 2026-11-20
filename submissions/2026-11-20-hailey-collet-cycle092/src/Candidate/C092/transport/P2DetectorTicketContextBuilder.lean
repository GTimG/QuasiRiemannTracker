/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
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
local instance c092LocalInst_Candidate_C092_transport_P2DetectorTicketContextBuilder_befcb729d55bbed2_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def normalizedContextSelection
    {Slot : Type} [Fintype Slot] [DecidableEq Slot] {M : Ideal O} [NeZero M] (A : Arithmetic M)
    {dmin dmax : ℝ} {dBank : Finset ℝ} (G : LateGeometry dmin dmax dBank) (db : dBank)
    {n y mesh buffer price U V Cslot step : ℝ} {Ilocal I : ℕ} {cell : Cell}
    (table : TerminalResponseTable y step cell)
    (hIJ : Ilocal ≤ I)
    (B : TerminalRowGeometry Slot M A G db n y mesh buffer price U V Cslot table)
    (selected : DetectorTicketSelection B.rows
      (fun z=>family M A.Hr A.hHr B.state A.baseShort (naturalRow B.state.character z.val.val z.val.property.1))
      (fun z=>family_nonprincipal M A.Hr A.hHr B.state A.baseShort B.modulus_ray B.modulus_base (B.keep z.val z.property)
        (naturalRow B.state.character z.val.val z.val.property.1))
      U db.val dmax G.τ G.ε G.ez price y step
      (fun z=>measured M A.Hr A.hHr B.state.character A.baseShort A.W U (Cslot*U^buffer) B.theta B.w B.v B.tShort z) Ilocal table) :
    DetectorTicketSelection B.rows
      (fun z=>family M A.Hr A.hHr B.state A.baseShort (naturalRow B.state.character z.val.val z.val.property.1))
      (fun z=>family_nonprincipal M A.Hr A.hHr B.state A.baseShort B.modulus_ray B.modulus_base (B.keep z.val z.property)
        (naturalRow B.state.character z.val.val z.val.property.1))
      U db.val dmax G.τ G.ε G.ez price y step
      (fun z=>measured M A.Hr A.hHr A.ηShort A.baseShort A.W U (Cslot*U^buffer) B.theta B.w B.v B.tShort z) I table := by
  exact liftDetectorTicketSelection hIJ
    (show ∀z : B.rows,measured M A.Hr A.hHr B.state.character A.baseShort A.W U (Cslot*U^buffer) B.theta B.w B.v B.tShort z.val=
      measured M A.Hr A.hHr A.ηShort A.baseShort A.W U (Cslot*U^buffer) B.theta B.w B.v B.tShort z.val
      from fun z=>by rw [B.character]) selected

def ticketContextOfSelection
    {Slot : Type} [Fintype Slot] [DecidableEq Slot] {M : Ideal O} [NeZero M] (A : Arithmetic M)
    {dmin dmax : ℝ} {dBank : Finset ℝ} (G : LateGeometry dmin dmax dBank) (db : dBank)
    {n y mesh buffer price U V Cslot step : ℝ} {Ilocal I : ℕ} {cell : Cell}
    (table : TerminalResponseTable y step cell)
    (hIJ : Ilocal ≤ I)
    (B : TerminalRowGeometry Slot M A G db n y mesh buffer price U V Cslot table)
    (selected : DetectorTicketSelection B.rows
      (fun z=>family M A.Hr A.hHr B.state A.baseShort (naturalRow B.state.character z.val.val z.val.property.1))
      (fun z=>family_nonprincipal M A.Hr A.hHr B.state A.baseShort B.modulus_ray B.modulus_base (B.keep z.val z.property)
        (naturalRow B.state.character z.val.val z.val.property.1))
      U db.val dmax G.τ G.ε G.ez price y step
      (fun z=>measured M A.Hr A.hHr B.state.character A.baseShort A.W U (Cslot*U^buffer) B.theta B.w B.v B.tShort z) Ilocal table) :
    TerminalTicketContext Slot M A G db n y mesh buffer price U V Cslot I table := by
  let S := normalizedContextSelection A G db table hIJ B selected
  exact {
    rows:=B.rows,state:=B.state,width_bound:=B.width_bound,character:=B.character,puncture:=B.puncture,
    modulus_ray:=B.modulus_ray,modulus_base:=B.modulus_base,keep:=B.keep,keep_equiv:=B.keep_equiv,plateau:=B.plateau,
    row_norm:=B.row_norm,long_keep:=B.long_keep,theta:=B.theta,thetaLong:=B.thetaLong,w:=B.w,v:=B.v,vLong:=B.vLong,
    tShort:=B.tShort,tLong:=B.tLong,height:=B.height,height_nonneg:=B.height_nonneg,pitch:=B.pitch,pitchLong:=B.pitchLong,
    native_height:=B.native_height,width_nonneg:=B.width_nonneg,width_mesh:=B.width_mesh,width_sum:=B.width_sum,
    physical:=B.physical,short_presentation:=B.short_presentation,long_presentation:=B.long_presentation,
    X:=B.X,Y:=B.Y,long_positive:=B.long_positive,short_positive:=B.short_positive,long_cap:=B.long_cap,short_cap:=B.short_cap,
    ticket:=S.ticket,window:=S.window,witness:=S.witness,window_bound:=S.window_bound }

theorem ticketContextOfSelection_matches
    {Slot : Type} [Fintype Slot] [DecidableEq Slot] {M : Ideal O} [NeZero M] (A : Arithmetic M)
    {dmin dmax : ℝ} {dBank : Finset ℝ} (G : LateGeometry dmin dmax dBank) (db : dBank)
    {n y mesh buffer price U V Cslot step : ℝ} {Ilocal I : ℕ} {cell : Cell}
    (table : TerminalResponseTable y step cell)
    (hIJ : Ilocal ≤ I)
    (B : TerminalRowGeometry Slot M A G db n y mesh buffer price U V Cslot table)
    (selected : DetectorTicketSelection B.rows
      (fun z=>family M A.Hr A.hHr B.state A.baseShort (naturalRow B.state.character z.val.val z.val.property.1))
      (fun z=>family_nonprincipal M A.Hr A.hHr B.state A.baseShort B.modulus_ray B.modulus_base (B.keep z.val z.property)
        (naturalRow B.state.character z.val.val z.val.property.1))
      U db.val dmax G.τ G.ε G.ez price y step
      (fun z=>measured M A.Hr A.hHr B.state.character A.baseShort A.W U (Cslot*U^buffer) B.theta B.w B.v B.tShort z) Ilocal table) :
    let D := ticketContextOfSelection A G db table hIJ B selected;
      D.rows=B.rows ∧ D.state=B.state ∧ D.physical=B.physical ∧ D.X=B.X ∧ D.Y=B.Y ∧
      D.tLong=B.tLong ∧ D.tShort=B.tShort ∧ D.theta=B.theta ∧ D.thetaLong=B.thetaLong ∧
      D.w=B.w ∧ D.v=B.v ∧ D.vLong=B.vLong ∧ D.height=B.height ∧
      ∀z : D.rows,(D.witness z).label=(D.ticket z).shared.label ∧
        (D.witness z).zero=(D.ticket z).shared.zero := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,(normalizedContextSelection A G db table hIJ B selected).same⟩

#print axioms ticketContextOfSelection_matches
end
end QRH.Cycle092.RegularColoredForward
