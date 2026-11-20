/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
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
local instance c092LocalInst_Candidate_C092_transport_P2DetectorTicketContextSelect_987dbb705ee82af9_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- A small retained packet separates genuine detector choice from the
later geometry record. It preserves the original selected window and zero. -/
structure DetectorTicketSelection {Label : Type} [Fintype Label]
    (rows : Finset FreeRow) (χ : ∀z : rows,Label→Character)
    (hn : ∀z j,(χ z j).residue≠1)
    (U d dmax τ ε ez price y step : ℝ) (response : FreeRow→ℝ) (I : ℕ)
    {cell : Cell} (table : TerminalResponseTable y step cell) where
  ticket : ∀z : rows,RowTicket (χ z) (hn z) U d dmax τ ε ez price (response z.val) I
  window : rows→Fin table.Je×Fin table.Jν
  witness : ∀z : rows,SupportedWitness (χ z) (U^d) ((51/100:ℝ)+ez*(ticket z).level.val) ε
    (totalCutoff (table.cutoff (window z))) (U^τ) ((U^d)^(τ/(2*dmax))) (ticket z).band.val
  window_bound : ∀z : rows,
    table.egrid (window z).1 ≤ response z.val ∧ response z.val < table.egrid (window z).1+step ∧
    max (table.egrid (window z).1) (table.νgrid (window z).2) ≤ 2*((51/100:ℝ)+ez*(ticket z).level.val)-1+price ∧
    2*((51/100:ℝ)+ez*(ticket z).level.val)-1 < max (table.egrid (window z).1) (table.νgrid (window z).2)+step
  same : ∀z : rows,(witness z).label=(ticket z).shared.label ∧ (witness z).zero=(ticket z).shared.zero

/-- This is exactly the retained actual DetectorAt call on the supplied
original rows. It asserts no moment, row count or class energy. -/
theorem detector_ticket_selection_at
    {Slot : Type} [Fintype Slot] {M : Ideal O} [NeZero M] (A : Arithmetic M)
    {dmin dmax : ℝ} {dBank : Finset ℝ} (G : LateGeometry dmin dmax dBank) (db : dBank)
    {buffer price U y step Cslot : ℝ} {I : ℕ} {cell : Cell} (table : TerminalResponseTable y step cell)
    (hDetector : DetectorAt Slot M A buffer price dmin dmax y step cell table dBank G db I Cslot U)
    (s : NaturalState U G.Bmask A.bΦ) (hs : s.width ≤ G.Mcap db)
    (hmask : s.mask=fixedBadMask*idealGenerator 1)
    (hsM : s.fixedModulus ≤ M) (hsBase : s.fixedModulus ≤ A.baseShort.modulus)
    (θ : Slot→RayQuotient.Characters M A.Hr) (w v : Slot→ℝ) (t height : ℝ)
    (hw : ∀j,0 ≤ w j) (hwd : ∀j,w j/db.val ≤ 22) (hv : ∀j,|v j| ≤ height)
    (ht : |t|+height ≤ U^G.τ)
    (rows : Finset FreeRow) (hkeep : ∀z∈rows,s.radial.keep z.val)
    (hplateau : ∀z∈rows,s.radial.profile (‖eisEmbedding z.val‖^2/s.radial.scale)≠0)
    (hmedium : ∀z∈rows,(cell.threshold:ℝ) ≤ measured M A.Hr A.hHr s.character A.baseShort A.W U
      (Cslot*U^buffer) θ w v t z ∧ measured M A.Hr A.hHr s.character A.baseShort A.W U
      (Cslot*U^buffer) θ w v t z ≤ (responseUpper:ℝ)) :
    Nonempty (DetectorTicketSelection rows
      (fun z=>family M A.Hr A.hHr s A.baseShort (naturalRow s.character z.val.val z.val.property.1))
      (fun z=>family_nonprincipal M A.Hr A.hHr s A.baseShort hsM hsBase (hkeep z.val z.property)
        (naturalRow s.character z.val.val z.val.property.1))
      U db.val dmax G.τ G.ε G.ez price y step
      (fun z=>measured M A.Hr A.hHr s.character A.baseShort A.W U (Cslot*U^buffer) θ w v t z) I table) := by
  obtain ⟨ticket,window,ws,hwindow,hsame⟩ := hDetector s hs hmask hsM hsBase θ w v t height
    hw hwd hv ht rows hkeep hplateau hmedium
  exact ⟨⟨ticket,window,ws,hwindow,hsame⟩⟩

#print axioms detector_ticket_selection_at
end
end QRH.Cycle092.RegularColoredForward
