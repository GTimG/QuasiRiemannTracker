/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact metadata and late functions of the genuine original P2 suppliers. -/
import Candidate.C092.transport.P2CommonSourceMetadataReady
import Candidate.C092.transport.P2CommonSourceMetadataSchedule
import Candidate.C092.transport.RegularColoredTerminalLeafDetector
import Candidate.C092.transport.P2CommonSourceMetadataInverse
import Candidate.C092.transport.P2CommonSourceMetadataTableBank
import Candidate.C092.transport.P2CommonSourceMetadataTypes
import Candidate.C092.transport.RegularColoredTerminalLeafTable
import Candidate.C092.transport.RegularColoredTerminalLeafLowHigh
import Candidate.C092.transport.RegularColoredTerminalLeafSmallActual
import Candidate.C092.transport.RegularColoredTerminalLeafOrdinaryBank
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.P2CommonSourceMetadata
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros HeckeDetectorRowwisePolynomial
open ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentHeckeSlots HeckePrimeAnnular
open QRH.Cycle092.WholeSlot
open CenteredMomentPrimeSlot CenteredMomentDetectorPlainFiberSource
open QRH.Cycle092.PairMarkAnchor QRH.Cycle092.TinyCore QRH.Cycle092.MediumReplace.Source
open QRH.Cycle090 QRH.SourceCertificate QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness
open QRH.Cycle092.StrongPair QRH.Cycle092.LowActual QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.RegularColoredForward QRH.Cycle092.SourceInverseP6 QRH.Cycle092.MediumInversePrice
open QRH.Cycle092.OrdinaryColumn Qrh.MarkedAnchor.Interface
local notation "O" =>  HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_P2CommonSourceMetadataDetector_52056635f8043a0c_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

def DetectorFactory (Slot : Type) [Fintype Slot]
    (buffer price Rwidth bΦ Mcap Bmask margin d dmin dmax τ η ε κ heightCost y step : ℝ)
    (cell : Cell) (table : TerminalResponseTable y step cell) (ezmax : ℝ) : Prop :=
        ∀ez : ℝ,0 < ez → ez ≤ ezmax → 12*ez*(22+2)+8*κ+2*heightCost ≤ ε/2 →
    ∀(M : Ideal O) [NeZero M] (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H),
    ∀W : ℝ→ℂ,Function.support W⊆Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
    ∃I : ℕ,0 < I ∧ ∃C : ℝ,0 < C ∧ ∀base : Character,∀ᶠ U : ℝ in atTop,1 < U ∧
    ∀Cslot : ℝ,C ≤ Cslot →
    ∀s : NaturalState U Bmask bΦ,s.width ≤ Mcap → s.mask=fixedBadMask*idealGenerator 1 →
    ∀(hQM : s.fixedModulus ≤ M) (hQbase : s.fixedModulus ≤ base.modulus)
      (θ : Slot→RayQuotient.Characters M H) (w v : Slot→ℝ) (t height : ℝ),
      (∀j,0 ≤ w j) → (∀j,w j/d ≤ Rwidth) →
      (∀j,|v j| ≤ height) → |t|+height ≤ U^τ →
    ∀(rows : Finset FreeRow) (hrows : ∀u∈rows,s.radial.keep u.val),
      (∀u∈rows,s.radial.profile (‖eisEmbedding u.val‖^2/s.radial.scale)≠0) →
      (∀u∈rows,(cell.threshold:ℝ) ≤ measured M H hH s.character base W U (Cslot*U^buffer) θ w v t u ∧
        measured M H hH s.character base W U (Cslot*U^buffer) θ w v t u ≤ (responseUpper:ℝ)) →
    let χ := fun u : rows=>family M H hH s base (naturalRow s.character u.val.val u.val.property.1);
    let hn := fun u : rows=>family_nonprincipal M H hH s base hQM hQbase (hrows u.val u.property)
      (naturalRow s.character u.val.val u.val.property.1);
    ∃ticket : ∀u : rows,RowTicket (χ u) (hn u) U d dmax τ ε ez price
      (measured M H hH s.character base W U (Cslot*U^buffer) θ w v t u.val) I,
    ∃window : rows→Fin table.Je×Fin table.Jν,
    ∃ws : ∀u : rows,SupportedWitness (χ u) (U^d) ((51/100:ℝ)+ez*(ticket u).level.val) ε
      (totalCutoff (table.cutoff (window u))) (U^τ) ((U^d)^(τ/(2*dmax))) (ticket u).band.val,
      (∀u : rows,table.egrid (window u).1 ≤ measured M H hH s.character base W U (Cslot*U^buffer) θ w v t u.val ∧
        measured M H hH s.character base W U (Cslot*U^buffer) θ w v t u.val < table.egrid (window u).1+step ∧
        max (table.egrid (window u).1) (table.νgrid (window u).2) ≤ 2*((51/100:ℝ)+ez*(ticket u).level.val)-1+price ∧
        2*((51/100:ℝ)+ez*(ticket u).level.val)-1 < max (table.egrid (window u).1) (table.νgrid (window u).2)+step) ∧
      (∀u : rows,(ws u).label=(ticket u).shared.label ∧ (ws u).zero=(ticket u).shared.zero)

def DetectorAt (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (buffer price dmin dmax y step : ℝ) (cell : Cell) (table : TerminalResponseTable y step cell)
    (dBank : Finset ℝ) (G : LateGeometry dmin dmax dBank) (db : dBank) (I : ℕ) (Cslot U : ℝ) : Prop :=
        ∀s : NaturalState U (G.Bmask) (A.bΦ),s.width ≤ G.Mcap db → s.mask=fixedBadMask*idealGenerator 1 →
    ∀(hQM : s.fixedModulus ≤ M) (hQbase : s.fixedModulus ≤ (A.baseShort).modulus)
      (θ : Slot→RayQuotient.Characters M (A.Hr)) (w v : Slot→ℝ) (t height : ℝ),
      (∀j,0 ≤ w j) → (∀j,w j/(db.val) ≤ (22:ℝ)) →
      (∀j,|v j| ≤ height) → |t|+height ≤ U^(G.τ) →
    ∀(rows : Finset FreeRow) (hrows : ∀u∈rows,s.radial.keep u.val),
      (∀u∈rows,s.radial.profile (‖eisEmbedding u.val‖^2/s.radial.scale)≠0) →
      (∀u∈rows,(cell.threshold:ℝ) ≤ measured M (A.Hr) (A.hHr) s.character (A.baseShort) (A.W) U (Cslot*U^buffer) θ w v t u ∧
        measured M (A.Hr) (A.hHr) s.character (A.baseShort) (A.W) U (Cslot*U^buffer) θ w v t u ≤ (responseUpper:ℝ)) →
    let χ := fun u : rows=>family M (A.Hr) (A.hHr) s (A.baseShort) (naturalRow s.character u.val.val u.val.property.1);
    let hn := fun u : rows=>family_nonprincipal M (A.Hr) (A.hHr) s (A.baseShort) hQM hQbase (hrows u.val u.property)
      (naturalRow s.character u.val.val u.val.property.1);
    ∃ticket : ∀u : rows,RowTicket (χ u) (hn u) U (db.val) dmax (G.τ) (G.ε) (G.ez) (price)
      (measured M (A.Hr) (A.hHr) s.character (A.baseShort) (A.W) U (Cslot*U^buffer) θ w v t u.val) I,
    ∃window : rows→Fin table.Je×Fin table.Jν,
    ∃ws : ∀u : rows,SupportedWitness (χ u) (U^(db.val)) ((51/100:ℝ)+(G.ez)*(ticket u).level.val) (G.ε)
      (totalCutoff (table.cutoff (window u))) (U^(G.τ)) ((U^(db.val))^((G.τ)/(2*dmax))) (ticket u).band.val,
      (∀u : rows,table.egrid (window u).1 ≤ measured M (A.Hr) (A.hHr) s.character (A.baseShort) (A.W) U (Cslot*U^buffer) θ w v t u.val ∧
        measured M (A.Hr) (A.hHr) s.character (A.baseShort) (A.W) U (Cslot*U^buffer) θ w v t u.val < table.egrid (window u).1+step ∧
        max (table.egrid (window u).1) (table.νgrid (window u).2) ≤ 2*((51/100:ℝ)+(G.ez)*(ticket u).level.val)-1+(price) ∧
        2*((51/100:ℝ)+(G.ez)*(ticket u).level.val)-1 < max (table.egrid (window u).1) (table.νgrid (window u).2)+step) ∧
      (∀u : rows,(ws u).label=(ticket u).shared.label ∧ (ws u).zero=(ticket u).shared.zero)

structure DetectorPacket (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (buffer price dmin dmax y step : ℝ) (cell : Cell) (table : TerminalResponseTable y step cell)
    (dBank : Finset ℝ) (G : LateGeometry dmin dmax dBank) (db : dBank) where
  I : ℕ
  I_pos : 0 < I
  C : ℝ
  C_pos : 0 < C
  event : ∀ᶠ U : ℝ in atTop,1 < U ∧ ∀Cslot : ℝ,C ≤ Cslot →
    DetectorAt Slot M A buffer price dmin dmax y step cell table dBank G db I Cslot U

/-- Only the zero collar is lowered; all early degrees and the chosen
height exponent, conductor geometry and source errors remain literal. -/
def shrinkEz {dmin dmax : ℝ} {dBank : Finset ℝ}
    (G : LateGeometry dmin dmax dBank) (ezmax : ℝ) (hmax : 0 < ezmax) :
    LateGeometry dmin dmax dBank := {
  G with
  ez := min G.ez ezmax
  hez := lt_min G.hez hmax
  hez_small := (min_le_left _ _).trans_lt G.hez_small
  budget := (by
    have h := mul_le_mul_of_nonneg_right (min_le_left G.ez ezmax) (show 0 ≤ 12*(G.R+2) by have h:=G.hR;positivity)
    nlinarith only [h,G.budget]) }

/-- The true detector is called for every surviving subset and conductor
cap. Its finite positive collars are minimized BEFORE the late orders and
unit-profile bank. Every returned I and ceiling payment is retained with
the genuine original-row ticket function. -/
theorem genuine_detector_schedule {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    {M : Ideal O} [NeZero M] (A : Arithmetic M)
    {buffer price dmin dmax y step : ℝ} {cell : Cell}
    (table : TerminalResponseTable y step cell) {dBank : Finset ℝ}
    (G0 : LateGeometry dmin dmax dBank)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hbuffer : 0 < buffer) (hprice : 0 < price)
    (hgap : (1/50:ℝ)+price < (cell.threshold:ℝ)) (hdmin : 0 < dmin)
    (hdb : ∀d∈dBank,dmin ≤ d ∧ d ≤ dmax)
    (hdsupply : ∀d : dBank,G0.Mcap d+G0.Bmask+G0.margin ≤ d.val)
    (hcost : G0.heightCost ≤ 1)
    (hdetector : 12*G0.ez*(22+2)+8*G0.κ+2*G0.heightCost ≤ G0.ε/2) :
    ∃ezmax : ℝ,∃hmax : 0 < ezmax,
      Nonempty (∀(T : Finset Slot) (d : dBank),
        DetectorPacket T M A buffer price dmin dmax y step cell table dBank (shrinkEz G0 ezmax hmax) d) := by
  classical
  have hτ0 : G0.τ < dmin/2 := by
    have h := mul_le_mul_of_nonneg_left hcost hdmin.le
    nlinarith only [h,G0.height,hdmin]
  let Key := Finset Slot × dBank
  have hf (p : Key) : ∃em : ℝ,0 < em ∧ em < 1/1000 ∧
      DetectorFactory p.1 buffer price 22 A.bΦ (G0.Mcap p.2) G0.Bmask G0.margin
        p.2.val dmin dmax G0.τ G0.heightCost G0.ε G0.κ G0.heightCost y step cell table em := by
    have hheight : 2*G0.τ < p.2.val*G0.heightCost := by
      have h := mul_le_mul_of_nonneg_right (hdb p.2.val p.2.property).1 G0.heightCost_nonneg
      nlinarith only [h,G0.height,G0.hτ]
    exact terminal_actual_medium_tickets (Slot:=p.1) hβ buffer price 22 A.bΦ
      (G0.Mcap p.2) G0.Bmask G0.margin p.2.val dmin dmax G0.τ G0.heightCost G0.ε G0.κ G0.heightCost
      y step cell table hbuffer hprice hgap (by norm_num) (by have h:=A.hbΦ;linarith) G0.hmargin
      hdmin G0.hdmax (hdb p.2.val p.2.property).1 (hdb p.2.val p.2.property).2 (hdsupply p.2)
      G0.hτ hτ0 G0.height G0.heightCost_nonneg hheight G0.hε G0.hκ G0.hκ_small G0.heightCost_nonneg
  choose em hem hemsmall hfactory using hf
  obtain ⟨floor,hfloor,hfloorle⟩ := terminal_positive_mesh_floor em hem
  let G := shrinkEz G0 floor hfloor
  have hbudget : 12*G.ez*(22+2)+8*G.κ+2*G.heightCost ≤ G.ε/2 := by
    have he : G.ez ≤ G0.ez := min_le_left _ _
    change 12*G.ez*(22+2)+8*G0.κ+2*G0.heightCost ≤ G0.ε/2
    nlinarith only [he,hdetector]
  have hp (p : Key) : Nonempty (DetectorPacket p.1 M A buffer price dmin dmax y step cell table dBank G p.2) := by
    have he : G.ez ≤ em p := (min_le_right _ _).trans (hfloorle p)
    obtain ⟨I,hI,C,hC,hsource⟩ := hfactory p G.ez G.hez he hbudget M A.Hr A.hHr A.W A.hWs A.hW
    exact ⟨⟨I,hI,C,hC,hsource A.baseShort⟩⟩
  exact ⟨floor,hfloor,⟨fun T d=>Classical.choice (hp (T,d))⟩⟩

#print axioms shrinkEz
#print axioms genuine_detector_schedule
end
end QRH.Cycle092.P2CommonSourceMetadata
