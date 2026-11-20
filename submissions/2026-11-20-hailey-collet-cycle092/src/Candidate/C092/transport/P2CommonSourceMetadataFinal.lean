/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact metadata and late functions of the genuine original P2 suppliers. -/
import Candidate.C092.transport.P2CommonSourceMetadataProfiles
import Candidate.C092.transport.P2CommonSourceMetadataEvents
import Candidate.C092.transport.P2CommonSourceMetadataDetector
import Candidate.C092.transport.TerminalProfileUniformCommon
import Candidate.C092.transport.TerminalProfileUniformPair
import Candidate.C092.transport.TerminalActualInverseApplyProfiles
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
local instance c092LocalInst_Candidate_C092_transport_P2CommonSourceMetadataFinal_791815f61851551c_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- All detector functions are genuine and fixed before Cslot and U. -/
abbrev DetectorBank (Slot : Type) [Fintype Slot] [DecidableEq Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (buffer price dmin dmax y step : ℝ) (cell : Cell) (table : TerminalResponseTable y step cell)
    (dBank : Finset ℝ) (G : LateGeometry dmin dmax dBank) :=
  ∀(T : Finset Slot) (d : dBank),DetectorPacket T M A buffer price dmin dmax y step cell table dBank G d

namespace DetectorBank
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot] {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {buffer price dmin dmax y step : ℝ} {cell : Cell} {table : TerminalResponseTable y step cell}
variable {dBank : Finset ℝ} {G : LateGeometry dmin dmax dBank}

def indexBound (D : DetectorBank Slot M A buffer price dmin dmax y step cell table dBank G) : ℕ :=
  1+Finset.univ.sup (fun p : Finset Slot×dBank=>(D p.1 p.2).I)

def paymentFloor (D : DetectorBank Slot M A buffer price dmin dmax y step cell table dBank G) : ℝ :=
  1+∑p : Finset Slot×dBank,(D p.1 p.2).C

theorem index_pos (D : DetectorBank Slot M A buffer price dmin dmax y step cell table dBank G) :
    0 < D.indexBound := by unfold indexBound;omega

theorem index_le (D : DetectorBank Slot M A buffer price dmin dmax y step cell table dBank G)
    (T : Finset Slot) (d : dBank) : (D T d).I ≤ D.indexBound := by
  have h := Finset.le_sup (f:=fun p : Finset Slot×dBank=>(D p.1 p.2).I) (Finset.mem_univ (T,d))
  dsimp only at h
  unfold indexBound
  omega

theorem payment_one (D : DetectorBank Slot M A buffer price dmin dmax y step cell table dBank G) :
    1 ≤ D.paymentFloor := by
  have h := Finset.sum_nonneg (s:=Finset.univ) (fun (p : Finset Slot×dBank) _=>(D p.1 p.2).C_pos.le)
  unfold paymentFloor
  linarith

theorem payment_pos (D : DetectorBank Slot M A buffer price dmin dmax y step cell table dBank G) :
    0 < D.paymentFloor := by
  have h := Finset.sum_nonneg (s:=Finset.univ) (fun (p : Finset Slot×dBank) _=>(D p.1 p.2).C_pos.le)
  unfold paymentFloor
  linarith

theorem payment_le (D : DetectorBank Slot M A buffer price dmin dmax y step cell table dBank G)
    (T : Finset Slot) (d : dBank) : (D T d).C ≤ D.paymentFloor := by
  have h := Finset.single_le_sum (f:=fun p : Finset Slot×dBank=>(D p.1 p.2).C)
    (fun (p : Finset Slot×dBank) _=>(D p.1 p.2).C_pos.le) (Finset.mem_univ (T,d))
  dsimp only at h
  unfold paymentFloor
  linarith

theorem common_event (D : DetectorBank Slot M A buffer price dmin dmax y step cell table dBank G)
    (Cslot : ℝ) (hCslot : D.paymentFloor ≤ Cslot) :
    ∀ᶠ U : ℝ in atTop,∀(T : Finset Slot) (d : dBank),
      DetectorAt T M A buffer price dmin dmax y step cell table dBank G d (D T d).I Cslot U := by
  apply Filter.eventually_all.mpr
  intro T
  apply Filter.eventually_all.mpr
  intro d
  filter_upwards [(D T d).event] with U hU
  exact hU.2 Cslot ((D.payment_le T d).trans hCslot)
end DetectorBank

variable {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {e Vmax smallMesh lowMesh ordinaryMesh εsource buffer : ℝ}
variable {ordinaryBank : Finset (ℝ×ℝ)} {dec : (ℝ×ℝ) → ℝ}
variable {B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError}

/-- The final collar is selected using the actual detector before any late
Mellin order or normalization. Both the source packets and the detector bank
are retained; the finite response window table is never changed. -/
theorem genuine_terminal_metadata
    (P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B)
    (G0 : LateGeometry dmin dmax dBank) (m0 gap : ℝ) (V : ℝ→ℂ) (hV : ContDiff ℝ ∞ V)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hbuffer : 0 < buffer) (hprice : 0 < price)
    (hgap : (1/50:ℝ)+price < (cell.threshold:ℝ)) (hdmin : 0 < dmin)
    (hdb : ∀d∈dBank,dmin ≤ d ∧ d ≤ dmax)
    (hdsupply : ∀d : dBank,G0.Mcap d+G0.Bmask+G0.margin ≤ d.val)
    (hcost : G0.heightCost ≤ 1)
    (hdetector : 12*G0.ez*(22+2)+8*G0.κ+2*G0.heightCost ≤ G0.ε/2)
    (hes : 0 ≤ εsource)
    (hbank : ∀b∈ordinaryBank,(98/100:ℝ) ≤ b.1 ∧ b.1 ≤ (QRH.SourceCertificate.H:ℝ) ∧ m0 ≤ b.2 ∧ b.2 ≤ 51/100 ∧
      0 < dec b ∧ dec b ≤ gap ∧ 0 < nearOrdinaryQuota n b.2 b.1-dec b)
    (hnet : ∀d m : ℝ,(98/100:ℝ) ≤ d → m0 ≤ m → m ≤ 51/100 →
      ∃b∈ordinaryBank,b.1 ≤ min d (QRH.SourceCertificate.H:ℝ) ∧ min d (QRH.SourceCertificate.H:ℝ)-b.1 < gap ∧ m ≤ b.2 ∧ b.2-m < gap)
    (hτD : G0.τ*(P.degreeBound:ℝ) ≤ heightLoss) :
    ∃ezmax : ℝ,∃hmax : 0 < ezmax,
    ∃D : DetectorBank Slot M A buffer price dmin dmax y (loss/10) cell table dBank (shrinkEz G0 ezmax hmax),
      Nonempty (LateBundle P (shrinkEz G0 ezmax hmax) m0 gap V) := by
  obtain ⟨ezmax,hmax,⟨D⟩⟩ := genuine_detector_schedule (Slot:=Slot) A table G0 hβ hbuffer hprice hgap hdmin hdb hdsupply hcost hdetector
  exact ⟨ezmax,hmax,D,genuine_late_bundle P (shrinkEz G0 ezmax hmax) m0 gap V hV hes hbank hnet hτD⟩

/-- The genuine common constructor chooses the source errors and one
positive height exponent from the retained finite degree, lowers the collar
using the actual detector, and then fixes all late source/profile packets. -/
theorem genuine_common_late_metadata
    (P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B)
    (m0 gap : ℝ) (V : ℝ→ℂ) (hV : ContDiff ℝ ∞ V)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hbuffer : 0 < buffer) (hprice : 0 < price)
    (hgap : (1/50:ℝ)+price < (cell.threshold:ℝ)) (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax)
    (hdb : ∀d∈dBank,dmin ≤ d ∧ d ≤ dmax)
    (margin reserve : ℝ) (Mcap : dBank → ℝ) (hmargin : 0 < margin)
    (hreserve : 0 < reserve) (hheightLoss : 0 < heightLoss)
    (hdsupply : ∀d : dBank,Mcap d+margin ≤ d.val)
    (hes : 0 ≤ εsource)
    (hbank : ∀b∈ordinaryBank,(98/100:ℝ) ≤ b.1 ∧ b.1 ≤ (QRH.SourceCertificate.H:ℝ) ∧ m0 ≤ b.2 ∧ b.2 ≤ 51/100 ∧
      0 < dec b ∧ dec b ≤ gap ∧ 0 < nearOrdinaryQuota n b.2 b.1-dec b)
    (hnet : ∀d m : ℝ,(98/100:ℝ) ≤ d → m0 ≤ m → m ≤ 51/100 →
      ∃b∈ordinaryBank,b.1 ≤ min d (QRH.SourceCertificate.H:ℝ) ∧ min d (QRH.SourceCertificate.H:ℝ)-b.1 < gap ∧ m ≤ b.2 ∧ b.2-m < gap) :
    ∃G : LateGeometry dmin dmax dBank,
      G.Mcap=Mcap ∧ G.Bmask=0 ∧ G.margin=margin ∧ G.R=22 ∧
      G.τ ≤ 1/4 ∧ G.τ*(P.degreeBound:ℝ) ≤ heightLoss ∧ G.τ*(P.degreeBound:ℝ) ≤ reserve ∧
      G.ε ≤ 1/7500 ∧ (dmax+1)*G.ε ≤ B.feeFloor/1000 ∧
      G.heightCost ≤ 1 ∧ 12*G.ez*(22+2)+8*G.κ+2*G.heightCost ≤ G.ε/2 ∧
      (dmax+1)*G.ε ≤ reserve/1000 ∧
      ∃D : DetectorBank Slot M A buffer price dmin dmax y (loss/10) cell table dBank G,
        Nonempty (LateBundle P G m0 gap V) := by
  obtain ⟨G0,hM,hB,hm,hR,hτsmall,hτD,hτreserve,hεtiny,hεfee,hcost,hdet,hεreserve⟩ :=
    choose_late_geometry P.degreeBound dmin dmax 22 B.feeFloor heightLoss reserve margin Mcap
      hdmin hdmax (by norm_num) B.feeFloor_pos hheightLoss hreserve hmargin
  have hsupply : ∀d : dBank,G0.Mcap d+G0.Bmask+G0.margin ≤ d.val := by
    intro d
    rw [hM,hB,hm,add_zero]
    exact hdsupply d
  obtain ⟨ezmax,hmax,D,hL⟩ := genuine_terminal_metadata P G0 m0 gap V hV hβ hbuffer hprice hgap hdmin hdb
    hsupply hcost hdet hes hbank hnet hτD
  let G := shrinkEz G0 ezmax hmax
  have hdet' : 12*G.ez*(22+2)+8*G.κ+2*G.heightCost ≤ G.ε/2 := by
    have he : G.ez ≤ G0.ez := min_le_left _ _
    change 12*G.ez*(22+2)+8*G0.κ+2*G0.heightCost ≤ G0.ε/2
    nlinarith only [he,hdet]
  exact ⟨G,hM,hB,hm,hR,hτsmall,hτD,hτreserve,hεtiny,hεfee,hcost,hdet',hεreserve,D,hL⟩

/-- There is ONE U threshold before all live profiles, cofactor radii,
original rows, detector tickets, response windows and native indices. Its
fields are actual source calls and the same actual descriptor cover. -/
theorem terminal_common_event
    (P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B)
    (G : LateGeometry dmin dmax dBank) (m0 gap : ℝ) (V : ℝ→ℂ)
    (L : LateBundle P G m0 gap V)
    (D : DetectorBank Slot M A buffer price dmin dmax y (loss/10) cell table dBank G)
    (hbuffer : 0 < buffer) (Cslot : ℝ)
    (hCslot : max L.CslotFloor D.paymentFloor ≤ Cslot) :
    ∃CLo : ℝ,0 < CLo ∧ ∀ᶠ U : ℝ in atTop,
      AtAll P G L.Bshort m0 gap L.sources D.indexBound Cslot CLo U ∧
      ∀(T : Finset Slot) (d : dBank),
        DetectorAt T M A buffer price dmin dmax y (loss/10) cell table dBank G d (D T d).I Cslot U := by
  have hCslot0 : 0 < Cslot := L.CslotFloor_pos.trans_le ((le_max_left _ _).trans hCslot)
  obtain ⟨CLo,hCLo,hsource⟩ := common_source_event P G L.Bshort m0 gap L.sources hbuffer D.indexBound Cslot hCslot0
  refine ⟨CLo,hCLo,?_⟩
  filter_upwards [hsource,D.common_event Cslot ((le_max_right _ _).trans hCslot)] with U hsource hdetector
  exact ⟨hsource,hdetector⟩

#print axioms genuine_terminal_metadata
#print axioms genuine_common_late_metadata
#print axioms terminal_common_event
#print axioms DetectorBank.common_event
end
end QRH.Cycle092.P2CommonSourceMetadata
