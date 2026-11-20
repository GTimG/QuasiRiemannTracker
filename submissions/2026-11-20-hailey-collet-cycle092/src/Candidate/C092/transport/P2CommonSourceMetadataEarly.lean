/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact metadata and late functions of the genuine original P2 suppliers. -/
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
local instance c092LocalInst_Candidate_C092_transport_P2CommonSourceMetadataEarly_f266219303c56409_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}

structure EarlyPackets (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (e Vmax smallMesh lowMesh ordinaryMesh εsource buffer : ℝ)
    (ordinaryBank : Finset (ℝ×ℝ)) (dec : (ℝ×ℝ)→ℝ)
    (B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError) where
  small : SmallPacket Slot M A n y smallMesh
  lowHigh : LowHighPacket Slot M A n y e Vmax lowMesh buffer
  ordinary : OrdinaryPacket Slot M A n y dmin εsource ordinaryMesh ordinaryBank dec
  inverse : InversePackets Slot M A buffer B

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {e Vmax smallMesh lowMesh ordinaryMesh εsource buffer : ℝ}
variable {ordinaryBank : Finset (ℝ×ℝ)} {dec : (ℝ×ℝ)→ℝ}
variable {B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError}

namespace EarlyPackets

def degreeBound (P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B) : ℕ :=
  P.small.degree+P.lowHigh.degree+P.ordinary.D+P.inverse.degreeBound

def controlsBound (P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B) : Finset (ℕ×ℕ) :=
  insert (0,0) (P.small.controls ∪ P.lowHigh.controls ∪ P.ordinary.S ∪ P.inverse.controlsBound)

theorem degree_bounds (P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B) :
    P.small.degree ≤ P.degreeBound ∧ P.lowHigh.degree ≤ P.degreeBound ∧
    (∀T,P.ordinary.degree T+2*P.ordinary.J T+1 ≤ P.degreeBound) ∧
    (∀T d k j ki kl,(P.inverse.marked T d k j).Jc ki kl+(P.inverse.marked T d k j).degree ki kl+1 ≤ P.degreeBound) ∧
    (∀T d k kl,(P.inverse.unmarked T d k).Jc kl+(P.inverse.unmarked T d k).degree kl+1 ≤ P.degreeBound) := by
  have hs : P.small.degree ≤ P.degreeBound := by unfold degreeBound;omega
  have hl : P.lowHigh.degree ≤ P.degreeBound := by unfold degreeBound;omega
  have ho : P.ordinary.D ≤ P.degreeBound := by unfold degreeBound;omega
  have hi : P.inverse.degreeBound ≤ P.degreeBound := by unfold degreeBound;omega
  exact ⟨hs,hl,(fun T=>((P.ordinary.bounds T).1).trans ho),
    (fun T d k j ki kl=>(P.inverse.marked_degree_le T d k j ki kl).trans hi),
    (fun T d k kl=>(P.inverse.unmarked_degree_le T d k kl).trans hi)⟩

theorem controls_bounds (P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B) :
    (0,0)∈P.controlsBound ∧ P.small.controls⊆P.controlsBound ∧ P.lowHigh.controls⊆P.controlsBound ∧
    (∀T,P.ordinary.controls T⊆P.controlsBound) ∧
    (∀T d k j ki kl,(P.inverse.marked T d k j).controls ki kl⊆P.controlsBound) ∧
    (∀T d k kl,(P.inverse.unmarked T d k).controls kl⊆P.controlsBound) := by
  have hs : P.small.controls⊆P.controlsBound := by intro a ha; simp [controlsBound,ha]
  have hl : P.lowHigh.controls⊆P.controlsBound := by intro a ha; simp [controlsBound,ha]
  have ho : P.ordinary.S⊆P.controlsBound := by intro a ha; simp [controlsBound,ha]
  have hi : P.inverse.controlsBound⊆P.controlsBound := by intro a ha; simp [controlsBound,ha]
  exact ⟨Finset.mem_insert_self _ _,hs,hl,(fun T=>(P.ordinary.bounds T).2.trans ho),
    (fun T d k j ki kl=>(P.inverse.marked_controls_le T d k j ki kl).trans hi),
    (fun T d k kl=>(P.inverse.unmarked_controls_le T d k kl).trans hi)⟩

end EarlyPackets

/-- One external buffer pays every surviving subset and is chosen before
its polynomial metadata or the later response-payment constant. -/
theorem common_buffer (N : ℕ) (bufferMax feeFloor reserve : ℝ)
    (hb : 0 < bufferMax) (hf : 0 < feeFloor) (hr : 0 < reserve) :
    ∃buffer : ℝ,0 < buffer ∧ buffer ≤ bufferMax ∧
      buffer*(N:ℝ) ≤ feeFloor/1000 ∧ buffer*(N:ℝ) ≤ reserve/1000 := by
  let buffer := min bufferMax (min (feeFloor/(1000*((N:ℝ)+1))) (reserve/(1000*((N:ℝ)+1))))
  have hden : 0 < 1000*((N:ℝ)+1) := by positivity
  have hbuf : 0 < buffer := lt_min hb (lt_min (div_pos hf hden) (div_pos hr hden))
  have hf' := (le_div_iff₀ hden).mp ((min_le_right _ _).trans (min_le_left _ _):buffer ≤ feeFloor/(1000*((N:ℝ)+1)))
  have hr' := (le_div_iff₀ hden).mp ((min_le_right _ _).trans (min_le_right _ _):buffer ≤ reserve/(1000*((N:ℝ)+1)))
  refine ⟨buffer,hbuf,min_le_left _ _,?_,?_⟩ <;> nlinarith only [hf',hr',hbuf]

/-- The common collection invokes every genuine branch factory. No branch
energy is a hypothesis: all late functions are returned in EarlyPackets. -/
theorem genuine_common_early_packets
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y loss heightLoss dmin dmax price m0 gap εsource Vmax : ℝ} {cell : Cell}
    (table : TerminalResponseTable y (loss/10) cell) (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y)
    (ht : 0 ≤ (cell.threshold:ℝ)) (ht' : (cell.threshold:ℝ) ≤ (responseUpper:ℝ))
    (hlow : (cell.threshold:ℝ)*max 0 (lowBracketAt y) < (u-rho:ℚ))
    (hloss : 0 < loss) (hheightLoss : 0 ≤ heightLoss) (hVmax : 1 ≤ Vmax)
    (hm0 : y/(QRH.SourceCertificate.H:ℝ) ≤ m0) (hm01 : m0 ≤ 51/100)
    (hgap : 0 < gap) (hes : 0 < εsource) (hdmin : 0 < dmin) (hdmax : dmin ≤ dmax)
    (dBank : Finset ℝ) (hdb : ∀d∈dBank,(98/100:ℝ) ≤ d ∧ dmin ≤ d ∧ d ≤ dmax)
    (hprice0 : 0 ≤ price) (hpriceBudget : price*dmax ≤ loss/4) :
    ∃εm nativeError : ℝ,∃B : TableBank (n:=n) (heightLoss:=heightLoss)
      (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError,
    ∃ms ml mo : ℝ,0 < ms ∧ 0 < ml ∧ 0 < mo ∧
    ∃bank : Finset (ℝ×ℝ),∃dec : (ℝ×ℝ)→ℝ,
      (∀b∈bank,(98/100:ℝ) ≤ b.1 ∧ b.1 ≤ (QRH.SourceCertificate.H:ℝ) ∧ m0 ≤ b.2 ∧ b.2 ≤ 51/100 ∧
        0 < dec b ∧ dec b ≤ gap ∧ 0 < nearOrdinaryQuota n b.2 b.1-dec b) ∧
      (∀d m : ℝ,(98/100:ℝ) ≤ d → m0 ≤ m → m ≤ 51/100 →
        ∃b∈bank,b.1 ≤ min d (QRH.SourceCertificate.H:ℝ) ∧ min d (QRH.SourceCertificate.H:ℝ)-b.1 < gap ∧
          m ≤ b.2 ∧ b.2-m < gap) ∧
    ∃mesh : ℝ,0 < mesh ∧ mesh ≤ ms ∧ mesh ≤ ml ∧ mesh ≤ mo ∧ mesh ≤ dmin*B.mesh ∧
    ∀(Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∃buffer : ℝ,0 < buffer ∧ buffer*(Fintype.card Slot:ℝ) ≤ B.feeFloor/1000 ∧
      buffer*(Fintype.card Slot:ℝ) ≤ (rho:ℝ)/1000 ∧
    ∀(M : Ideal O) [NeZero M] (A : Arithmetic M),
      Nonempty (EarlyPackets Slot M A (cell.threshold:ℝ) Vmax ms ml mo εsource buffer bank dec B) := by
  obtain ⟨εm,nativeError,⟨B⟩⟩ := genuine_table_bank hβ table hy0 hy1 hyn hn ht hloss hheightLoss hdmin hdmax dBank hdb hprice0 hpriceBudget
  obtain ⟨ms,hms,hs⟩ := small_packets hβ hy0 hy1 hyn hn
  obtain ⟨ml,hml,hl⟩ := low_high_packets hVmax hβ cover hy0 hy1 hyn hn ht ht' hlow
  obtain ⟨bank,dec,mo,hmo,hbank,hnet,ho⟩ := ordinary_packets hβ cover hy0 hy1 hyn hn hm0 hm01 hgap hes hdmin
  let mesh := min ms (min ml (min mo (dmin*B.mesh)))
  have hmesh : 0 < mesh := lt_min hms (lt_min hml (lt_min hmo (mul_pos hdmin B.mesh_pos)))
  refine ⟨εm,nativeError,B,ms,ml,mo,hms,hml,hmo,bank,dec,hbank,hnet,mesh,hmesh,
    min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)),?_⟩
  intro Slot _ _
  obtain ⟨bufferMax,hbMax,hl⟩ := hl Slot
  obtain ⟨buffer,hbuffer,hbMax',hfee,hrho⟩ := common_buffer (Fintype.card Slot) bufferMax B.feeFloor (rho:ℝ)
    hbMax B.feeFloor_pos (by norm_num [rho])
  refine ⟨buffer,hbuffer,hfee,hrho,?_⟩
  intro M _ A
  exact ⟨⟨Classical.choice (hs Slot M A),Classical.choice (hl buffer hbuffer hbMax' M A),
    Classical.choice (ho Slot M A),inverse_packets Slot M A buffer hbuffer B⟩⟩

#print axioms common_buffer
#print axioms genuine_common_early_packets
#print axioms EarlyPackets.degree_bounds
#print axioms EarlyPackets.controls_bounds
end
end QRH.Cycle092.P2CommonSourceMetadata
