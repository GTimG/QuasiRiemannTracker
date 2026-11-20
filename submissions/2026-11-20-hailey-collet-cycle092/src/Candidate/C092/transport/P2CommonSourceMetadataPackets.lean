/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact metadata and late functions of the genuine original P2 suppliers. -/
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
local instance c092LocalInst_Candidate_C092_transport_P2CommonSourceMetadataPackets_fef3eba00a673aaa_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

structure SmallPacket (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M) (n y mesh : ℝ) where
  degree : ℕ
  controls : Finset (ℕ×ℕ)
  C : ℝ
  positive : 0 < C
  late : SmallPhysical Slot M A n y mesh degree controls C

structure LowHighPacket (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M) (n y e Vmax mesh buffer : ℝ) where
  degree : ℕ
  controls : Finset (ℕ×ℕ)
  late : LowHighPhysical Slot M A n y e Vmax mesh buffer degree controls

structure OrdinaryPacket (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n y dmin εsource mesh : ℝ) (bank : Finset (ℝ×ℝ)) (dec : (ℝ×ℝ)→ℝ) where
  degree : Finset Slot→ℕ
  controls : Finset Slot→Finset (ℕ×ℕ)
  Csource : Finset Slot→ℝ
  J : Finset Slot→ℕ
  Crow : Finset Slot→ℝ
  positive : ∀T,0 < Csource T ∧ 0 < Crow T
  D : ℕ
  S : Finset (ℕ×ℕ)
  bounds : ∀T,degree T+2*J T+1 ≤ D ∧ controls T⊆S
  physical : ∀T : Finset Slot,TerminalOrdinaryNormalizedPhysical T M A.Hr A.hHr A.W A.bΦ
    A.ηLong A.baseLong A.ηShort A.baseShort A.QLong A.QShort
    n y dmin εsource mesh bank dec (degree T) (controls T) (Csource T) (J T) (Crow T)

/-- A genuine marked supplier is consumed once; the same early matrices
and exact late analytic function are retained together in one packet. -/
theorem marked_packet_of_physical
    (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n y e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (ρ : Contract.AnchorRect) (εm nativeError N quota dmin dmax price im nm buffer : ℝ)
    (hb : 0 < buffer)
    (hphysical : TerminalActualClassMarkedPhysical n y e0 nu0 loss heightLoss c step δ fee
      ρ εm nativeError N quota dmin dmax price im nm) :
    Nonempty (MarkedPacket Slot M A n y e0 nu0 loss heightLoss c step δ fee
      ρ εm nativeError N quota dmin dmax price im nm buffer) := by
  obtain ⟨Fb,hFb,hpacket⟩ := hphysical Slot M A.Hr A.hHr A.W A.hWs A.hW A.ηShort A.baseShort A.ηLong A.baseLong
    A.QLong A.hQLM A.hQL0 A.hQLt A.hQL72 A.bΦ A.hbΦ A.hΦ
  obtain ⟨Jc,Cc,degree,controls,Cl,D,hD,hpos,hlate⟩ := hpacket buffer hb
  exact ⟨⟨Fb,hFb,Jc,Cc,degree,controls,Cl,D,hD,hpos,hlate⟩⟩

/-- The true unmarked/top-face constructor is kept with its own metadata. -/
theorem unmarked_packet_of_physical
    (Slot : Type) [Fintype Slot] (M : Ideal O) [NeZero M] (A : Arithmetic M)
    (n y e0 nu0 loss heightLoss : ℝ) (c : Cutoff) (step δ fee : ℝ)
    (εm nativeError N quota dmin dmax price nm buffer : ℝ) (hb : 0 < buffer)
    (hphysical : TerminalActualClassUnmarkedPhysical n y e0 nu0 loss heightLoss c step δ fee
      εm nativeError N quota dmin dmax price nm) :
    Nonempty (UnmarkedPacket Slot M A n y e0 nu0 loss heightLoss c step δ fee
      εm nativeError N quota dmin dmax price nm buffer) := by
  obtain ⟨Fb,hFb,hpacket⟩ := hphysical Slot M A.Hr A.hHr A.W A.hWs A.hW A.ηShort A.baseShort A.ηLong A.baseLong
    A.QLong A.hQLM A.hQL0 A.hQLt A.hQL72 A.bΦ A.hbΦ A.hΦ
  obtain ⟨Jc,Cc,degree,controls,Cl,D,hD,hpos,hlate⟩ := hpacket buffer hb
  exact ⟨⟨Fb,hFb,Jc,Cc,degree,controls,Cl,D,hD,hpos,hlate⟩⟩

/-- The small branch is obtained from the genuine global .75 ceiling,
retaining its original old-anchor keep and separate internal calibration. -/
theorem small_packets {n y : ℝ} (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y) :
    ∃mesh : ℝ,0 < mesh ∧ ∀(Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∀(M : Ideal O) [NeZero M] (A : Arithmetic M),Nonempty (SmallPacket Slot M A n y mesh) := by
  obtain ⟨mesh,hm,hs⟩ := terminal_actual_small_radii hβ hy0 hy1 hyn hn
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _ M _ A
  obtain ⟨buffer,hbuffer,hs⟩ := hs Slot
  obtain ⟨degree,controls,C,hC,hlate⟩ := hs M A.Hr A.hHr A.W A.hW A.hWs A.bΦ A.hbΦ A.hΦ
    A.old A.base A.ηLong A.ηShort A.baseLong A.baseShort A.Qold A.QLong A.QShort
    A.hQoldM A.hQoldBase A.hQLM A.hQL0 A.hQLt A.hQL72 A.hQSM A.hQS0 A.hQSt A.hQS72
  exact ⟨⟨degree,controls,C,hC,hlate⟩⟩

theorem low_high_packets {n y e Vmax : ℝ} (hVmax : 1 ≤ Vmax)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y)
    (he0 : 0 ≤ e) (he1 : e ≤ (responseUpper:ℝ))
    (hp : e*max 0 (lowBracketAt y) < (u-rho:ℚ)) :
    ∃mesh : ℝ,0 < mesh ∧ ∀(Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∃bufferMax : ℝ,0 < bufferMax ∧ ∀buffer : ℝ,0 < buffer → buffer ≤ bufferMax →
    ∀(M : Ideal O) [NeZero M] (A : Arithmetic M),
      Nonempty (LowHighPacket Slot M A n y e Vmax mesh buffer) := by
  obtain ⟨mesh,hm,hs⟩ := terminal_low_high_selected (by linarith) hVmax hβ cover hy0 hy1 hyn hn he0 he1 hp
  refine ⟨mesh,hm,?_⟩
  intro Slot _ _
  obtain ⟨bufferMax,hbMax,hs⟩ := hs Slot
  refine ⟨bufferMax,hbMax,?_⟩
  intro buffer hb hbSmall M _ A
  obtain ⟨degree,controls,hlate⟩ := hs buffer hb hbSmall M A.Hr A.hHr A.W A.hW A.hWs A.bΦ A.hbΦ A.hΦ
    A.ηLong A.ηShort A.baseLong A.baseShort A.QLong A.QShort
    A.hQLM A.hQL0 A.hQLt A.hQL72 A.hQSM A.hQS0 A.hQSt A.hQS72 A.old A.base
  exact ⟨⟨degree,controls,hlate⟩⟩

/-- The ordinary factory calls the established earlier-cover source and
keeps the actual all-subset functions, without an input PairAt bound. -/
theorem ordinary_packets (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    {n y m0 gap εsource dmin : ℝ} (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y)
    (hm0 : y/(QRH.SourceCertificate.H:ℝ) ≤ m0) (hm01 : m0 ≤ 51/100)
    (hgap : 0 < gap) (hes : 0 < εsource) (hdmin : 0 < dmin) :
    ∃bank : Finset (ℝ×ℝ),∃dec : (ℝ×ℝ)→ℝ,∃mesh : ℝ,0 < mesh ∧
      (∀B∈bank,(98/100:ℝ) ≤ B.1 ∧ B.1 ≤ (QRH.SourceCertificate.H:ℝ) ∧ m0 ≤ B.2 ∧ B.2 ≤ 51/100 ∧
        0 < dec B ∧ dec B ≤ gap ∧ 0 < nearOrdinaryQuota n B.2 B.1-dec B) ∧
      (∀d m : ℝ,(98/100:ℝ) ≤ d → m0 ≤ m → m ≤ 51/100 →
        ∃B∈bank,B.1 ≤ min d (QRH.SourceCertificate.H:ℝ) ∧ min d (QRH.SourceCertificate.H:ℝ)-B.1 < gap ∧
          m ≤ B.2 ∧ B.2-m < gap) ∧
    ∀(Slot : Type) [Fintype Slot] [DecidableEq Slot],∀(M : Ideal O) [NeZero M] (A : Arithmetic M),
      Nonempty (OrdinaryPacket Slot M A n y dmin εsource mesh bank dec) := by
  obtain ⟨bank,dec,mesh,hm,hbank,hnet,hs⟩ := terminal_ordinary_normalized_bank hβ cover hy0 hy1 hyn hn hm0 hm01 hgap hes hdmin
  refine ⟨bank,dec,mesh,hm,hbank,hnet,?_⟩
  intro Slot _ _ M _ A
  obtain ⟨degree,controls,Csource,J,Crow,hpos,D,S,hbounds,hphysical⟩ := hs Slot M A.Hr A.hHr A.W A.hW A.hWs A.bΦ A.hbΦ A.hΦ
    A.ηLong A.baseLong A.ηShort A.baseShort A.QLong A.QShort
    A.hQLM A.hQL0 A.hQLt A.hQL72 A.hQSM A.hQS0 A.hQSt A.hQS72
  exact ⟨⟨degree,controls,Csource,J,Crow,hpos,D,S,hbounds,hphysical⟩⟩

#print axioms marked_packet_of_physical
#print axioms unmarked_packet_of_physical
#print axioms small_packets
#print axioms low_high_packets
#print axioms ordinary_packets
end
end QRH.Cycle092.P2CommonSourceMetadata
