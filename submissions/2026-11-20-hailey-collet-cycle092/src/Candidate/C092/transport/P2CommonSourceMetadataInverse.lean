/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact metadata and late functions of the genuine original P2 suppliers. -/
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
local instance c092LocalInst_Candidate_C092_transport_P2CommonSourceMetadataInverse_3d6971400ac8230b_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}

structure InversePackets (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M) (buffer : ℝ)
    (B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError) where
  marked : ∀(T : Finset Slot) (d : dBank) (k : WindowKey table) (j : Fin B.J),
    MarkedPacket T M A n y (table.egrid k.1) (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss
      (table.cutoff k) (loss/10) (loss/10) (B.feeM k) (B.rhoBank j) εm nativeError
      (terminalNativeCap n d.val) (B.quota k d) dmin dmax price (B.im k d j) (B.nm k d j) buffer
  unmarked : ∀(T : Finset Slot) (d : dBank) (k : WindowKey table),
    UnmarkedPacket T M A n y (table.egrid k.1) (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss
      (table.cutoff k) (loss/10) (loss/10) (B.feeU k) εm nativeError
      (terminalNativeCap n d.val) (B.quota k d) dmin dmax price (B.nu k d) buffer

/-- Every family member calls the actual analytic constructor. There is no
per-row bound or source moment assumed by this finite collection. -/
noncomputable def inverse_packets (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (M : Ideal O) [NeZero M] (A : Arithmetic M) (buffer : ℝ) (hb : 0 < buffer)
    (B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError) :
    InversePackets Slot M A buffer B where
  marked := fun T d k j => Classical.choice (marked_packet_of_physical T M A
    n y (table.egrid k.1) (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss
    (table.cutoff k) (loss/10) (loss/10) (B.feeM k) (B.rhoBank j) εm nativeError
    (terminalNativeCap n d.val) (B.quota k d) dmin dmax price (B.im k d j) (B.nm k d j) buffer hb (B.marked k d j))
  unmarked := fun T d k => Classical.choice (unmarked_packet_of_physical T M A
    n y (table.egrid k.1) (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss
    (table.cutoff k) (loss/10) (loss/10) (B.feeU k) εm nativeError
    (terminalNativeCap n d.val) (B.quota k d) dmin dmax price (B.nu k d) buffer hb (B.unmarked k d))

variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M} {buffer : ℝ}
variable {B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError}

abbrev MarkedIndex (Slot : Type) [Fintype Slot] (dBank : Finset ℝ) (Key : Type) (J : ℕ) :=
  Finset Slot × dBank × Key × Fin J
abbrev UnmarkedIndex (Slot : Type) [Fintype Slot] (dBank : Finset ℝ) (Key : Type) :=
  Finset Slot × dBank × Key

namespace InversePackets

def degreeBound (P : InversePackets Slot M A buffer B) : ℕ :=
  Finset.univ.sup (fun p : MarkedIndex Slot dBank (WindowKey table) B.J => (P.marked p.1 p.2.1 p.2.2.1 p.2.2.2).D)+
  Finset.univ.sup (fun p : UnmarkedIndex Slot dBank (WindowKey table) => (P.unmarked p.1 p.2.1 p.2.2).D)

def controlsBound (P : InversePackets Slot M A buffer B) : Finset (ℕ×ℕ) :=
  (Finset.univ.biUnion fun p : MarkedIndex Slot dBank (WindowKey table) B.J =>
    Finset.univ.biUnion fun ki : Fin (nativeK buffer dmax+1) =>
    Finset.univ.biUnion fun kl : Fin (nativeK buffer dmax+1) => (P.marked p.1 p.2.1 p.2.2.1 p.2.2.2).controls ki kl) ∪
  (Finset.univ.biUnion fun p : UnmarkedIndex Slot dBank (WindowKey table) =>
    Finset.univ.biUnion fun kl : Fin (nativeK buffer dmax+1) => (P.unmarked p.1 p.2.1 p.2.2).controls kl)

theorem marked_degree_le (P : InversePackets Slot M A buffer B)
    (T : Finset Slot) (d : dBank) (k : WindowKey table) (j : Fin B.J) (ki kl : Fin (nativeK buffer dmax+1)) :
    (P.marked T d k j).Jc ki kl+(P.marked T d k j).degree ki kl+1 ≤ P.degreeBound := by
  have h := (P.marked T d k j).hD ki kl
  have hs := Finset.le_sup (f:=fun p : MarkedIndex Slot dBank (WindowKey table) B.J => (P.marked p.1 p.2.1 p.2.2.1 p.2.2.2).D)
    (Finset.mem_univ (T,d,k,j))
  exact h.trans (hs.trans (Nat.le_add_right _ _))

theorem unmarked_degree_le (P : InversePackets Slot M A buffer B)
    (T : Finset Slot) (d : dBank) (k : WindowKey table) (kl : Fin (nativeK buffer dmax+1)) :
    (P.unmarked T d k).Jc kl+(P.unmarked T d k).degree kl+1 ≤ P.degreeBound := by
  have h := (P.unmarked T d k).hD kl
  have hs := Finset.le_sup (f:=fun p : UnmarkedIndex Slot dBank (WindowKey table) => (P.unmarked p.1 p.2.1 p.2.2).D)
    (Finset.mem_univ (T,d,k))
  exact h.trans (hs.trans (Nat.le_add_left _ _))

theorem marked_controls_le (P : InversePackets Slot M A buffer B)
    (T : Finset Slot) (d : dBank) (k : WindowKey table) (j : Fin B.J) (ki kl : Fin (nativeK buffer dmax+1)) :
    (P.marked T d k j).controls ki kl ⊆ P.controlsBound := by
  intro a ha
  apply Finset.mem_union_left
  exact Finset.mem_biUnion.mpr ⟨(T,d,k,j),Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨ki,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨kl,Finset.mem_univ _,ha⟩⟩⟩

theorem unmarked_controls_le (P : InversePackets Slot M A buffer B)
    (T : Finset Slot) (d : dBank) (k : WindowKey table) (kl : Fin (nativeK buffer dmax+1)) :
    (P.unmarked T d k).controls kl ⊆ P.controlsBound := by
  intro a ha
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨(T,d,k),Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨kl,Finset.mem_univ _,ha⟩⟩

end InversePackets
#print axioms inverse_packets
#print axioms InversePackets.marked_degree_le
#print axioms InversePackets.marked_controls_le
end
end QRH.Cycle092.P2CommonSourceMetadata
