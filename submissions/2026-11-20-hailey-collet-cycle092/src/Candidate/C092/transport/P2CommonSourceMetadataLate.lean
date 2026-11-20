/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact metadata and late functions of the genuine original P2 suppliers. -/
import Candidate.C092.transport.P2CommonSourceMetadataSchedule
import Candidate.C092.transport.P2CommonSourceMetadataReady
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
local instance c092LocalInst_Candidate_C092_transport_P2CommonSourceMetadataLate_82c58b3541f7ce70_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

variable {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {e Vmax smallMesh lowMesh ordinaryMesh εsource buffer : ℝ}
variable {ordinaryBank : Finset (ℝ×ℝ)} {dec : (ℝ×ℝ) → ℝ}
variable {B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError}

structure LatePackets (P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B)
    (G : LateGeometry dmin dmax dBank) (Bshort m0 gap : ℝ) where
  ordinary : ∀(T : Finset Slot) (d : dBank),ReadyOrdinary Slot M A n y dmin dmax εsource ordinaryMesh ordinaryBank dec
    P.ordinary T dBank G d m0 gap
  marked : ∀(T : Finset Slot) (d : dBank) (k : WindowKey table) (j : Fin B.J),
    ReadyMarked T M A n y (table.egrid k.1) (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss
      (table.cutoff k) (loss/10) (loss/10) (B.feeM k) (B.rhoBank j) εm nativeError
      (terminalNativeCap n d.val) (B.quota k d) dmin dmax price (B.im k d j) (B.nm k d j) buffer
      (P.inverse.marked T d k j) dBank G d Bshort
  unmarked : ∀(T : Finset Slot) (d : dBank) (k : WindowKey table),
    ReadyUnmarked T M A n y (table.egrid k.1) (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss
      (table.cutoff k) (loss/10) (loss/10) (B.feeU k) εm nativeError
      (terminalNativeCap n d.val) (B.quota k d) dmin dmax price (B.nu k d) buffer
      (P.inverse.unmarked T d k) dBank G d Bshort

/-- Each finite late supplier is invoked once with its retained early
matrices. Ordinary uses the authentic internal slot and radius selection. -/
noncomputable def late_packets
    (P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B)
    (G : LateGeometry dmin dmax dBank) (Bshort m0 gap : ℝ)
    (hBshort : 0 ≤ Bshort) (hes : 0 ≤ εsource)
    (hbank : ∀b∈ordinaryBank,(98/100:ℝ) ≤ b.1 ∧ b.1 ≤ (QRH.SourceCertificate.H:ℝ) ∧ m0 ≤ b.2 ∧ b.2 ≤ 51/100 ∧
      0 < dec b ∧ dec b ≤ gap ∧ 0 < nearOrdinaryQuota n b.2 b.1-dec b)
    (hnet : ∀d m : ℝ,(98/100:ℝ) ≤ d → m0 ≤ m → m ≤ 51/100 →
      ∃b∈ordinaryBank,b.1 ≤ min d (QRH.SourceCertificate.H:ℝ) ∧ min d (QRH.SourceCertificate.H:ℝ)-b.1 < gap ∧ m ≤ b.2 ∧ b.2-m < gap)
    (hτD : G.τ*(P.degreeBound:ℝ) ≤ heightLoss) : LatePackets P G Bshort m0 gap := by
  have hMD (T : Finset Slot) (d : dBank) (k : WindowKey table) (j : Fin B.J) :
      (P.inverse.marked T d k j).D ≤ P.degreeBound := by
    have h := Finset.le_sup (f:=fun p : MarkedIndex Slot dBank (WindowKey table) B.J => (P.inverse.marked p.1 p.2.1 p.2.2.1 p.2.2.2).D)
      (Finset.mem_univ (T,d,k,j))
    dsimp only at h
    unfold EarlyPackets.degreeBound InversePackets.degreeBound
    omega
  have hUD (T : Finset Slot) (d : dBank) (k : WindowKey table) :
      (P.inverse.unmarked T d k).D ≤ P.degreeBound := by
    have h := Finset.le_sup (f:=fun p : UnmarkedIndex Slot dBank (WindowKey table) => (P.inverse.unmarked p.1 p.2.1 p.2.2).D)
      (Finset.mem_univ (T,d,k))
    dsimp only at h
    unfold EarlyPackets.degreeBound InversePackets.degreeBound
    omega
  exact {
    ordinary := fun T d => Classical.choice (ready_ordinary Slot M A n y dmin dmax εsource ordinaryMesh ordinaryBank dec
      P.ordinary T dBank G d m0 gap hes hbank hnet)
    marked := fun T d k j => Classical.choice (ready_marked T M A n y (table.egrid k.1) (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss
      (table.cutoff k) (loss/10) (loss/10) (B.feeM k) (B.rhoBank j) εm nativeError
      (terminalNativeCap n d.val) (B.quota k d) dmin dmax price (B.im k d j) (B.nm k d j) buffer
      (P.inverse.marked T d k j) dBank G d Bshort hBshort
      ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hMD T d k j)) G.hτ.le).trans hτD))
    unmarked := fun T d k => Classical.choice (ready_unmarked T M A n y (table.egrid k.1) (max (table.egrid k.1) (table.νgrid k.2)) loss heightLoss
      (table.cutoff k) (loss/10) (loss/10) (B.feeU k) εm nativeError
      (terminalNativeCap n d.val) (B.quota k d) dmin dmax price (B.nu k d) buffer
      (P.inverse.unmarked T d k) dBank G d Bshort hBshort
      ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hUD T d k)) G.hτ.le).trans hτD)) }

namespace LatePackets
variable {P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B}
variable {G : LateGeometry dmin dmax dBank} {Bshort m0 gap : ℝ}

def orders (L : LatePackets P G Bshort m0 gap) : Finset ℕ :=
  insert 2 (
    (Finset.univ.biUnion fun p : MarkedIndex Slot dBank (WindowKey table) B.J =>
      Finset.univ.biUnion fun ki : Fin (nativeK buffer dmax+1) =>
      Finset.univ.image fun kl : Fin (nativeK buffer dmax+1) => (L.marked p.1 p.2.1 p.2.2.1 p.2.2.2).order ki kl+2) ∪
    (Finset.univ.biUnion fun p : UnmarkedIndex Slot dBank (WindowKey table) =>
      Finset.univ.image fun kl : Fin (nativeK buffer dmax+1) => (L.unmarked p.1 p.2.1 p.2.2).order kl+2) ∪
    (Finset.univ.image fun p : Finset Slot×dBank => (L.ordinary p.1 p.2).order+2))

def ordinaryControls (L : LatePackets P G Bshort m0 gap) : Finset (ℕ×ℕ) :=
  Finset.univ.biUnion fun p : Finset Slot×dBank => (L.ordinary p.1 p.2).S

theorem orders_two (L : LatePackets P G Bshort m0 gap) : 2∈L.orders := Finset.mem_insert_self _ _

theorem marked_order (L : LatePackets P G Bshort m0 gap)
    (T : Finset Slot) (d : dBank) (k : WindowKey table) (j : Fin B.J) (ki kl : Fin (nativeK buffer dmax+1)) :
    (L.marked T d k j).order ki kl+2∈L.orders := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  exact Finset.mem_biUnion.mpr ⟨(T,d,k,j),Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨ki,Finset.mem_univ _,
    Finset.mem_image.mpr ⟨kl,Finset.mem_univ _,rfl⟩⟩⟩

theorem unmarked_order (L : LatePackets P G Bshort m0 gap)
    (T : Finset Slot) (d : dBank) (k : WindowKey table) (kl : Fin (nativeK buffer dmax+1)) :
    (L.unmarked T d k).order kl+2∈L.orders := by
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨(T,d,k),Finset.mem_univ _,Finset.mem_image.mpr ⟨kl,Finset.mem_univ _,rfl⟩⟩

theorem ordinary_controls (L : LatePackets P G Bshort m0 gap) (T : Finset Slot) (d : dBank) :
    (L.ordinary T d).S ⊆ L.ordinaryControls := by
  intro a ha
  exact Finset.mem_biUnion.mpr ⟨(T,d),Finset.mem_univ _,ha⟩
end LatePackets

#print axioms late_packets
#print axioms LatePackets.marked_order
end
end QRH.Cycle092.P2CommonSourceMetadata
