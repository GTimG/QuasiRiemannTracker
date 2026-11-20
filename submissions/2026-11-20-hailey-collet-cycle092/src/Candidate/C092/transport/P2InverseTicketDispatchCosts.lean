/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual ordinary ticket classes consume the genuine common source event. -/
import Candidate.C092.transport.RegularColoredTerminalLeafContext
import Candidate.C092.transport.RegularColoredTerminalLeafMarkedOriginal
import Candidate.C092.transport.RegularColoredTerminalLeafUnmarkedOriginal
import Candidate.C092.transport.RegularColoredTerminalLeafDecision
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros
open ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_P2InverseTicketDispatchCosts_9b442795c25ff5f7_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {e Vmax smallMesh lowMesh ordinaryMesh εsource buffer : ℝ}
variable {ordinaryBank : Finset (ℝ×ℝ)} {dec : (ℝ×ℝ)→ℝ}
variable {B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError}
variable {P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B}
variable {G : LateGeometry dmin dmax dBank} {m0 gap : ℝ} {kernel : ℝ→ℂ}

def terminalInverseMarkedCost (L : LateBundle P G m0 gap kernel) (T : Finset Slot) (db : dBank)
    (k : WindowKey table) (j : Fin B.J) (I : ℕ) (Cslot : ℝ) : ℝ :=
  (Fintype.card T:ℝ)*(∑z : Fin (nativeK buffer dmax+1)×Fin (nativeK buffer dmax+1),
    Cslot^(Fintype.card T)*(L.sources.marked T db k j).Cy z.1 z.2*
      (12*(P.inverse.marked T db k j).Cc z.1 z.2+1)*
      ((P.inverse.marked T db k j).Cl z.1 z.2*QuadraticInitialBound.diagonalControl radialMajorant+1)*
      (2+2*Real.pi+(3*I:ℕ))^((P.inverse.marked T db k j).Jc z.1 z.2+1)*
      (3:ℝ)^((P.inverse.marked T db k j).degree z.1 z.2))

def terminalInverseUnmarkedCost (L : LateBundle P G m0 gap kernel) (T : Finset Slot) (db : dBank)
    (k : WindowKey table) (I : ℕ) (Cslot : ℝ) : ℝ :=
  (Fintype.card T:ℝ)*(∑z : Fin (nativeK buffer dmax+1),
    Cslot^(Fintype.card T)*(L.sources.unmarked T db k).Cy z*
      (192*(P.inverse.unmarked T db k).Cc z+1)*
      ((P.inverse.unmarked T db k).Cl z*QuadraticInitialBound.diagonalControl radialMajorant+1)*
      (2+2*Real.pi+(3*I:ℕ))^((P.inverse.unmarked T db k).Jc z+1)*
      (3:ℝ)^((P.inverse.unmarked T db k).degree z))

def terminalInverseCost (L : LateBundle P G m0 gap kernel) (T : Finset Slot) (db : dBank)
    (k : WindowKey table) (I : ℕ) (Cslot : ℝ) : ℝ :=
  terminalInverseUnmarkedCost L T db k I Cslot+∑j : Fin B.J,terminalInverseMarkedCost L T db k j I Cslot

theorem terminal_inverse_marked_cost_nonneg (L : LateBundle P G m0 gap kernel) (T : Finset Slot) (db : dBank)
    (k : WindowKey table) (j : Fin B.J) (I : ℕ) {Cslot : ℝ} (hCslot : 0 ≤ Cslot) :
    0 ≤ terminalInverseMarkedCost L T db k j I Cslot := by
  unfold terminalInverseMarkedCost
  apply mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg _)
  intro z _
  have hCy := (L.sources.marked T db k j).positive z.1 z.2
  have hp := (P.inverse.marked T db k j).positive z.1 z.2
  have hCc := hp.1
  have hCl := hp.2
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  positivity

theorem terminal_inverse_unmarked_cost_nonneg (L : LateBundle P G m0 gap kernel) (T : Finset Slot) (db : dBank)
    (k : WindowKey table) (I : ℕ) {Cslot : ℝ} (hCslot : 0 ≤ Cslot) :
    0 ≤ terminalInverseUnmarkedCost L T db k I Cslot := by
  unfold terminalInverseUnmarkedCost
  apply mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg _)
  intro z _
  have hCy := (L.sources.unmarked T db k).positive z
  have hp := (P.inverse.unmarked T db k).positive z
  have hCc := hp.1
  have hCl := hp.2
  have hdiag := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
  positivity

theorem terminal_inverse_cost_bounds (L : LateBundle P G m0 gap kernel) (T : Finset Slot) (db : dBank)
    (k : WindowKey table) (I : ℕ) {Cslot : ℝ} (hCslot : 0 ≤ Cslot) :
    0 ≤ terminalInverseCost L T db k I Cslot ∧
    terminalInverseUnmarkedCost L T db k I Cslot ≤ terminalInverseCost L T db k I Cslot ∧
    ∀j,terminalInverseMarkedCost L T db k j I Cslot ≤ terminalInverseCost L T db k I Cslot := by
  have hu := terminal_inverse_unmarked_cost_nonneg L T db k I hCslot
  have hm := fun j=>terminal_inverse_marked_cost_nonneg L T db k j I hCslot
  have hs := Finset.sum_nonneg (s:=Finset.univ) (fun j _=>hm j)
  unfold terminalInverseCost
  refine ⟨add_nonneg hu hs,by linarith,?_⟩
  intro j
  have h := Finset.single_le_sum (fun j _=>hm j) (Finset.mem_univ j)
  linarith

#print axioms terminal_inverse_cost_bounds
end
end QRH.Cycle092.RegularColoredForward
