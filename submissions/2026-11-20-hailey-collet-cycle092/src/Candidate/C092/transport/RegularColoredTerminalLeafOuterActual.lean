/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual ordinary ticket classes consume the genuine common source event. -/
import Candidate.C092.transport.RegularColoredTerminalLeafOriginalInput
import Candidate.C092.transport.P2InverseTicketDispatchActual
import Candidate.C092.transport.RegularColoredTerminalLeafAggregate
import Candidate.C092.transport.StrongPairRegularTerminalReserve
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
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafOuterActual_11cf966a2e85eb93_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {n y loss heightLoss dmin dmax price εm nativeError : ℝ} {cell : Cell}
variable {table : TerminalResponseTable y (loss/10) cell} {dBank : Finset ℝ}
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot]
variable {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {e Vmax smallMesh lowMesh ordinaryMesh εsource buffer : ℝ}
variable {ordinaryBank : Finset (ℝ×ℝ)} {dec : (ℝ×ℝ)→ℝ}
variable {B : TableBank (n:=n) (heightLoss:=heightLoss) (dmin:=dmin) (dmax:=dmax) (price:=price) table dBank εm nativeError}
variable {P : EarlyPackets Slot M A e Vmax smallMesh lowMesh ordinaryMesh εsource buffer ordinaryBank dec B}
variable {G : LateGeometry dmin dmax dBank} {m0 gap : ℝ} {kernel : ℝ→ℂ}

theorem terminal_actual_small_input_at (L : LateBundle P G m0 gap kernel)
    {U V Cslot CLo mesh : ℝ} {I : ℕ}
    (hAt : AtAll P G L.Bshort m0 gap L.sources I Cslot CLo U)
    (F : TerminalOriginalInput Slot M A n y mesh U V)
    (hV0 : 0 ≤ V) (hV1 : V ≤ 98/100)
    (hy : 0 ≤ y) (hn : 0 ≤ n) (hmesh : mesh ≤ smallMesh)
    (hOld : |F.tOld|+F.height ≤ U^(1/2:ℝ)) (p : Profiles (1/4) (9/4)) :
    F.energy F.rows p ≤ P.small.C*QuadraticInitialBound.diagonalControl radialMajorant*
      (p.control P.small.controls)^2*(1+|F.tLong|+|F.tShort|+F.height)^P.small.degree*
      U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)) := by
  exact hAt.small.2 V hV0 hV1 F.T F.theta F.thetaLong F.thetaShort F.w F.sigma F.sigma F.sigma
    F.v F.vLong F.vShort F.tOld F.tLong F.tShort F.height F.height F.width_nonneg
    (fun j=>(F.width_mesh j).trans hmesh) F.sigma_eq
    (fun j=>(F.sigma_eq j).ge) (fun j=>(F.sigma_eq j).le)
    (fun j=>(F.sigma_eq j).ge) (fun j=>(F.sigma_eq j).le)
    F.pitch hOld F.height_nonneg F.pitchLong F.pitchShort F.width_sum p F.X F.Y
    F.long_positive F.short_positive
    (terminal_original_length_cap hAt.one hn F.long_cap)
    (terminal_original_length_cap hAt.one hy F.short_cap)
    F.rows F.old_keep F.long_keep F.short_keep F.row_norm F.long_presentation F.short_presentation

theorem terminal_actual_low_high_input_at (L : LateBundle P G m0 gap kernel)
    {U V Cslot CLo mesh : ℝ} {I : ℕ}
    (hAt : AtAll P G L.Bshort m0 gap L.sources I Cslot CLo U)
    (F : TerminalOriginalInput Slot M A n y mesh U V)
    (hV0 : (98/100:ℝ) ≤ V) (hV1 : V ≤ Vmax)
    (hy : 0 ≤ y) (hn : 0 ≤ n) (hmesh : mesh ≤ lowMesh) (p : Profiles (1/4) (9/4)) :
    F.energy (F.rows.filter (fun z=>F.response buffer Cslot z ≤ e)) p+
      F.energy (F.rows.filter (fun z=>(responseUpper:ℝ)<F.response buffer Cslot z)) p ≤
      CLo*QuadraticInitialBound.diagonalControl radialMajorant*(p.control P.lowHigh.controls)^2*
      (1+|F.tLong|+|F.tShort|+F.height)^P.lowHigh.degree*
      U^(V+(u:ℝ)-(rho:ℝ)/4+(5/6)*max 0 ((H:ℝ)-V)) := by
  have hupper : (responseUpper:ℝ)=(5002/10000:ℝ) := by norm_num [responseUpper]
  simpa only [TerminalOriginalInput.energy,TerminalOriginalInput.response,TerminalOriginalInput.mark,
    hupper] using hAt.lowHigh V hV0 hV1 F.T F.theta F.thetaLong F.thetaShort F.w F.sigma F.sigma F.sigma
    F.v F.vLong F.vShort F.tOld F.tLong F.tShort F.height F.width_nonneg
    (fun j=>(F.width_mesh j).trans hmesh)
    (fun j=>(F.sigma_eq j).ge) (fun j=>(F.sigma_eq j).le)
    (fun j=>(F.sigma_eq j).ge) (fun j=>(F.sigma_eq j).le)
    (fun j=>(F.sigma_eq j).ge) (fun j=>(F.sigma_eq j).le)
    F.height_nonneg F.pitchLong F.pitchShort F.width_sum p F.X F.Y
    F.long_positive F.short_positive
    (terminal_original_length_cap hAt.one hn F.long_cap)
    (terminal_original_length_cap hAt.one hy F.short_cap)
    F.rows F.long_keep F.short_keep F.row_norm F.long_presentation F.short_presentation

#print axioms terminal_actual_small_input_at
#print axioms terminal_actual_low_high_input_at
end
end QRH.Cycle092.RegularColoredForward
