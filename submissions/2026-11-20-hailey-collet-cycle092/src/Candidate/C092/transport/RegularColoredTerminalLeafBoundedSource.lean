/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
import Candidate.C092.transport.RegularColoredTerminalLeafBoundedStage
import Candidate.C092.transport.RegularP2AllHeights
import Candidate.C092.transport.RegularColoredTerminalLeafStateInput
import Candidate.C092.transport.P2StageScalarsLate
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
open CenteredMomentDetectorPlainFiberSource
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros
open ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafBoundedSource_66295f94e1b85753_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

open QRH.Cycle092.P2StageScalars

/-- A stricter terminal reserve is chosen before every genuine source
factory. Its positive margin remains independent of all live heights. -/
def terminal_paid_scalars (sc : Scalars) : Scalars := { sc with
  reserve:=min sc.reserve ((rho:ℝ)/256),
  reserve_pos:=lt_min sc.reserve_pos (by norm_num [rho]),
  reserve_small:=(min_le_left _ _).trans sc.reserve_small }

theorem terminal_paid_scalars_fee (sc : Scalars) :
    (terminal_paid_scalars sc).reserve ≤ (rho:ℝ)/128 :=
  (min_le_right _ _).trans (by norm_num [rho])

/-- Genuine bounded original P2 with mesh before Slot, and all degree,
profile controls and constants before the base U and every live row. -/
theorem terminal_genuine_bounded_ordered_source {n y : ℝ}
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (cover : EarlierCover PairOpenWidth y)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y) :
    ∃mesh : ℝ,0 < mesh ∧
    ∀(Slot : Type) [Fintype Slot] [DecidableEq Slot],
    ∀(M : Ideal O) [NeZero M] (Hr : Subgroup (O⧸M)ˣ) (hHr : RayOrthogonality.globalUnits M ≤ Hr),
    ∀(W : ℝ→ℂ),ContDiff ℝ ∞ W → Function.support W⊆Icc (1:ℝ) 2 →
    ∀bΦ : ℝ,2 ≤ bΦ → Function.support (radialMajorant:ℝ→ℂ)⊆Iic bΦ →
    ∀(old base omega1 omega2 : Character) (Q : Ideal O),Q ≤ M →
      internalQ Q (base.product omega1)≠0 → internalQ Q (base.product omega1)≠⊤ →
      internalQ Q (base.product omega1) ≤ Ideal.span {(72:O)} →
      internalQ Q (base.product omega2)≠0 → internalQ Q (base.product omega2)≠⊤ →
      internalQ Q (base.product omega2) ≤ Ideal.span {(72:O)} →
    ∃kappa : ℝ,0 < kappa ∧ ∃degree : ℕ,∃controls : Finset (ℕ×ℕ),∃C : ℝ,0 < C ∧
      ∀ᶠ U : ℝ in atTop,QRH.Cycle092.RegularFramePhysicalReturn.BoundedOrderedP2At Slot M Hr hHr W n y mesh U
        old base omega1 omega2 Q degree controls C kappa := by
  obtain ⟨sc0⟩:=choose_stage_scalars
  let sc:=terminal_paid_scalars sc0
  have hreserve : sc.reserve ≤ (rho:ℝ)/128:=terminal_paid_scalars_fee sc0
  obtain ⟨r⟩:=genuine_stage_early sc hbeta cover hy0 hy1 hyn hn
  refine ⟨r.mesh,r.mesh_bounds.1,?_⟩
  intro Slot _ _
  obtain ⟨buffer,hbuffer,hbufferFee,hbufferRho,hpackets⟩:=r.packets Slot
  intro M _ Hr hHr W hW hWs bΦ hbΦ hΦ old base omega1 omega2 Q hQM hQ10 hQ1t hQ172 hQ20 hQ2t hQ272
  let A:=terminal_pair_arithmetic M Hr hHr W hW hWs bΦ hbΦ hΦ old base omega1 omega2 Q hQM
    hQ10 hQ1t hQ172 hQ20 hQ2t hQ272
  obtain ⟨P⟩:=hpackets M A
  obtain ⟨kappa,hkappa,degree,controls,C,hC,hsource⟩:=terminal_genuine_bounded_stage_source sc r P
    hbeta hy0 hy1 hyn hn hbuffer hbufferFee hbufferRho hreserve (fun _=>1) contDiff_const
  refine ⟨kappa,hkappa,degree,controls,C,hC,?_⟩
  filter_upwards [hsource] with U hU
  exact terminal_bounded_ordered_of_original M Hr hHr W hW hWs bΦ hbΦ hΦ old base omega1 omega2 Q hQM
    hQ10 hQ1t hQ172 hQ20 hQ2t hQ272 hU

#print axioms terminal_genuine_bounded_ordered_source
end
end QRH.Cycle092.RegularColoredForward
