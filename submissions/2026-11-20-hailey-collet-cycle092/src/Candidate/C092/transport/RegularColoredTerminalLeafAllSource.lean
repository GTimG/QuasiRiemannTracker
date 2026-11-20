/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
import Candidate.C092.transport.RegularColoredTerminalLeafBoundedSource
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
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafAllSource_93562302d845c3a2_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Genuine all-response, all-radius original P2. Independent ordinary
characters, selected whole slots, all physical heights and actual shortened
ordered scales are retained in the checked public physical source inlet. -/
theorem terminal_genuine_ordered_source {n y : ℝ}
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
    ∃degree : ℕ,∃controls : Finset (ℕ×ℕ),∃C : ℝ,0 < C ∧
      ∀ᶠ U : ℝ in atTop,QRH.Cycle092.RegularFramePhysicalReturn.OrderedP2At Slot M Hr hHr W n y mesh U
        old base omega1 omega2 Q degree controls C := by
  obtain ⟨mesh,hmesh,hbounded⟩:=terminal_genuine_bounded_ordered_source hbeta cover hy0 hy1 hyn hn
  refine ⟨mesh,hmesh,?_⟩
  intro Slot _ _ M _ Hr hHr W hW hWs bΦ hbΦ hΦ old base omega1 omega2 Q hQM hQ10 hQ1t hQ172 hQ20 hQ2t hQ272
  obtain ⟨kappa,hkappa,degree,controls,C,hC,hsource⟩:=hbounded Slot M Hr hHr W hW hWs bΦ hbΦ hΦ
    old base omega1 omega2 Q hQM hQ10 hQ1t hQ172 hQ20 hQ2t hQ272
  exact QRH.Cycle092.RegularFramePhysicalReturn.full_ordered_from_bounded Slot M Hr hHr W hW.continuous hWs
    n y mesh kappa hkappa hbeta hy0 hy1 hyn hn old base omega1 omega2 Q hQM hQ10 hQ1t hQ172 hQ20 hQ2t hQ272
    bΦ (by linarith only [hbΦ]) hΦ degree controls C hC hsource

#print axioms terminal_genuine_ordered_source
end
end QRH.Cycle092.RegularColoredForward
