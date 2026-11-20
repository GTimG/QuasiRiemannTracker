/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
import Candidate.C092.transport.RegularColoredTerminalLeafOriginalMedium
import Candidate.C092.transport.RegularColoredTerminalLeafOriginalHeights
import Candidate.C092.transport.RegularColoredTerminalLeafBoundedNative
import Candidate.C092.transport.RegularP2BranchCollection
import Candidate.C092.transport.RegularFramePhysicalReturnSourceCaps
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
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafBoundedStage_877e8f174c7fda44_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

open QRH.Cycle092.P2StageScalars
variable {n y : ℝ} (sc : Scalars) (r : ReadyStage sc n y)
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot] {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {buffer : ℝ}
variable {P : EarlyPackets Slot M A (r.cell.threshold:ℝ) 2 r.smallMesh r.lowMesh r.ordinaryMesh
  sc.εsource buffer r.ordinaryBank r.dec r.B}
variable {G : LateGeometry sc.dmin sc.dmax sc.dBank} {kernel : ℝ→ℂ}

/-- The complete all-response bounded P2 source on the actual original
rows. Every analytic branch is invoked from its genuine common packet; the
only hypothesis inherited from the earlier induction is already inside P. -/
theorem terminal_genuine_bounded_stage_source
    (P : EarlyPackets Slot M A (r.cell.threshold:ℝ) 2 r.smallMesh r.lowMesh r.ordinaryMesh
      sc.εsource buffer r.ordinaryBank r.dec r.B)
    (hbeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y)
    (hbuffer : 0 < buffer) (hbufferFee : buffer*(Fintype.card Slot:ℝ) ≤ r.B.feeFloor/1000)
    (hbufferRho : buffer*(Fintype.card Slot:ℝ) ≤ (rho:ℝ)/1000)
    (hReserve : sc.reserve ≤ (rho:ℝ)/128)
    (kernel : ℝ→ℂ) (hkernel : ContDiff ℝ ∞ kernel) :
    ∃kappa : ℝ,0 < kappa ∧ ∃degree : ℕ,∃controls : Finset (ℕ×ℕ),∃C : ℝ,0 < C ∧
      ∀ᶠ U : ℝ in atTop,TerminalBoundedOriginalAt Slot M A n y r.mesh U kappa degree controls C := by
  obtain ⟨G,hGcap,hGmask,hGmargin,hGR,htau,hheightLoss,hheight,heps,hepsFee,hCost,hDetector,hepsReserve,
    bank,hL⟩:=genuine_stage_late r P kernel hkernel hbeta hbuffer
  obtain ⟨L⟩:=hL
  obtain ⟨Cslot,hCslot0,hCslot,hBankSlot,CLo,hCLo,K,hK,hevent⟩:=
    terminal_original_common_event sc r L bank hbuffer hGmask
  let C:=collectedConstant L bank.indexBound Cslot CLo K
  have hC : 0 < C := by
    have hN : 0 < L.normalizationConstant := zero_lt_one.trans_le L.normalization_bounds.1
    have hEnv := (terminal_medium_envelope_bounds L bank.indexBound hCslot0.le).1
    have hSmall := P.small.positive
    have hDiag := QuadraticInitialBound.diagonalControl_nonneg radialMajorant
    dsimp only [C,collectedConstant]
    positivity
  refine ⟨G.τ/2,half_pos G.hτ,P.degreeBound,L.controlsBound,C,hC,?_⟩
  filter_upwards [hevent] with U hAt
  intro V hV hV2 F hY hH p
  have hheights:=terminal_original_height_gates F hAt.sources.one htau hAt.half_height hH
  have hcaps:=QRH.Cycle092.RegularFramePhysicalReturn.original_source_caps hy0 hy1 hyn hn
  have hwidth : sourceWidth n y-(u:ℝ) ≤ 1 :=
    hcaps.1.trans (by norm_num [QRH.Cycle092.ReferenceArmRadial.widthCap])
  have hy : 0 ≤ y := (by norm_num [sourceY0] : (0:ℝ) ≤ sourceY0).trans hy0
  have hn0 : 0 ≤ n := hy.trans hyn
  apply collect_actual_branches L hAt.sources hAt.sources.one F p hV hV2 hy hn0
    r.mesh_all_sources.1 r.mesh_all_sources.2.1 hheights.2 r.threshold_upper
    (bank.payment_one.trans hBankSlot) hCLo.le hK
  intro hV98
  exact terminal_actual_original_medium_at sc r L bank hAt F hy0 hy1 hyn hn hV98.le hV2
    hGcap hGmask hGmargin hGR heps hepsFee hepsReserve hheight hReserve hbuffer.le hbufferFee hbufferRho
    hCslot hK hY hwidth hheights.1 p

#print axioms terminal_genuine_bounded_stage_source
end
end QRH.Cycle092.RegularColoredForward
