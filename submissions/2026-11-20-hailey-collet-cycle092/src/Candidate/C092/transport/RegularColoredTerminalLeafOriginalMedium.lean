/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
import Candidate.C092.transport.RegularColoredTerminalLeafOriginalEvents
import Candidate.C092.transport.RegularColoredTerminalLeafOriginalGeometry
import Candidate.C092.transport.RegularColoredTerminalLeafStageMedium
import Candidate.C092.transport.P2DetectorTicketContextCore
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
open CenteredMomentEnergyBands CenteredMomentWholeSlotDeletion CenteredMomentFiniteProfileExceptional
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorZeros
open ConcretePrimeRowBridge ConcreteTraceCRT
open QRH.Cycle092.MediumReplace.Source
open QRH.Cycle092.P2CommonSourceMetadata QRH.Cycle092.TerminalActualRow
open QRH.Cycle092.SourceInverseP6 QRH.Cycle092.WholeSlot QRH.Cycle092.LowActual QRH.Cycle092.StrongPair
open QRH.Cycle092.Source QRH.Cycle092.SourceFurtherWitness QRH.Cycle090 QRH.SourceCertificate
local notation "O" => HeckeFamily.O
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafOriginalMedium_ce449400b63140e1_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

open QRH.Cycle092.P2StageScalars
variable {n y : ℝ} (sc : Scalars) (r : ReadyStage sc n y)
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot] {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {buffer : ℝ}
variable {P : EarlyPackets Slot M A (r.cell.threshold:ℝ) 2 r.smallMesh r.lowMesh r.ordinaryMesh
  sc.εsource buffer r.ordinaryBank r.dec r.B}
variable {G : LateGeometry sc.dmin sc.dmax sc.dBank} {kernel : ℝ→ℂ}

/-- The genuine source is applied to exactly the medium filter of the
original row set. The actual radial state and same-zero tickets are built
from retained source events; no class energy is an input. -/
theorem terminal_actual_original_medium_at (L : LateBundle P G (sc.m0 y) sc.gap kernel)
    (bank : DetectorBank Slot M A buffer sc.price sc.dmin sc.dmax y (sc.loss/10) r.cell r.table sc.dBank G)
    {U V Cslot CLo K : ℝ}
    (hAt : TerminalStageAt sc r L bank Cslot CLo K U)
    (F : TerminalOriginalInput Slot M A n y r.mesh U V)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y)
    (hV : (98/100:ℝ) ≤ V) (hV2 : V ≤ 2)
    (hGcap : G.Mcap=sc.Mcap) (hGmask : G.Bmask=0) (hGmargin : G.margin=sc.conductor) (hGR : G.R=22)
    (heps : G.ε ≤ 1/7500) (hepsFee : (sc.dmax+1)*G.ε ≤ r.B.feeFloor/1000)
    (hepsReserve : (sc.dmax+1)*G.ε ≤ sc.reserve/1000)
    (hheight : G.τ*(P.degreeBound:ℝ) ≤ sc.reserve) (hReserve : sc.reserve ≤ (rho:ℝ)/128)
    (hbuffer : 0 ≤ buffer) (hbufferFee : buffer*(Fintype.card Slot:ℝ) ≤ r.B.feeFloor/1000)
    (hbufferRho : buffer*(Fintype.card Slot:ℝ) ≤ (rho:ℝ)/1000)
    (hCslot : L.CslotFloor ≤ Cslot) (hK : 0 ≤ K)
    (hY : 1 ≤ F.Y) (hwidth : sourceWidth n y-(u:ℝ) ≤ 1)
    (hnative : |F.tShort|+|F.tLong|+2*F.height ≤ U^G.τ)
    (p : Profiles (1/4) (9/4)) :
    F.energy (F.mediumRows buffer Cslot (r.cell.threshold:ℝ)) p ≤
      K*L.normalizationConstant^4*(p.control L.controlsBound)^2*
      terminalMediumEnvelope L bank.indexBound Cslot*U^(terminalFramePrice V) := by
  obtain ⟨db,hdb,hdb',hcap,hsupply,hdV⟩:=sc.selected_cap_geometry hV hV2
  have hV0 : 0 ≤ V := by linarith only [hV]
  have hcap' : V+sc.conductor ≤ G.Mcap db := by rw [hGcap];exact hcap
  obtain ⟨s,hs,hchar,hpuncture,hsM,hsBase,hmask,hkeepEq,hsupport⟩:=hAt.state V (G.Mcap db) hV0 hcap'
  obtain ⟨B,hBR,hBS,hBP,hBX,hBY,hBtL,hBtS,hBw,hmedium⟩:=terminal_original_medium_geometry (buffer:=buffer) (price:=sc.price) (Cslot:=Cslot) A G db r.table F
    s hs hchar hpuncture hsM hsBase hkeepEq (hsupport F.rows F.short_keep F.row_norm) hnative
  have hwd : ∀j,B.w j/db.val ≤ 22 := by
    intro j
    rw [hBw]
    have hj : F.w j.val ≤ 1 :=
      (Finset.single_le_sum (fun i _=>F.width_nonneg i) j.property).trans (F.width_sum.trans hwidth)
    have hd0 : 0 < db.val := sc.dmin_pos.trans_le hdb
    apply (div_le_iff₀ hd0).mpr
    have hdb98 : (98/100:ℝ) ≤ db.val := by simpa only [sc.dmin_eq] using hdb
    nlinarith only [hj,hdb98]
  obtain ⟨D,hDR,hDS,hDP,hDX,hDY,hDtL,hDtS,hrest⟩:=terminal_ticket_context_from_geometry A G db r.table
    (hAt.detectors F.T db) (bank.index_le F.T db) B hwd hmedium
  have hY' : 1 ≤ D.Y := by rw [hDY,hBY];exact hY
  have hVd : V ≤ db.val := by
    have hc:=sc.conductor_pos
    dsimp only [Scalars.Mcap] at hcap
    linarith only [hcap,hc]
  have hc := hAt.key_budget db
  have hE:=terminal_stage_medium_context_at sc r L hAt.sources F.T db D hy0 hy1 hyn hn hV hVd hdV
    hGcap hGmask hGmargin hGR heps hepsFee hepsReserve hheight hReserve hbuffer hbufferFee hbufferRho
    hCslot hY' hwidth K hK hc p
  rw [D.character,hDR,hBR,hDP,hBP,hDX,hBX,hDY,hBY,hDtL,hBtL,hDtS,hBtS] at hE
  unfold TerminalOriginalInput.energy
  rw [terminal_energy_subtype]
  exact hE

#print axioms terminal_actual_original_medium_at
end
end QRH.Cycle092.RegularColoredForward
