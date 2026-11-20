/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
import Candidate.C092.transport.RegularColoredTerminalLeafMediumUniform
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
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafStageMedium_0606d2698adf019a_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

open QRH.Cycle092.P2StageScalars
variable {n y : ℝ} (sc : Scalars) (r : ReadyStage sc n y)
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot] {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {buffer : ℝ}
variable {P : EarlyPackets Slot M A (r.cell.threshold:ℝ) 2 r.smallMesh r.lowMesh r.ordinaryMesh
  sc.εsource buffer r.ordinaryBank r.dec r.B}
variable {G : LateGeometry sc.dmin sc.dmax sc.dBank} {kernel : ℝ→ℂ}

/-- Every numerical guard in the genuine ordinary/inverse class join is
paid by the chosen stage. No source energy bound is supplied here. -/
theorem terminal_stage_medium_context_at (L : LateBundle P G (sc.m0 y) sc.gap kernel)
    {U V Cslot CLo : ℝ} {I : ℕ}
    (hAt : AtAll P G L.Bshort (sc.m0 y) sc.gap L.sources I Cslot CLo U)
    (T : Finset Slot) (db : sc.dBank)
    (D : TerminalTicketContext T M A G db n y r.mesh buffer sc.price U V Cslot I r.table)
    (hy0 : sourceY0 ≤ y) (hy1 : y ≤ sourceY) (hyn : y ≤ n) (hn : n ≤ sourceRatio*y)
    (hV : (98/100:ℝ) ≤ V) (hVd : V ≤ db.val) (hdV : db.val ≤ V+3*sc.conductor)
    (hGcap : G.Mcap=sc.Mcap) (hGmask : G.Bmask=0) (hGmargin : G.margin=sc.conductor) (hGR : G.R=22)
    (heps : G.ε ≤ 1/7500) (hepsFee : (sc.dmax+1)*G.ε ≤ r.B.feeFloor/1000)
    (hepsReserve : (sc.dmax+1)*G.ε ≤ sc.reserve/1000)
    (hheight : G.τ*(P.degreeBound:ℝ) ≤ sc.reserve) (hReserve : sc.reserve ≤ (rho:ℝ)/128)
    (hbuffer : 0 ≤ buffer) (hbufferFee : buffer*(Fintype.card Slot:ℝ) ≤ r.B.feeFloor/1000)
    (hbufferRho : buffer*(Fintype.card Slot:ℝ) ≤ (rho:ℝ)/1000)
    (hCslot : L.CslotFloor ≤ Cslot) (hY : 1 ≤ D.Y) (hwidth : sourceWidth n y-(u:ℝ) ≤ 1)
    (K : ℝ) (hK : 0 ≤ K) (hcard : (Fintype.card D.Key:ℝ) ≤ K*U^sc.dyadLoss)
    (p : Profiles (1/4) (9/4)) :
    finiteEnergyOn Finset.univ D.rows A.ηLong D.state.character
      (p.profile 0) (p.profile 1) D.tLong D.tShort D.X D.Y D.physical ≤
      K*L.normalizationConstant^4*(p.control L.controlsBound)^2*terminalMediumEnvelope L I Cslot*
      U^(terminalFramePrice V) := by
  have hb := sc.bank_source_bounds db.val db.property
  have hR : y/sc.dmin ≤ G.R := by
    rw [hGR]
    rw [sc.dmin_eq]
    norm_num [sourceY] at hy1 ⊢
    linarith
  have hm : r.mesh ≤ sc.dmin*r.ordinaryMesh := by
    have h := (div_le_iff₀ sc.dmin_pos).mp r.mesh_bounds.2.2.1
    simpa only [mul_comm] using h
  have hmi : r.mesh ≤ sc.dmin*r.B.mesh := by
    have h := (div_le_iff₀ sc.dmin_pos).mp r.mesh_bounds.2.2.2.2
    simpa only [mul_comm] using h
  have hsupply : G.Mcap db+G.Bmask+G.margin ≤ db.val := by
    rw [hGcap,hGmask,hGmargin,add_zero]
    exact sc.Mcap_supply db
  have he0 := G.hε.le
  have hde : sc.dmax*G.ε ≤ sc.reserve/1000 := by nlinarith only [hepsReserve,he0]
  have hwitness : (15/4:ℝ)*sc.dmax*G.ε ≤ (rho:ℝ)/128 := by
    have hr := sc.reserve_rho
    have hr0 : (0:ℝ) ≤ (rho:ℝ) := by norm_num [rho]
    nlinarith only [hde,hr,hr0]
  exact terminal_uniform_medium_source_at L hAt T db D r.threshold_pos hy0 hy1 hyn hn
    sc.dmin_pos hb.2.1 hb.2.2 hV hVd hdV hsupply hY hR hm r.mesh_bounds.2.2.2.1
    sc.gap_pos.le sc.gap_small r.table.ordinaryCap
    hCslot hbuffer hwidth heps sc.loss_pos.le sc.loss_small sc.price_pos.le sc.price_fee
    sc.conductor_fee sc.cap_fee hwitness sc.source_fee
    (hbufferRho.trans (by norm_num [rho])) (hheight.trans hReserve) hmi sc.conductor_loss hbufferFee hepsFee
    sc.dyadLoss K hK hcard sc.loss_height sc.dyad_budget p

#print axioms terminal_stage_medium_context_at
end
end QRH.Cycle092.RegularColoredForward
