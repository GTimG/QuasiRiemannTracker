/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
import Candidate.C092.transport.RegularColoredTerminalLeafMediumUniform
import Candidate.C092.transport.RegularColoredTerminalLeafCount
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
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafOriginalEvents_e588fe0085b9c812_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

open QRH.Cycle092.P2StageScalars
variable {n y : ℝ} (sc : Scalars) (r : ReadyStage sc n y)
variable {Slot : Type} [Fintype Slot] [DecidableEq Slot] {M : Ideal O} [NeZero M] {A : Arithmetic M}
variable {buffer : ℝ}
variable {P : EarlyPackets Slot M A (r.cell.threshold:ℝ) 2 r.smallMesh r.lowMesh r.ordinaryMesh
  sc.εsource buffer r.ordinaryBank r.dec r.B}
variable {G : LateGeometry sc.dmin sc.dmax sc.dBank} {kernel : ℝ→ℂ}

def TerminalOriginalStateAt (A : Arithmetic M) (Bmask collar U : ℝ) : Prop :=
  ∀(V Mcap : ℝ),0 ≤ V → V+collar ≤ Mcap →
    ∃s : NaturalState U Bmask A.bΦ,
      s.width ≤ Mcap ∧ s.character=A.ηShort ∧ s.puncture=1 ∧
      s.fixedModulus ≤ M ∧ s.fixedModulus ≤ A.baseShort.modulus ∧
      s.mask=fixedBadMask*idealGenerator 1 ∧
      (∀z : O,s.radial.keep z ↔ initialKeep s.character (internalQ A.QShort A.baseShort) z) ∧
      ∀rows : Finset FreeRow,
      (∀z∈rows,initialKeep A.ηShort (internalQ A.QShort A.baseShort) z.val) →
      (∀z∈rows,rowNorm z ≤ U^V) →
        (∀z∈rows,s.radial.keep z.val) ∧
        (∀z∈rows,s.radial.profile (‖eisEmbedding z.val‖^2/s.radial.scale)≠0)

structure TerminalStageAt (L : LateBundle P G (sc.m0 y) sc.gap kernel)
    (bank : DetectorBank Slot M A buffer sc.price sc.dmin sc.dmax y (sc.loss/10) r.cell r.table sc.dBank G)
    (Cslot CLo K U : ℝ) : Prop where
  sources : AtAll P G L.Bshort (sc.m0 y) sc.gap L.sources bank.indexBound Cslot CLo U
  detectors : ∀(T : Finset Slot) (d : sc.dBank),
    DetectorAt T M A buffer sc.price sc.dmin sc.dmax y (sc.loss/10) r.cell r.table sc.dBank G d (bank T d).I Cslot U
  state : TerminalOriginalStateAt A G.Bmask sc.conductor U
  key_budget : ∀db : sc.dBank,
    (Fintype.card (Fin (bank.indexBound+1)×Fin (⌊(73/200:ℝ)/G.ez⌋₊+1)×(Fin r.table.Je×Fin r.table.Jν)×
      Option (RayQuotient.Characters M A.Hr×RayQuotient.Characters M A.Hr)×
      Fin (dyadicLength (U^db.val))×Fin (dyadicLength (U^db.val))):ℝ) ≤ K*U^sc.dyadLoss
  half_height : 2 ≤ U^(G.τ/2)

/-- One common source event also retains the actual original radial state
and true two-dyad ticket budget, before any original live row or profile. -/
theorem terminal_original_common_event (L : LateBundle P G (sc.m0 y) sc.gap kernel)
    (bank : DetectorBank Slot M A buffer sc.price sc.dmin sc.dmax y (sc.loss/10) r.cell r.table sc.dBank G)
    (hbuffer : 0 < buffer) (hGmask : G.Bmask=0) :
    ∃Cslot : ℝ,0 < Cslot ∧ L.CslotFloor ≤ Cslot ∧ bank.paymentFloor ≤ Cslot ∧
    ∃CLo : ℝ,0 < CLo ∧ ∃K : ℝ,0 ≤ K ∧
      ∀ᶠ U : ℝ in atTop,TerminalStageAt sc r L bank Cslot CLo K U := by
  let Cslot := max L.CslotFloor bank.paymentFloor
  have hc : L.CslotFloor ≤ Cslot := le_max_left _ _
  have hb : bank.paymentFloor ≤ Cslot := le_max_right _ _
  obtain ⟨CLo,hCLo,hevent⟩:=terminal_common_event P G (sc.m0 y) sc.gap kernel L bank hbuffer Cslot le_rfl
  obtain ⟨K,hK,hcard⟩:=terminal_actual_key_budget
    (Label:=Option (RayQuotient.Characters M A.Hr×RayQuotient.Characters M A.Hr))
    bank.indexBound ⌊(73/200:ℝ)/G.ez⌋₊ r.table.Je r.table.Jν sc.dmin_pos sc.dmin_dmax sc.dyadLoss_pos
  have hs:=terminal_original_state_input M A G.Bmask sc.conductor hGmask sc.conductor_pos
  have hh : ∀ᶠ U : ℝ in atTop,2 < U^(G.τ/2) :=
    (tendsto_rpow_atTop (half_pos G.hτ)).eventually (eventually_gt_atTop (2:ℝ))
  refine ⟨Cslot,L.CslotFloor_pos.trans_le hc,hc,hb,CLo,hCLo,K,hK,?_⟩
  filter_upwards [hevent,hs,hcard,hh] with U he hs hk hh
  refine ⟨he.1,he.2,hs.2,?_,hh.le⟩
  intro db
  have hdb:=sc.bank_source_bounds db.val db.property
  exact hk.2 db.val hdb.2.1 hdb.2.2

#print axioms terminal_original_common_event
end
end QRH.Cycle092.RegularColoredForward
