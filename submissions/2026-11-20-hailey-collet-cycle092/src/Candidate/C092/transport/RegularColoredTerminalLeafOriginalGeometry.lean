/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Literal original finite data passed from the genuine detector to the terminal
sources. Every field is geometry, a coefficient identity, or a real ticket;
there is no analytic energy bound in this interface. -/
import Candidate.C092.transport.P2DetectorTicketContextGeometry
import Candidate.C092.transport.RegularColoredTerminalLeafOriginalInput
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
local instance c092LocalInst_Candidate_C092_transport_RegularColoredTerminalLeafOriginalGeometry_4da1bc63218e2f79_001 (M : Ideal O) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- Build the actual detector geometry on precisely the medium original
rows. Both complete common-mark presentations are inherited literally. -/
theorem terminal_original_medium_geometry
    {Slot : Type} [Fintype Slot] [DecidableEq Slot] {M : Ideal O} [NeZero M] (A : Arithmetic M)
    {dmin dmax : ℝ} {dBank : Finset ℝ} (G : LateGeometry dmin dmax dBank) (db : dBank)
    {n y mesh buffer price U V Cslot step : ℝ} {cell : Cell}
    (table : TerminalResponseTable y step cell)
    (F : TerminalOriginalInput Slot M A n y mesh U V)
    (s : NaturalState U G.Bmask A.bΦ)
    (hs : s.width ≤ G.Mcap db) (hchar : s.character=A.ηShort) (hpuncture : s.puncture=1)
    (hsM : s.fixedModulus ≤ M) (hsBase : s.fixedModulus ≤ A.baseShort.modulus)
    (hkeepEq : ∀z : O,s.radial.keep z ↔ initialKeep s.character (internalQ A.QShort A.baseShort) z)
    (hsupport : (∀z∈F.rows,s.radial.keep z.val) ∧
      ∀z∈F.rows,s.radial.profile (‖eisEmbedding z.val‖^2/s.radial.scale)≠0)
    (hheight : |F.tShort|+|F.tLong|+2*F.height ≤ U^G.τ) :
    ∃B : TerminalRowGeometry F.T M A G db n y mesh buffer price U V Cslot table,
      B.rows=F.mediumRows buffer Cslot (cell.threshold:ℝ) ∧ B.state=s ∧
      B.physical=(fun j:F.T=>F.mark j.val) ∧ B.X=F.X ∧ B.Y=F.Y ∧
      B.tLong=F.tLong ∧ B.tShort=F.tShort ∧ B.w=(fun j:F.T=>F.w j.val) ∧
      (∀z∈B.rows,(cell.threshold:ℝ) ≤ measured M A.Hr A.hHr A.ηShort A.baseShort A.W U
        (Cslot*U^buffer) B.theta B.w B.v B.tShort z ∧ measured M A.Hr A.hHr A.ηShort A.baseShort A.W U
        (Cslot*U^buffer) B.theta B.w B.v B.tShort z ≤ (responseUpper:ℝ)) := by
  let rows := F.mediumRows buffer Cslot (cell.threshold:ℝ)
  have hsub : rows⊆F.rows := Finset.filter_subset _ _
  let B : TerminalRowGeometry F.T M A G db n y mesh buffer price U V Cslot table := {
    rows:=rows,state:=s,width_bound:=hs,character:=hchar,puncture:=hpuncture,
    modulus_ray:=hsM,modulus_base:=hsBase,keep:=fun z hz=>hsupport.1 z (hsub hz),
    keep_equiv:=hkeepEq,plateau:=fun z hz=>hsupport.2 z (hsub hz),
    row_norm:=fun z hz=>F.row_norm z (hsub hz),long_keep:=fun z hz=>F.long_keep z (hsub hz),
    theta:=fun j=>F.thetaShort j.val,thetaLong:=fun j=>F.thetaLong j.val,
    w:=fun j=>F.w j.val,v:=fun j=>F.vShort j.val,vLong:=fun j=>F.vLong j.val,
    tShort:=F.tShort,tLong:=F.tLong,height:=F.height,height_nonneg:=F.height_nonneg,
    pitch:=fun j=>F.pitchShort j.val,pitchLong:=fun j=>F.pitchLong j.val,native_height:=hheight,
    width_nonneg:=fun j=>F.width_nonneg j.val,width_mesh:=fun j=>F.width_mesh j.val,
    width_sum:=by simpa only [Finset.sum_coe_sort] using F.width_sum,
    physical:=fun j=>F.mark j.val,
    short_presentation:=fun z hz j=>F.descriptor_short z (hsub hz) j,
    long_presentation:=fun z hz j=>F.descriptor_long z (hsub hz) j,
    X:=F.X,Y:=F.Y,long_positive:=F.long_positive,short_positive:=F.short_positive,
    long_cap:=F.long_cap,short_cap:=F.short_cap }
  refine ⟨B,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro z hz
  have hm := (Finset.mem_filter.mp hz).2
  have he := F.response_measured buffer Cslot z (hsub hz)
  exact ⟨by rw [←he];exact hm.1.le,
    by rw [←he];exact hm.2⟩

#print axioms terminal_original_medium_geometry
end
end QRH.Cycle092.RegularColoredForward
