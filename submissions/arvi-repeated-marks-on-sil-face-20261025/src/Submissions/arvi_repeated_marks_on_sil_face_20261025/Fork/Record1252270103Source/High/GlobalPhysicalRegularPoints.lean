/- Repeated marks: fork of Record1252270103Source.High.GlobalPhysicalRegularPoints (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularPoints
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainC
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.CountWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.GainPaymentK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.PaymentWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.WitnessWrappersK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Finite.SourceValid2
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.High.GlobalPhysicalRegularControls
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Fork.Record1252270103Source.Admission.SelectedRegularCombinedPointSome
/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Genuine earlier LOW and HIGH sources control the same full centered family. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
open OAI OAI.SevenEighths
open QRH.Record1252270103Source.High
open QRH.Record1252270103Source.Admission
open QRH.Record1252270103Source.High.GlobalPhysical
open QRH.Record1252270103Low QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open Record1252270103Source Record1252270103Second
open Record1252270103Finite PhysicalScalar HighScalar Record1252270103Source.Collision
open Cycle61HighGeometry Record1252270103CommonGeometry
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open Record12518109Natural
open Cycle61InitialMass WeightedHigh JointHigh MarkedPlain
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Set Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
open CenteredMomentChildRows RayFourExpansion HeckeInverseAmplification
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstSourceReduction ConcretePrimeRowBridge
open ProbeHighRowFamily ProbePhysical Record12518109GainWholeGeometry
open SelectedHighCofactorFamily SelectedHighCofactorCoordinates
open SelectedHighPaid Pool
local instance regularPointsDecEq_rm {ι : Type*} : DecidableEq ι := Classical.decEq _
local notation "O" => HeckeFamily.O

open SelectedRegularHighPoint CenteredMomentEnergyBands
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondInputCapacitySource Cycle61Moment LocalMoment
open PhysicalAnalytic Record1252270103Finite
open Set Filter Admission
open High.GlobalPhysical SelectedRegularHighPoint SelectedRegularSourceData SelectedHighCofactorFamily
open SelectedRegularCombinedPoint SelectedRegularLowPoint
variable {α:Type}[Fintype α]
variable (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
variable (ηanchor η₀:Character)(n low:Source)(setup:DensityCountingSetup)
variable (W:ℝ→ℂ)(hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
variable (bRad:ℝ)(hbRad:2≤bRad)
variable (hrad:Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bRad)
variable (Kgraph:ℚ)(bcell reserve θ mesh ξ width:ℝ)(N:ℕ)(wmin rmin εslot:ℝ)
variable (hf:FixedBudget reserve 100 100 1 θ)(hc:CardinalityBudget θ 100 100 1 1 N wmin rmin εslot)
variable (sc:Scalar Kgraph n low bcell θ mesh ξ width)
variable (hmesh:100*mesh≤θ)(hwidth:width≤θ)(hbcell:bcell≤1)
variable (hr:reserve≤(n.allowance:ℝ))(hfee:0≤(n.highFee:ℝ))(hq:1/2≤(n.q:ℝ))
variable (R₀:Ideal O)(hR₀:R₀≠0)(Q:Ideal O)(hQM:Q≤M)(hQ72:internalQ Q η₀≤Ideal.span {(72:O)})
variable (hβ:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hβhi:HeckeZeroSupremum.beta≤7/8)
variable (hq1:(n.q:ℝ)≤1)(hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))
variable (hLowMesh:mesh≤regularLowMesh Kgraph n low bcell θ sc.geometry sc.parent sc.low_parent
  sc.allowance_pos hq hq1 hG hf.positive)
variable (hQ:internalQ Q η₀≠0)(hQt:internalQ Q η₀≠⊤)
include setup hbRad hrad hc hmesh hβ hβhi hQM hLowMesh hQ hQt hwidth hbcell hr hfee hq hQ72 in
/-- The two estimates are obtained from the earlier genuine sources, with
all source constants preceding the original physical data. -/
theorem regular_some_point_source_rm (hN:Fintype.card α≤N) (high:Source)(hB0:22/23≤(high.B:ℝ))(hB1:(high.B:ℝ)≤1)(hlam:1<(high.L:ℝ))
    (hcap0:0≤(high.cap:ℝ))(hcap1:(high.cap:ℝ)<1)
    (hparent:QRH.Record12518109Existence.UnitFaceSource
      (globalFace (high.B:ℝ) (high.L:ℝ) (high.cap:ℝ)) (100*mesh) θ)
    (hgaps:∀ν∈Icc (n.q:ℝ) (3/4),ActualGaps_rm n low (some high) bcell ν reserve):
    ∃degree:ℕ,∃controls:Finset (ℕ×ℕ),(0,0)∈controls ∧
    ∃C τsource:ℝ,0<C ∧ 0<τsource ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      RegularPointAt (α:=α) M H hH W hW hWs ηanchor η₀ R₀ hR₀ Q n low
        bcell reserve θ mesh ξ width τsource N degree controls C Z:=by
  obtain ⟨bound,hb,J,SH,CH,Cslot,Cpref,JL,SL,CL,hCH,hslot,hpref,hCL,econtrols⟩:=
    regular_some_controls_rm (α:=α) (M:=M) (H:=H) (hH:=hH) (ηanchor:=ηanchor) (η₀:=η₀) (n:=n)
    (low:=low) (setup:=setup) (W:=W) (hWs:=hWs) (hW:=hW) (bRad:=bRad) (hbRad:=hbRad) (hrad:=hrad)
    (reserve:=reserve) (θ:=θ) (mesh:=mesh) (N:=N) (wmin:=wmin) (rmin:=rmin)
    (εslot:=εslot) (hf:=hf) (hc:=hc) (hmesh:=hmesh) (R₀:=R₀) (hR₀:=hR₀)
    (hβ:=hβ) (hβhi:=hβhi) (Kgraph:=Kgraph) (bcell:=bcell) (Q:=Q) (hQM:=hQM)
    (hQ:=hQ) (hQt:=hQt) (hQ72:=hQ72) (amp:=sourceAReal n low bcell) (hm:=sc.mesh_nonneg) (hamp:=sc.geometry.a_pos)
    (hg:=sc.geometry) (hn:=sc.parent) (hlow:=sc.low_parent) (ha:=sc.allowance_pos) (hqhalf:=hq) (hq1:=hq1)
    (hG:=hG) (hLowMesh:=hLowMesh) (hN:=hN) (hparent:=hparent) (high:=high) (hB0:=hB0)
    (hB1:=hB1) (hlam:=hlam) (hcap0:=hcap0) (hcap1:=hcap1)
  let P:=regularParameters W θ εslot J bound hWs hW hf.positive hc.slot_pos hb
  obtain ⟨Cpoint,hCpoint,epoint⟩:=SelectedRegularCombinedPointSome.eventually_actual_point_rm
    (M:=M) (H:=H) (hH:=hH) (ηanchor:=ηanchor) (η₀:=η₀) (n:=n)
    (low:=low) (setup:=setup) (W:=W) (hWs:=hWs) (hW:=hW) (bRad:=bRad) (hbRad:=hbRad) (hrad:=hrad)
    (Kgraph:=Kgraph) (bcell:=bcell) (reserve:=reserve) (θ:=θ) (mesh:=mesh) (ξ:=ξ)
    (width:=width) (N:=N) (wmin:=wmin) (rmin:=rmin) (εslot:=εslot) (hf:=hf)
    (hc:=hc) (sc:=sc) (hmesh:=hmesh) (hwidth:=hwidth) (hbcell:=hbcell) (hr:=hr)
    (hfee:=hfee) (hq:=hq) (R₀:=R₀) (hR₀:=hR₀) (Q:=Q) (hQM:=hQM)
    (hQ72:=hQ72) (hβ:=hβ) (hβhi:=hβhi) (hN:=hN) (hparent:=hparent) (hgaps:=hgaps)
    (bound:=bound) (hbound:=hb) (J:=J) (JL:=JL) (SL:=SL) (SH:=SH)
    (CL:=CL) (Cpref:=Cpref) (Cslot:=Cslot) (CH:=CH) (hCL:=hCL.le) (hCpref:=hpref.le)
    (hCslot:=zero_le_one.trans hslot) (hCH:=hCH.le) (high:=high) (hB0:=hB0) (hB1:=hB1) (hlam:=hlam)
    (hcap0:=hcap0) (hcap1:=hcap1)
  refine ⟨JL,regularProfileControl SL SH,Finset.mem_insert_self _ _,Cpoint,P.τ,hCpoint,P.hτ,?_⟩
  filter_upwards [econtrols,epoint] with Z hcZ hpZ
  refine ⟨hpZ.1,?_⟩
  intro hZ
  exact hpZ.2 hZ hcZ.2.1 hcZ.2.2

end
end QRH.Record1252270103Source.High.GlobalPhysical
