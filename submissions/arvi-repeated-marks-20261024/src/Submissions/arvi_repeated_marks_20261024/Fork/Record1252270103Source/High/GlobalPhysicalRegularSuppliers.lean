/- Repeated marks: fork of Record1252270103Source.High.GlobalPhysicalRegularSuppliers (Hailey Collet, Apache-2.0; inherited notices retained).
Only the declarations whose statement depends on the HIGH gain, the uniform detector
cutoff or the source validity are restated, renamed `*_rm`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalRegularSuppliers
import Submissions.arvi_repeated_marks_20261024.Source.GainC
import Submissions.arvi_repeated_marks_20261024.Source.CountWrappersK
import Submissions.arvi_repeated_marks_20261024.Source.GainPaymentK
import Submissions.arvi_repeated_marks_20261024.Source.PaymentWrappersK
import Submissions.arvi_repeated_marks_20261024.Source.WitnessWrappersK
import Submissions.arvi_repeated_marks_20261024.Finite.SourceValid2
import Submissions.arvi_repeated_marks_20261024.Fork.Record1252270103Source.High.GlobalPhysicalRegularPoints
import Submissions.arvi_repeated_marks_20261024.Fork.Record1252270103Source.Admission.SelectedRegularCombinedPointSome
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
local instance regularSuppliersDecEq_rm {ι : Type*} : DecidableEq ι := Classical.decEq _
local notation "O" => HeckeFamily.O

open SelectedRegularHighPoint CenteredMomentEnergyBands
open OAI OAI.SevenEighths
open scoped Classical BigOperators ContDiff
open HeckeFamily ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondInputCapacitySource Cycle61Moment LocalMoment
open PhysicalAnalytic Record1252270103Finite
open Set Filter Admission
open High.GlobalPhysical SelectedRegularHighPoint SelectedRegularSourceData SelectedHighCofactorFamily
open SelectedRegularCombinedPoint SelectedRegularLowPoint CenteredMomentSourceMass
open CenteredMomentFirstAmplificationChoice CenteredMomentSourceMass
open Record1252270103StepScalar QRH.Record1252270103Graph CenteredMomentLogDyadic
open SelectedRegularCanonicalAbsolute
local instance regularSuppliersFinite_rm (M:Ideal O)[NeZero M]:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

open InitialRegularToTruncated
variable (Kgraph:ℚ)(n low:Source)(bcell reserve θ mesh ξ width:ℝ)
variable (hf:FixedBudget reserve 100 100 1 θ)(sc:Scalar Kgraph n low bcell θ mesh ξ width)
variable (hmesh:100*mesh≤θ)(hwidth:width≤θ)(hbcell:bcell≤1)
variable (hr:reserve≤(n.allowance:ℝ))(hfee:0≤(n.highFee:ℝ))
variable (hq:(1/2:ℝ)≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
variable (hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))
variable (hLowMesh:mesh≤regularLowMesh Kgraph n low bcell θ sc.geometry sc.parent sc.low_parent
  sc.allowance_pos hq hq1 hG hf.positive)
variable (hβ:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hβhi:HeckeZeroSupremum.beta≤7/8)

include hf sc hmesh hwidth hbcell hr hfee hq hq1 hG hLowMesh hβ hβhi in
theorem regular_supplier_some_rm (hmeshamp:mesh<sourceAReal n low bcell/2)
    (high:Source)(hB0:22/23≤(high.B:ℝ))(hB1:(high.B:ℝ)≤1)(hlam:1<(high.L:ℝ))
    (hcap0:0≤(high.cap:ℝ))(hcap1:(high.cap:ℝ)<1)
    (hparent:QRH.Record12518109Existence.UnitFaceSource
      (globalFace (high.B:ℝ) (high.L:ℝ) (high.cap:ℝ)) (100*mesh) θ)
    (hgaps:∀ν∈Icc (n.q:ℝ) (3/4),ActualGaps_rm n low (some high) bcell ν reserve):
    RegularJointSupplier Kgraph n low bcell mesh ξ θ width:=by
  apply regular_supplier_of_points Kgraph n low bcell reserve θ mesh ξ width hf sc.geometry sc.parent
    sc.xi_pos (sc.xi_loss.trans (hf.small.trans (by norm_num))) sc.mesh_nonneg hmeshamp
  intro α _ M _ H hH W hW hWs ηanchor η₀ Q hQM hQ hQt hQ72 R₀ hR₀
  obtain ⟨wmin,rmin,εslot,hc⟩:=cardinality_loss_exists θ 100 100 1 1 hf.positive
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Fintype.card α)
  obtain ⟨bRad₀,hbRad₀,hsRad⟩:=CenteredMomentDetectorEnergyInitialState.radialMajorant_support_bound
  let bRad:=max 2 bRad₀
  have hbRad:2≤bRad:=le_max_left _ _
  have hrad:Function.support (CenteredMomentDetectorPlainFiberSource.radialMajorant:ℝ→ℂ)⊆Iic bRad:=
    by
      intro x hx
      change x≤bRad
      exact (show x≤bRad₀ from hsRad hx).trans (le_max_right 2 bRad₀)
  let setup:=OAI.SevenEighths.LocalMoment.canonicalDensityCountingSetup
  exact regular_some_point_source_rm (α:=α)
    (M:=M) (H:=H) (hH:=hH) (ηanchor:=ηanchor) (η₀:=η₀) (n:=n) (low:=low)
    (setup:=setup) (W:=W) (hWs:=hWs) (hW:=hW) (bRad:=bRad) (hbRad:=hbRad) (hrad:=hrad)
    (Kgraph:=Kgraph) (bcell:=bcell) (reserve:=reserve) (θ:=θ) (mesh:=mesh) (ξ:=ξ)
    (width:=width) (N:=Fintype.card α) (wmin:=wmin) (rmin:=rmin) (εslot:=εslot)
    (hf:=hf) (hc:=hc) (sc:=sc) (hmesh:=hmesh) (hwidth:=hwidth) (hbcell:=hbcell)
    (hr:=hr) (hfee:=hfee) (hq:=hq) (R₀:=R₀) (hR₀:=hR₀) (Q:=Q) (hQM:=hQM)
    (hQ72:=hQ72) (hβ:=hβ) (hβhi:=hβhi) (hq1:=hq1) (hG:=hG) (hLowMesh:=hLowMesh)
    (hQ:=hQ) (hQt:=hQt)
    (hN:=le_refl _) high hB0 hB1 hlam hcap0 hcap1 hparent hgaps

end
end QRH.Record1252270103Source.High.GlobalPhysical
