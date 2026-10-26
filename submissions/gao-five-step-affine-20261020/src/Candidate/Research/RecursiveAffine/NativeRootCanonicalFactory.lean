/- Actual source gates used by the bare ROOT canonical LOW producer.
Copyright (c)2026 Zhongpai Gao. Native source estimates by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootCommonCallbacks
import Candidate.Research.RecursiveAffine.NativeRootCanonicalUnit
import Candidate.Research.RecursiveAffine.ActualRootNativeFee
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineLowPayment
import Candidate.Cycle63.Physical.InitialMass.SecondSourceControls

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentEnergyBands CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open Cycle63Moment Cycle63InitialMass Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity Cycle153Reachable Cycle153RegionalLow
open CenteredMomentAllocatedChildCapacity CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSlotRatios CenteredMomentEligibleEnergy CenteredMomentFirstChildProfileControl
open Cycle153ContinuationUnit Cycle153SourceSchedule Cycle153RootStep
open Cycle63FinalNatural
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}
noncomputable local instance actualRootCanonicalFactoryLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger

/-- The literal common-source allowance is paid by the SAME measured
source pad used in the actual arithmetic edge. There is no second detached
column pad and no fixed asymptotic allowance is substituted into the edge. -/
theorem actual_root_common_allowance
    (s : Input alpha)(p : Profiles (1/4) (9/4))(Cs : ℝ)
    (caps : GeometryAffineLowSourceGates s p Cs C.globalBase)
    (ch : Chain s)(sourceCharacter : Character)(sourceHeight : ℝ)
    (B : actualAllocations (withHeight ch.first sourceCharacter sourceHeight).pools ch.E₂) :
    (commonData (withHeight ch.first sourceCharacter sourceHeight) ch.E₂ ch.R₂ B).toSource.allowance
      C.globalBase ≤ actualRootSourcePad C s :=by
  let src:=commonData (withHeight ch.first sourceCharacter sourceHeight) ch.E₂ ch.R₂ B
  have hlog : Real.log 2 ≤ 2*Real.log (9/4:ℝ) :=by
    have hh:=Real.log_le_log (by norm_num : (0:ℝ)<2)
      (by norm_num : (2:ℝ)≤(9/4)*(9/4))
    rw [Real.log_mul (by norm_num : (9/4:ℝ)≠0) (by norm_num : (9/4:ℝ)≠0)] at hh
    linarith only [hh]
  have hbound:=fixed_source_allowance (Fintype.card alpha) (2*Real.log (9/4:ℝ)) (9/4)
    (by positivity) (by norm_num) src
    ((live_card_le B.val).trans (live_card_le ch.B₁.val))
    (fun i=>(caps.windows i.val.val).trans hlog)
    (by exact le_of_eq caps.b₁) (by exact le_of_eq caps.b₂)
    C.globalBase C.globalBase_gt_one
  have hclip : 0 ≤ Cycle63.Physical.plainClipAllowance C.globalBase ![src.b₁,src.b₂] :=by
    unfold Cycle63.Physical.plainClipAllowance
    exact Finset.sum_nonneg (fun k _=>Real.logb_nonneg C.globalBase_gt_one (le_max_left _ _))
  have heq : (((Fintype.card alpha:ℝ)*(2*Real.log (9/4:ℝ))+2*Real.log (9/4:ℝ))/
      Real.log C.globalBase)=actualRootSourcePad C s :=by
    unfold actualRootSourcePad
    rw [caps.b₁,caps.b₂]
    norm_num only [max_eq_right (by norm_num : (1:ℝ)≤9/4)]
    unfold Real.logb
    rw [show (81/16:ℝ)=(9/4)*(9/4) by norm_num]
    rw [Real.log_mul (by norm_num : (9/4:ℝ)≠0) (by norm_num : (9/4:ℝ)≠0)]
    ring
  rw [heq] at hbound
  exact le_trans (le_add_of_nonneg_right hclip) hbound

/-- The native live-source theorem supplies its actual width ceiling.
Supported common data makes this ceiling at most one even on a direct or
zero branch; no continuing child is needed for that bound. -/
theorem actual_root_source_unit
    (C : SourceContext (α:=alpha) M H)(s : Input alpha)(ch : Chain s)
    (omega xi reserve b : ℝ)(budget : ℕ)
    (g : LiveMainGeometry s ch C.globalBase 1 (rootSourceAmp C.originalWeight) omega xi b budget)
    (hamp : 0 ≤ rootSourceAmp C.originalWeight)(hb : 0<b)
    (sourceRay : RayFourExpansion.RayCharacter)(Q : Ideal O)
    (hP : ch.R₂*ch.E₂≠0)(hPN : ((ch.R₂*ch.E₂).absNorm:ℝ)≤C.globalBase^(28:ℝ))
    (hfit : 1+Real.logb C.globalBase (s.η.modulus.absNorm:ℝ)≤1+reserve/2)
    (hconstants : Real.logb C.globalBase CenteredMomentFirstPhysicalSource.fixedPresentationCost+
      2*(budget:ℝ)*Real.logb C.globalBase b+Real.logb C.globalBase 1+
      Real.logb C.globalBase (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤reserve/2)
    (homega : omega=frequencyLoss C.globalBase 32 xi+reserve) :
    let st:=retainedState C.globalBase 28 C.globalBase_gt_one (g.datum.τ sourceRay) Q
      (ch.R₂*ch.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let u:=nativeUnit 1 C.globalBase (rootSourceAmp C.originalWeight) omega reserve xi ch.C₁ g.D₁
      g.datum.C g.datum.D g.datum.inactive
    st.width≤u ∧ u≤1 ∧ st.width≤2 :=by
  intro st u
  have hh:=actual_native_unit (U:=1) g 28 C.globalBase_gt_one hb sourceRay Q hP hPN
    (by simpa only [mul_one,div_mul_eq_mul_div] using hfit)
    (by simpa only [mul_one] using hconstants) (by simpa only [mul_one] using homega)
  have hv : 0≤commonWidthLoss C.globalBase ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive :=by
    have hcommon:=CenteredMomentSecondActualWidth.actual_common_log_ge_unit
      g.datum.C g.datum.D g.datum.hC g.datum.inactive C.globalBase C.globalBase_gt_one
    unfold commonWidthLoss
    linarith only [hcommon,le_max_right
      (Real.logb C.globalBase (ch.C₁.absNorm:ℝ)-Real.logb C.globalBase (g.D₁.absNorm:ℝ)) 0]
  have hu : u≤1 :=by
    have ht:=hh.2.2
    have he:=hh.2.1
    dsimp only [u] at *
    linarith only [he,hv,ht,hamp]
  exact ⟨hh.1,hu,hh.1.trans (hu.trans (by norm_num))⟩

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_root_common_allowance
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_root_source_unit
