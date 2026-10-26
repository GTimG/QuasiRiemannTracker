/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.PhysicalChildContinuation
import Candidate.Research.RecursiveAffine.NativeNodeStepRebase
import Candidate.Research.RecursiveAffine.NativeStrictLowStep

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentCommonProfile
open CenteredMomentCommonRawScale CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedChildCapacity
open CenteredMomentDivisorRaw CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentSourceLiveColumn CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open Cycle63InitialMass Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity
open Cycle63Moment.LowBranch Cycle153RegionalLow Cycle153ContinuationUnit
open Cycle153Geometry Cycle153ReachableGeometry Cycle63.Optimization

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=α) M H} {j : Fin 4}

/-- Finite set difference does not depend on the equality algorithm.
Keep the finite carrier fixed before comparing those algorithms. -/
theorem native_sdiff_decEq {ι : Type*} (d1 d2 : DecidableEq ι) (S T : Finset ι) :
    @sdiff (Finset ι) (@Finset.instSDiff _ d1) S T=
      @sdiff (Finset ι) (@Finset.instSDiff _ d2) S T := by
  cases Subsingleton.elim d1 d2
  rfl

/-- Construct the actual child geometry and puncture from the SAME
native live geometry, selected residual allocation and detector deletion.
The capacity and history inputs are proved internally from the physical
source. No next-source facts, energy or returned-family bound is assumed. -/
def actual_inner_native_child_package (N : ReachableNode C j) (hj : j.val<3)
    (s : Input N.slots) (ch : Chain s) (χ : Character) (t : ℝ)
    (n : ℕ) (b Mrow omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch N.localBase Mrow (nodeSourceAmp N) omega xi b n)
    (hb : 1 ≤ b) (hcard : Fintype.card N.slots ≤ n)
    (hs : s.upper ≤ b) (hlower : 1 ≤ s.lower)
    (hX₁ : s.X₁=N.X1) (hX₂ : s.X₂=N.X2)
    (hscale : ∀i,s.P i=N.localBase^(C.originalWeight i/N.unit))
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (row : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final χ t).toSource second L alloc row≠0)
    (Rdel : Finset N.slots) (hRdel : Rdel ⊆ ch.indices L alloc) (hproper : Rdel≠ch.indices L alloc)
    (hcover : Rdel=ch.indices L alloc ∨ nodeDetectorDeletion N ≤ ∑i∈Rdel,C.originalWeight i/N.unit)
    (hdelmesh : (∑i∈Rdel,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+mesh)
    (homega : omega=frequencyLoss N.localBase 32 xi+reserve*1)
    (hR₂ : ch.R₂=N.state.puncture*ch.C₁) (hPuncture : ch.R₂*ch.E₂≠0)
    (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
      (2*(n:ℝ)*Real.logb N.localBase b+
        Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000)
    (hcontinue : let r := nativeNodeStepValues N s ch χ t n b Mrow omega xi reserve g second L alloc Rdel
      Cycle153RegionalLow.nativeMainContinuation N.state r.u (ch.indices L alloc) Rdel
        (fun i=>C.originalWeight i/N.unit)
        (rawDaughterScale (ch.final χ t) second L alloc 0)
        (rawDaughterScale (ch.final χ t) second L alloc 1))
    (hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin) :
    let r := nativeNodeStepValues N s ch χ t n b Mrow omega xi reserve g second L alloc Rdel
    let slots := nativeSurvivingSlots N.slots (ch.indices L alloc) Rdel
    {geom : NativeChildGeometry C (nextInner j hj) N.localBase N.unit r.u slots
        (rawDaughterScale (ch.final χ t) second L alloc 0)
        (rawDaughterScale (ch.final χ t) second L alloc 1) //
      Real.logb C.globalBase ((ch.R₂*ch.E₂).absNorm:ℝ)≤
        modelMissing (nextInner j hj) geom.coordinates+modelReduction (nextInner j hj) geom.coordinates+
          (((nextInner j hj).val:ℝ)+1)/1000000000000000 ∧
      ((ch.R₂*ch.E₂).absNorm:ℝ)≤(N.localBase^r.u)^(20:ℝ)} := by
  intro r slots
  have step := actual_inner_native_node_step N s ch χ t n b Mrow omega xi reserve mesh g
    hb hcard hs hlower hX₁ hX₂ hscale second L alloc row hne Rdel hRdel hproper hcover hdelmesh
    homega hR₂ hPuncture hfinite
  change 0≤r.V ∧ 0≤r.Red ∧ 0≤r.ell ∧
    N.unit*r.u=N.unit-6*modelAmplification j N.coordinates-r.V ∧
    r.childSlots=modelSlots j N.coordinates-pathDeletion j.val N.coordinates-r.ell ∧
    r.childA=modelLength j N.coordinates-pathDeletion j.val N.coordinates-r.V-r.Red ∧
    r.ell≤r.V+r.Red+r.pad ∧
    Real.logb C.globalBase ((ch.R₂*ch.E₂).absNorm:ℝ)≤
      Real.logb C.globalBase (N.state.puncture.absNorm:ℝ)+r.V+r.Red+r.pad ∧
    r.pad≤1/100000000000000000000 at step
  have hV:=step.1
  have hRed:=step.2.1
  have hell:=step.2.2.1
  have hU:=step.2.2.2.1
  have hSlots:=step.2.2.2.2.1
  have hA:=step.2.2.2.2.2.1
  have hPaid:=step.2.2.2.2.2.2.1
  have hInc:=step.2.2.2.2.2.2.2.1
  have hPad:=step.2.2.2.2.2.2.2.2
  have hm := hcontinue
  have hDec : Cycle153RegionalLow.strictCurrentDecidableEq (Current:=N.slots)=
      (inferInstance : DecidableEq N.slots) := Subsingleton.elim _ _
  have hdiff :
      @sdiff (Finset N.slots) (@Finset.instSDiff _ (Cycle153RegionalLow.strictCurrentDecidableEq (Current:=N.slots)))
        (ch.indices L alloc) Rdel = ch.indices L alloc\Rdel := by
    exact native_sdiff_decEq _ _ (ch.indices L alloc) Rdel
  simp only [nativeMainContinuation,hdiff] at hm
  change (397/1000:ℝ)≤r.u ∧ _ at hm
  have hu : 0<r.u := lt_of_lt_of_le (by norm_num) hm.1
  have hamp : 0≤ modelAmplification j N.coordinates := by
    have hr : RawPrefixRows j N.coordinates := by
      intro i hi _ _
      exact N.prefixRows i (by simpa only [Nat.add_assoc] using hi)
    have ha := raw_prefix_amplifier_nonneg j N.coordinates hr
    fin_cases j <;> exact ha
  have hu1 : r.u≤1 := by nlinarith only [hU,hamp,hV,N.unit_pos]
  have hRebase := actual_native_child_length_rebase N s ch χ t n b Mrow omega xi reserve
    g second L alloc Rdel hu
  change (∑i : slots,C.originalWeight i)=r.childSlots ∧ _ at hRebase
  have hlocalSlots : (∑i : slots,C.originalWeight i)/N.unit=
      ∑i∈ch.indices L alloc\Rdel,C.originalWeight i/N.unit := by
    rw [hRebase.1]
    change (∑i∈ch.indices L alloc\Rdel,C.originalWeight i)/N.unit=_
    exact Finset.sum_div _ _ _
  have hLen : N.unit*(length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 0)+
      length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 1))+
      (∑i : slots,C.originalWeight i)=
        modelLength j N.coordinates-pathDeletion j.val N.coordinates-r.V-r.Red := by
    calc
      _ = (N.unit*r.u)*(length (N.localBase^r.u) (rawDaughterScale (ch.final χ t) second L alloc 0)+
        length (N.localBase^r.u) (rawDaughterScale (ch.final χ t) second L alloc 1)+
        ∑i : slots,C.originalWeight i/(N.unit*r.u)) :=
          (native_total_length_rebase (fun i : slots=>C.originalWeight i)
            N.localBase_gt_one N.unit_pos hu).symm
      _ = r.childA := hRebase.2
      _ = _ := hA
  have hNotOld := hm.2.2.1
  have hNotReflect := hm.2.2.2
  have hNotOld' : r.u<length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 0)+
      length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 1)+
      6*slotPrice*((∑i : slots,C.originalWeight i)/N.unit) := by
    simpa only [hlocalSlots,hDec] using hNotOld
  have hNotReflect' : ¬(length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 0)+
      length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 1)+
      6*slotPrice*((∑i : slots,C.originalWeight i)/N.unit)≤r.u+19/5000 ∧
      (max 0 (r.u-length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 1)+1/10000)+
        length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 0)+
        6*slotPrice*((∑i : slots,C.originalWeight i)/N.unit)+19/5000≤r.u ∨
       max 0 (r.u-length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 0)+1/10000)+
        length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 1)+
        6*slotPrice*((∑i : slots,C.originalWeight i)/N.unit)+19/5000≤r.u)) := by
    simpa only [hlocalSlots,hDec] using hNotReflect
  let geom := childGeometryOfActualContinuation N hj r.u r.V r.Red r.ell slots
    (rawDaughterScale (ch.final χ t) second L alloc 0)
    (rawDaughterScale (ch.final χ t) second L alloc 1) hV hRed hell hu1 hU hLen
    (hRebase.1.trans hSlots) (by linarith only [hPaid,hPad]) hm.1 hNotOld' hNotReflect' hgrid
  have hcoords : geom.coordinates=extendCoordinates N.coordinates (nextInner j hj) r.V r.Red r.ell := rfl
  have hHistory : Real.logb C.globalBase ((ch.R₂*ch.E₂).absNorm:ℝ)≤
      modelMissing (nextInner j hj) geom.coordinates+modelReduction (nextInner j hj) geom.coordinates+
        (((nextInner j hj).val:ℝ)+1)/1000000000000000 := by
    rw [hcoords]
    exact actual_continuation_puncture_history N hj r.V r.Red r.ell r.pad (ch.R₂*ch.E₂)
      hInc (by linarith only [hPad])
  have hMask := actual_child_mask_of_history C (nextInner j hj) geom.coordinates
    (N.unit*r.u) geom.unit_eq (ch.R₂*ch.E₂) hPuncture geom.prefixRows hHistory
  have hBase : C.globalBase^(N.unit*r.u)=N.localBase^r.u := by
    rw [N.localBase_eq,←Real.rpow_mul (zero_lt_one.trans C.globalBase_gt_one).le]
  rw [hBase] at hMask
  exact ⟨geom,hHistory,hMask⟩

end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_inner_native_child_package
