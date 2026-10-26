/- Literal recursive callback on the SAME selected physical common source.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeActualChild
import Candidate.Research.RecursiveAffine.NativeCommonMap

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open Cycle63FinalCapacity Cycle63Moment Cycle63InitialMass Cycle63FinalLow Cycle153Reachable Cycle153RegionalLow
open Cycle153ContinuationUnit
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

/-- This is the actual inner geometry constructor at the common allocation
selected by Columns. All remaining arguments are the genuine detector's
residual allocation, nonzero row, SAME deleted set and native finite-source
conditions. The first-column height stays inside `ch`; the final source
height is independently quantified. The return is the native package whose
`.val`, `.property.1`, and `.property.2` are the actual Column callbacks.
No child/output is chosen here, and no energy or capacity conclusion is a
premise of this constructor. -/
def actualCanonicalInnerCommonChild
    (N : ReachableNode C j) (hj : j.val<3)
    (s : Input N.slots) (ch : Chain s) (sourceCharacter : Character) (sourceHeight : ℝ)
    (n : ℕ) (b Mrow omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch N.localBase Mrow (nodeSourceAmp N) omega xi b n)
    (hb : 1 ≤ b) (hcard : Fintype.card N.slots ≤ n)
    (hs : s.upper ≤ b) (hlower : 1 ≤ s.lower)
    (hX1 : s.X₁=N.X1) (hX2 : s.X₂=N.X2)
    (hscale : ∀i,s.P i=N.localBase^(C.originalWeight i/N.unit))
    (chosenAllocation : actualAllocations (withHeight ch.first sourceCharacter sourceHeight).pools ch.E₂)
    (hadmitted : commonScalar (withHeight ch.first sourceCharacter sourceHeight)
      ch.E₂ ch.R₂ chosenAllocation ≠ 0) :=
  actual_inner_native_child_package N hj s
    (commonContinuationChain s ch sourceCharacter sourceHeight chosenAllocation)
    sourceCharacter sourceHeight n b Mrow omega xi reserve mesh
    (commonContinuationGeometry g sourceCharacter sourceHeight chosenAllocation hadmitted)
    hb hcard hs hlower hX1 hX2 hscale

/-- Changing the selected common allocation leaves the actual retained
unit unchanged. This is the exact alias used by the native Column callback,
not a new independently selected recursion scale. -/
theorem canonical_inner_common_unit
    (N : ReachableNode C j) (s : Input N.slots) (ch : Chain s)
    (sourceCharacter : Character) (sourceHeight : ℝ)
    (n : ℕ) (b Mrow omega xi reserve : ℝ)
    (g : LiveMainGeometry s ch N.localBase Mrow (nodeSourceAmp N) omega xi b n)
    (chosenAllocation : actualAllocations (withHeight ch.first sourceCharacter sourceHeight).pools ch.E₂)
    (hadmitted : commonScalar (withHeight ch.first sourceCharacter sourceHeight)
      ch.E₂ ch.R₂ chosenAllocation ≠ 0) :
    let q:=commonContinuationChain s ch sourceCharacter sourceHeight chosenAllocation
    let gg:=commonContinuationGeometry g sourceCharacter sourceHeight chosenAllocation hadmitted
    nativeUnit 1 N.localBase (nodeSourceAmp N) omega reserve xi q.C₁ gg.D₁
      gg.datum.C gg.datum.D gg.datum.inactive =
      secondNominal 1 N.localBase (nodeSourceAmp N) omega ch.C₁ g.D₁
        g.datum.C g.datum.D g.datum.inactive+(reserve+xi/2) :=by
  dsimp only [nativeUnit,commonContinuationChain,commonContinuationGeometry,LiveMainGeometry.D₁]
  ring
end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualCanonicalInnerCommonChild
#print axioms OAI.SevenEighths.Cycle153ActualColumn.canonical_inner_common_unit
