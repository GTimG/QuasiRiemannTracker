/- SAME physical Common daughter to actual inner geometry/history/mask callbacks.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalInnerCallbacks
import Candidate.Research.RecursiveAffine.NativeActualChildCoordinates
import Candidate.Research.RecursiveAffine.NativeFiniteDaughterSource

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity CenteredMomentDivisorAllocation
open Cycle153SourceReturn Cycle63FinalCapacity
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedChildCapacity
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentCommonRawScale
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained Cycle63Moment Cycle63Moment.LowBranch
open CenteredMomentAllocatedRayDictionary
open Cycle63FinalLow Cycle63InitialMass Cycle153Reachable Cycle153RegionalLow Cycle153ContinuationUnit
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

/-- The exact three callbacks of native Columns are projections of ONE
actual native arithmetic package at the SAME chosen common allocation,
residual allocation, nonzero row and detector deletion. There is no
assumed next geometry, puncture, energy, record or count. -/
def actualCanonicalInnerDaughterPackage
    (N : ReachableNode C j)(hj : j.val<3)
    (s : Input N.slots)(ch : Chain s)(sourceCharacter : Character)(sourceHeight : ℝ)
    (n : ℕ)(b Mrow omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch N.localBase Mrow (nodeSourceAmp N) omega xi b n)
    (hb : 1 ≤ b)(hcard : Fintype.card N.slots ≤ n)(hs : s.upper ≤ b)(hlower : 1 ≤ s.lower)
    (hX1 : s.X₁=N.X1)(hX2 : s.X₂=N.X2)
    (hscale : ∀i,s.P i=N.localBase^(C.originalWeight i/N.unit))
    (homega : omega=frequencyLoss N.localBase 32 xi+reserve*1)
    (hR2 : ch.R₂=N.state.puncture*ch.C₁)(hP : ch.R₂*ch.E₂≠0)
    (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
      (2*(n:ℝ)*Real.logb N.localBase b+
        Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ) ≤ positionMargin)
    (Ds : Finset (Ideal O)) :
    let firstInput:=withHeight ch.first sourceCharacter sourceHeight
    let u:=nativeUnit 1 N.localBase (nodeSourceAmp N) omega reserve xi ch.C₁ g.D₁
      g.datum.C g.datum.D g.datum.inactive
    let Daughter:=PhysicalDaughter firstInput ch.E₂ ch.R₂ Ds
    let src:=fun d : Daughter=>commonData firstInput ch.E₂ ch.R₂ d.1
    let J:=fun d : Daughter=>(CenteredMomentDivisorRaw.liveIndices d.2.1.1 d.2.2.1.1).map
      ((originalEmbedding ch.first ch.E₂ d.1).trans (originalEmbedding s ch.C₁ ch.B₁))
    ∀(d : Daughter)(hn : commonScalar firstInput ch.E₂ ch.R₂ d.1≠0)
      (row : O)(hne : Cycle63.Physical.sourcePositiveRow (src d).toSource
        d.2.2.2 d.2.1.1 d.2.2.1.1 row≠0)
      (R : Finset N.slots)(hR : R⊆J d)
      (hsum : (∑i∈R,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+mesh)
      (hcover : R=J d ∨ nodeDetectorDeletion N ≤ ∑i∈R,C.originalWeight i/N.unit)
      (hc : nativeMainContinuation N.state u (J d) R (fun i=>C.originalWeight i/N.unit)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1)),
    {geom : NativeChildGeometry C (nextInner j hj) N.localBase N.unit u
        (((J d\R).map (originalSubsetEmbedding N.slots)))
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1) //
      Real.logb C.globalBase ((ch.R₂*ch.E₂).absNorm:ℝ) ≤
        modelMissing (nextInner j hj) geom.coordinates+modelReduction (nextInner j hj) geom.coordinates+
          (((nextInner j hj).val:ℝ)+1)/1000000000000000 ∧
      ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ (N.localBase^u)^(20:ℝ)} :=by
  intro firstInput u Daughter src J d hn row hne R hR hsum hcover hc
  let q:=commonContinuationChain s ch sourceCharacter sourceHeight d.1
  let gg:=commonContinuationGeometry g sourceCharacter sourceHeight d.1 hn
  exact actual_inner_native_child_package N hj s q sourceCharacter sourceHeight n b Mrow omega xi reserve mesh gg
    hb hcard hs hlower hX1 hX2 hscale d.2.2.2 d.2.1.1 d.2.2.1.1 row hne R hR hc.2.1 hcover hsum
    homega hR2 hP hfinite hc hgrid

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualCanonicalInnerDaughterPackage
