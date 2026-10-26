/- SAME physical Common daughter to actual root geometry/history/mask callbacks.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeCanonicalRootPackagePort
import Candidate.Research.RecursiveAffine.NativeRootCanonicalUnit
import Candidate.Research.RecursiveAffine.NativeFiniteDaughterSource
import Candidate.Research.RecursiveAffine.NativeRootFieldwiseTransport
import Candidate.Research.RecursiveAffine.NativeActualRootCoordinates

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentEnergyState Cycle63FinalNatural
open CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity CenteredMomentDivisorAllocation
open Cycle153SourceReturn Cycle63FinalCapacity
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedChildCapacity
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentCommonRawScale
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained Cycle63Moment Cycle63Moment.LowBranch
open CenteredMomentAllocatedRayDictionary
open CenteredMomentEnergyState Cycle63FinalNatural
open CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyBands
open Cycle63FinalLow Cycle63InitialMass Cycle153Reachable Cycle153RegionalLow Cycle153ContinuationUnit
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}
noncomputable local instance rootCoordinateReceiptLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
open Cycle153RootStep

def actualCanonicalRootCoordinateReceipt
    (C : SourceContext (α:=alpha) M H)
    (s : Input alpha)(ch : Chain s)(sourceCharacter : Character)(sourceHeight : ℝ)
    (n : ℕ)(b omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch C.globalBase 1 (rootSourceAmp C.originalWeight) omega xi b n)
    (hb : 1 ≤ b)(hcard : Fintype.card alpha ≤ n)(hs : s.upper ≤ b)(hlower : 1 ≤ s.lower)
    (hscale : ∀i,s.P i=C.globalBase^(C.originalWeight i))
    (hwindow : Cycle63.AffineLedger.PlainWindow
      (length C.globalBase s.X₁) (length C.globalBase s.X₂) (∑i,C.originalWeight i))
    (homega : omega=frequencyLoss C.globalBase 32 xi+reserve*1)
    (hR2 : ch.R₂=(1:Ideal O)*ch.C₁)(hP : ch.R₂*ch.E₂≠0)
    (hfinite : Real.logb C.globalBase 128+
      (2*(n:ℝ)*Real.logb C.globalBase b+
        Real.logb C.globalBase (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ) ≤ positionMargin)
    (Bmask : ℝ)(st : NaturalState C.globalBase Bmask 2)
    (Ds : Finset (Ideal O)) :
    let firstInput:=withHeight ch.first sourceCharacter sourceHeight
    let u:=nativeUnit 1 C.globalBase (rootSourceAmp C.originalWeight) omega reserve xi ch.C₁ g.D₁
      g.datum.C g.datum.D g.datum.inactive
    let Daughter:=PhysicalDaughter firstInput ch.E₂ ch.R₂ Ds
    let src:=fun d : Daughter=>commonData firstInput ch.E₂ ch.R₂ d.1
    let J:=fun d : Daughter=>(CenteredMomentDivisorRaw.liveIndices d.2.1.1 d.2.2.1.1).map
      ((originalEmbedding ch.first ch.E₂ d.1).trans (originalEmbedding s ch.C₁ ch.B₁))
    ∀(d : Daughter)(hn : commonScalar firstInput ch.E₂ ch.R₂ d.1≠0)
      (row : O)(hne : Cycle63.Physical.sourcePositiveRow (src d).toSource
        d.2.2.2 d.2.1.1 d.2.2.1.1 row≠0)
      (R : Finset alpha)(hR : R⊆J d)
      (hsum : (∑i∈R,C.originalWeight i/1) ≤ rootDetectorDeletion C.originalWeight+mesh)
      (hcover : R=J d ∨ rootDetectorDeletion C.originalWeight ≤ ∑i∈R,C.originalWeight i/1)
      (hc : nativeMainContinuation st u (J d) R (fun i=>C.originalWeight i/1)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1)),
    let nextChain:=commonContinuationChain s ch sourceCharacter sourceHeight d.1
    let nextGeometry:=commonContinuationGeometry g sourceCharacter sourceHeight d.1 hn
    let step:=nativeRootStepValues s nextChain sourceCharacter sourceHeight C.globalBase n b 1 omega xi reserve
      C.originalWeight nextGeometry d.2.2.2 d.2.1.1 d.2.2.1.1 R
    {geom : NativeChildGeometry C (0:Fin 4) C.globalBase 1 u
        ((J d\R).map (Function.Embedding.refl alpha))
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
        (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1) //
      Real.logb C.globalBase ((ch.R₂*ch.E₂).absNorm:ℝ) ≤
        modelMissing (0:Fin 4) geom.coordinates+modelReduction (0:Fin 4) geom.coordinates+
          (((0:Fin 4).val:ℝ)+1)/1000000000000000 ∧
      ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ (C.globalBase^u)^(20:ℝ) ∧
      geom.coordinates=rootCoordinates step.b step.rootSlack step.V step.Red step.ell} :=by
  intro firstInput u Daughter src J d hn row hne R hR hsum hcover hc nextChain nextGeometry step
  let q:=nextChain
  let gg:=nextGeometry
  have hsum0 : (∑i∈R,C.originalWeight i)≤rootDetectorDeletion C.originalWeight+mesh:=by
    simpa only [div_one] using hsum
  have hcover0 : R=J d ∨ rootDetectorDeletion C.originalWeight≤∑i∈R,C.originalWeight i:=by
    simpa only [div_one] using hcover
  have hc0 : nativeMainContinuation st u (J d) R C.originalWeight
      (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 0)
      (rawDaughterScale (src d) d.2.2.2 d.2.1.1 d.2.2.1.1 1):=by
    simpa only [div_one] using hc
  let pack:=actual_root_native_child_package C s q sourceCharacter sourceHeight n b omega xi reserve mesh gg
    hb hcard hs hlower hscale hwindow d.2.2.2 d.2.1.1 d.2.2.1.1 row hne R hR hcover0 hsum0
    homega hR2 hP hfinite hgrid Bmask st hc0
  have hu : (nativeRootStepValues s q sourceCharacter sourceHeight C.globalBase n b 1 omega xi reserve
      C.originalWeight gg d.2.2.2 d.2.1.1 d.2.2.1.1 R).u=u:=by
    dsimp only [nativeRootStepValues,commonContinuationChain,commonContinuationGeometry,LiveMainGeometry.D₁]
    rfl
  have hi : q.indices d.2.1.1 d.2.2.1.1=J d:=rfl
  have hsourceEq : q.final sourceCharacter sourceHeight=src d:=rfl
  have hp : q.R₂*q.E₂=ch.R₂*ch.E₂:=rfl
  have h1:=congrArg (fun src=>rawDaughterScale src d.2.2.2 d.2.1.1 d.2.2.1.1 0) hsourceEq
  have h2:=congrArg (fun src=>rawDaughterScale src d.2.2.2 d.2.1.1 d.2.2.1.1 1) hsourceEq
  let transported:=rootPackageFieldwiseTransport hu
    ((congrArg (fun K=>K\R) hi).trans Finset.map_refl.symm) h1 h2 hp pack
  have coords : pack.val.coordinates=rootCoordinates step.b step.rootSlack step.V step.Red step.ell:=
    actual_root_native_child_package_coordinates C s q sourceCharacter sourceHeight n b omega xi reserve mesh gg
      hb hcard hs hlower hscale hwindow d.2.2.2 d.2.1.1 d.2.2.1.1 row hne R hR hcover0 hsum0
      homega hR2 hP hfinite hgrid Bmask st hc0
  refine ⟨transported.val,?_,?_,?_⟩
  · simpa only [Fin.val_zero,Nat.cast_zero,zero_add] using transported.property.1
  · exact transported.property.2
  · exact coords
end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualCanonicalRootCoordinateReceipt
