/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Original finite marked arrays enter the same actual divided canonical source.
Every bound below is inherited from the physical restoration data. -/
import Candidate.C092.transport.ActualStageFrameBudgetStage
import Candidate.C092.transport.ActualRootFrameHitCanonical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.ActualStageFrameBudget
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentFiniteProfileExceptional
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedPrincipalWindow MixedCanonicalSource
open NativeMaskedEnergy RestoredRootDictionary RestoredInitialSource
open QRH.SilDensitySplit.CubeFree.FP.RestorationFamily
open QRH.SilDensitySplit.CubeFree.FP.RestorationCollisionEnergy
open Candidate.FourthPower.KernelCollisionEnergy
open Candidate.FourthPower.NativeFiniteHoles
open QRH.Cycle092.OrderedPairActualRestored QRH.Cycle092.FixedFramePacking
open QRH.Cycle092.TwistedRawBallRootProducer QRH.Cycle092.ActualRootFrameHit
open RepairedSourceSideSupply
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O
variable {Slot:Type} [Fintype Slot]

/-- This package records only literal physical metadata, with the original
slot-count bound. It contains no frame or energy estimate. -/
structure EarlierRestoredIntake {ι:Type} [Fintype ι] (M:Id) [NeZero M]
    (Hr:Subgroup (O⧸M)ˣ) (r:RestoredRootSource.Data M Hr ι)
    (N:ℕ) (mesh height l t₁ Kslot:ℝ) : Prop where
  count : Fintype.card ι ≤ N
  smooth : ContDiff ℝ ∞ r.W
  Lcap : r.Lcap=8
  pitch : r.t=t₁
  slots : RestoredRootSource.slotBound r.W r.hW r.hWs ≤ Kslot
  wmesh : ∀i,r.w i ≤ mesh
  frequency : ∀i,|r.freq i| ≤ height
  holes : ∀i,(r.R₀ i).card ≤ 2*N
  width : (∑i,r.w i) ≤ l

/-- Collision blocks and inverse frozen marks preserve the original first
presentation, pitches and width. The injective marked tuple need not be
replaced by a new descriptor family. -/
theorem earlier_restored_intake
    (M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)
    (Z:ℝ)(hZ:1<Z)(W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)
    (hWs:Function.support W⊆Set.Icc (1:ℝ) 2)
    (base η₁:Character)(T:Finset Slot)(θ:Slot→RayQuotient.Characters M Hr)
    (w freq:Slot→ℝ)(mesh height l t₁ Kslot:ℝ)
    (hw:∀i,0 ≤ w i)(hwm:∀i,w i ≤ mesh)(hmesh:mesh ≤ 1/6)
    (hfreq:∀i,|freq i| ≤ height)(hwidth:(∑i∈T,w i) ≤ l)
    (hslots:RestoredRootSource.slotBound W hW.continuous hWs ≤ Kslot)
    (p:Profiles (1/4) (9/4))(r:Setoid T)
    (tc:{q // ¬singletonBlock r q}→primeEnclosure Z)
    (A:Finset {q // singletonBlock r q})(ti:A→primeEnclosure Z) :
    let data:=restoredMarksData M Hr Z hZ W hW.continuous hWs base η₁
      (fun i:T=>θ i.val) (fun i:T=>w i.val) (fun i:T=>freq i.val)
      (fun i=>hw i.val) (fun i=>(hwm i.val).trans hmesh) t₁ p r tc A ti
    EarlierRestoredIntake M Hr data (Fintype.card Slot) mesh height l t₁ Kslot := by
  intro data
  have hcount:Fintype.card (remainingSet r A) ≤ Fintype.card Slot:=
    root_slot_card (⟨T,remainingSet r A⟩:RootShape Slot)
  have hT:Fintype.card T ≤ Fintype.card Slot:=by
    simpa only [Fintype.card_coe] using Finset.card_le_univ T
  refine ⟨hcount,hW,rfl,rfl,hslots,?_,?_,?_,?_⟩
  · intro i
    exact hwm i.val.val
  · intro i
    exact hfreq i.val.val
  · intro i
    exact actual_restoration_holes (Fintype.card Slot) hT r Z tc A ti
  · exact (actual_survivor_width r A (fun i:T=>w i.val) (fun i=>hw i.val)).trans
      (by simpa only [Finset.sum_coe_sort] using hwidth)

/-- Canonicality and power scales are exact fields of the actual divided
source, independently of the size or ordering of the reference companion. -/
theorem earlier_divided_canonical {ι:Type} [Fintype ι]
    (M:Id)[NeZero M](Hr:Subgroup (O⧸M)ˣ)(hHr:RayOrthogonality.globalUnits M ≤ Hr)
    (r:RestoredRootSource.Data M Hr ι)(hL:r.Lcap=8)
    (X₁ X₂ Y₁ Y₂ t₁ t₂:ℝ)(d:IdealPair)(g:DividedLengths r.Z X₁ X₂ Y₁ Y₂ d) :
    let s:=dividedCanonicalSource M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g
    MixedFirstActualNonexceptional.Canonical M Hr hHr r.W 16 8 r.Z r.η₀ r.θ r.w
      (fun _=>33/50) r.freq r.t r.R₀ s ∧ (∀i,s.P i=r.Z^(r.w i)) ∧
      s.H=∅ ∧ s.R=1 ∧ s.d=(1,1) := by
  intro s
  exact ⟨by simpa only [hL] using divided_canonical M Hr hHr r X₁ X₂ Y₁ Y₂ t₁ t₂ d g,
    fun _=>rfl,rfl,rfl,rfl⟩

#print axioms earlier_restored_intake
#print axioms earlier_divided_canonical
end
end QRH.Cycle092.ActualStageFrameBudget
