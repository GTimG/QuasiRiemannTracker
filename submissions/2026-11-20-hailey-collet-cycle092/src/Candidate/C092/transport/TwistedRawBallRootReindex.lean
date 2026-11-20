/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual canonical restored root with independently colored ordinary slots. -/
import Candidate.C092.transport.TwistedRawBallRootProducer
import Candidate.C092.transport.RegularColoredForwardSource
import Submissions.sil_density_split_20261026.CubeFree.FP.RestoredRootEnergy
import Submissions.sil_density_split_20261026.CubeFree.FP.RecenteredRootSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBallRootProducer
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform CenteredMomentLattice
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalRadial CenteredMomentSecondHeightFamily
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations MixedCanonicalSource
open Candidate.FourthPower.KernelCollisionEnergy
open QRH.SilDensitySplit.CubeFree.FP.RestorationFamily
open QRH.SilDensitySplit.CubeFree.FP.RestorationCollisionEnergy
open NativeMaskedEnergy
open MixedInnerExceptionalBlock MixedLiveNormalization RestoredRootDictionary
open Candidate.FourthPower.KernelNaturalSlots Candidate.FourthPower.KernelAssignmentReindex
open Candidate.FourthPower.NativeFiniteHoles
open KernelRowProfiles KernelRowExpansion
open KernelMarkedRows KernelRowPools KernelLabelledSlots
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]

/-- The exact common-domain colored family is reindexed before norms. -/
theorem restoredRowOn_reindex (e : ι ≃ κ) (S : Finset PrimeIdeal) (χ : Character)
    (ω₁ ω₂ : Id→*₀ℂ) (pool : κ→Finset Id) (β : κ→Id→ℂ) (P : κ→ℝ)
    (D : Finset (Id×Id)) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ) :
    restoredRowOn χ ω₁ ω₂ S (fun i=>pool (e i)) (fun i=>β (e i)) (fun i=>P (e i))
      D W₁ W₂ X₁ X₂ = restoredRowOn χ ω₁ ω₂ S pool β P D W₁ W₂ X₁ X₂ := by
  unfold restoredRowOn weightedSum
  apply Finset.sum_bij (fun slot _=>fun j=>slot (e.symm j))
  · intro slot _
    exact Finset.mem_univ _
  · intro slot _ slot' _ h
    funext i
    have he := congrFun h (e i)
    simpa only [e.symm_apply_apply] using he
  · intro slot _
    refine ⟨fun i=>slot (e i),Finset.mem_univ _,?_⟩
    funext j
    exact congrArg slot (e.apply_symm_apply j)
  · intro slot _
    have hinj : Function.Injective (fun j=>slot (e.symm j)) ↔ Function.Injective slot := by
      constructor
      · intro h i i' hii'
        apply e.injective
        apply h
        simpa only [e.symm_apply_apply] using hii'
      · intro h
        exact h.comp e.symm.injective
    have hkernel : sourceValue false S (fun j=>slot (e.symm j))=sourceValue false S slot := by
      unfold sourceValue
      rw [RestoredRootDictionary.marked_reindex]
    have hprod : (∏i,naturalCoefficients χ S pool β P (e i) (slot i)) =
        ∏j,naturalCoefficients χ S pool β P j (slot (e.symm j)) := by
      simpa only [e.symm_apply_apply] using
        e.prod_comp (fun j=>naturalCoefficients χ S pool β P j (slot (e.symm j)))
    simp only [hinj,hkernel]
    by_cases hi : Function.Injective slot
    · simp only [hi,ite_true]
      change _*(∏i,naturalCoefficients χ S pool β P (e i) (slot i))=_
      rw [hprod]
    · simp only [hi,ite_false]

/-- The two actual restoration masks become canonical marked slots on a
    subset of the original ambient type. Independent ordinary colors stay live. -/
theorem colored_restored_on_original_subset (r : Setoid α) (S : Finset PrimeIdeal)
    (tc : {q // ¬singletonBlock r q}→S)
    (A : Finset {q // singletonBlock r q}) (ti : A→S)
    (χ : Character) (ω₁ ω₂ : Id→*₀ℂ) (pool : α→Finset Id) (ν : α→Character)
    (W : ℝ→ℂ) (P σ v : α→ℝ) (t : ℝ)
    (D : Finset (Id×Id)) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ) :
    restoredRowOn χ ω₁ ω₂ S
      (fun q : Remaining r A=>pool (singletonRepresentative r q.val))
      (crossBeta A S ti (collisionBeta r S tc (fun i=>heightCoefficient
        (fun I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight W (P i) (σ i) (v i) I) t)))
      (fun q=>P (singletonRepresentative r q.val)) D W₁ W₂ X₁ X₂ =
    restoredRowOn χ ω₁ ω₂ S (fun i : remainingSet r A=>pool i.val)
      (fun i I=>slotCoefficient (fun j : remainingSet r A=>ν j.val)
        (fun _=>restorationHoles r S tc A ti) t i I*
        slotProfile W (σ i.val) (v i.val) (I.absNorm/P i.val))
      (fun i=>P i.val) D W₁ W₂ X₁ X₂ := by
  rw [restoration_canonical_coefficients]
  exact restoredRowOn_reindex (remainingEquiv r A) S χ ω₁ ω₂
    (fun i : remainingSet r A=>pool i.val)
    (fun i I=>slotCoefficient (fun j : remainingSet r A=>ν j.val)
      (fun _=>restorationHoles r S tc A ti) t i I*
      slotProfile W (σ i.val) (v i.val) (I.absNorm/P i.val))
    (fun i=>P i.val) D W₁ W₂ X₁ X₂

#print axioms restoredRowOn_reindex
#print axioms colored_restored_on_original_subset
end
end QRH.Cycle092.TwistedRawBallRootProducer
