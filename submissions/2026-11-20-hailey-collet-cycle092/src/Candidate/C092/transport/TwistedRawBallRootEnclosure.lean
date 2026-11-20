/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual canonical restored root with independently colored ordinary slots. -/
import Candidate.C092.transport.TwistedRawBallRootReindex
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
open CenteredMomentAllocatedNaturalRadial CenteredMomentSecondHeightFamily
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations MixedCanonicalSource
open MixedCompletedRows
open NativeMaskedEnergy
open MixedInnerExceptionalBlock MixedLiveNormalization RestoredRootDictionary
open Candidate.FourthPower.KernelNaturalSlots Candidate.FourthPower.KernelAssignmentReindex
open Candidate.FourthPower.NativeFiniteHoles Candidate.FourthPower.RestorationCollisionEnergy
open KernelRowProfiles KernelRowExpansion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.Cycle092.RegularColoredForward
open KernelMarkedRows KernelRowPools KernelLabelledSlots
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι]


theorem colored_fixed_row_enclosure (S S' : Finset PrimeIdeal) (hSS : S ⊆ S')
    (slot : ι→S) (χ : Character) (ω₁ ω₂ : Id→*₀ℂ)
    (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b) (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (hoff : ∀I,¬Supported I→idealCoeff χ I=0)
    (hS : ∀I,Supported I→((I.absNorm:ℝ) ≤ b*X₁ ∨ (I.absNorm:ℝ) ≤ b*X₂)→
      primeSupport I ⊆ primeValues S) :
    RegularColoredForward.row χ ω₁ ω₂ (supportedRectangle S b X₁ X₂)
      (sourceValue false S slot) W₁ W₂ X₁ X₂ =
    RegularColoredForward.row χ ω₁ ω₂ (supportedRectangle S' b X₁ X₂)
      (sourceValue false S' (fun i=>(⟨(slot i).val,hSS (slot i).property⟩ : S')))
      W₁ W₂ X₁ X₂ := by
  unfold RegularColoredForward.row
  rw [source_value_enclosure S S' hSS slot false]
  have hvalues : primeValues S ⊆ primeValues S' := by
    intro I hI
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
    exact Finset.mem_image.mpr ⟨P,hSS hP,rfl⟩
  calc
    _ = normalizedRow χ (rectangle b X₁ X₂)
        (fun n=>sourceValue false S slot n*color ω₁ ω₂ n) W₁ W₂ X₁ X₂ :=
      (normalized_row_complete χ S (rectangle b X₁ X₂)
        (fun n=>sourceValue false S slot n*color ω₁ ω₂ n)
        W₁ W₂ b X₁ X₂ hX₁ hX₂ hs₁ hs₂ (Finset.Subset.refl _) hoff hS).symm
    _ = _ := normalized_row_complete χ S' (rectangle b X₁ X₂)
      (fun n=>sourceValue false S slot n*color ω₁ ω₂ n)
      W₁ W₂ b X₁ X₂ hX₁ hX₂ hs₁ hs₂ (Finset.Subset.refl _) hoff
      (fun I hI hlen=>(hS I hI hlen).trans hvalues)

theorem colored_row_enclosure (S S' : Finset PrimeIdeal) (hSS : S ⊆ S')
    (χ : Character) (ω₁ ω₂ : Id→*₀ℂ) (pool : ι → Finset Id) (β : ι → Id → ℂ) (P : ι → ℝ)
    (hp : ∀ i, pool i ⊆ primeValues S)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (hoff : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (hS : ∀ I, Supported I → ((I.absNorm:ℝ) ≤ b*X₁ ∨ (I.absNorm:ℝ) ≤ b*X₂) →
      QRH.Record1252270103KernelMass.primeSupport I ⊆ primeValues S) :
    restoredRow χ ω₁ ω₂ S pool β P W₁ W₂ b X₁ X₂ =
      restoredRow χ ω₁ ω₂ S' pool β P W₁ W₂ b X₁ X₂ := by
  let extend : (ι → S) → (ι → S') := fun slot i => ⟨(slot i).val, hSS (slot i).property⟩
  have hext : Function.Injective extend := by
    intro slot slot' h
    funext i
    apply Subtype.ext
    exact congrArg (fun p : S' => p.val) (congrFun h i)
  let f : (ι → S) → ℂ := fun slot => if Function.Injective slot then
    RegularColoredForward.row χ ω₁ ω₂ (supportedRectangle S b X₁ X₂) (sourceValue false S slot) W₁ W₂ X₁ X₂ *
      ∏ i, naturalCoefficients χ S pool β P i (slot i) else 0
  let g : (ι → S') → ℂ := fun slot => if Function.Injective slot then
    RegularColoredForward.row χ ω₁ ω₂ (supportedRectangle S' b X₁ X₂) (sourceValue false S' slot) W₁ W₂ X₁ X₂ *
      ∏ i, naturalCoefficients χ S' pool β P i (slot i) else 0
  have hterm (slot : ι → S) : f slot = g (extend slot) := by
    have hi : Function.Injective (extend slot) ↔ Function.Injective slot := by
      constructor
      · intro h i j hij
        apply h
        apply Subtype.ext
        exact congrArg (fun p : S => p.val) hij
      · intro h i j hij
        apply h
        apply Subtype.ext
        exact congrArg (fun p : S' => p.val) hij
    dsimp only [f, g]
    simp only [hi]
    by_cases hinj : Function.Injective slot
    · simp only [hinj, ite_true]
      rw [colored_fixed_row_enclosure S S' hSS slot χ ω₁ ω₂ W₁ W₂ b X₁ X₂
        hX₁ hX₂ hs₁ hs₂ hoff hS]
      rfl
    · simp only [hinj, ite_false]
  have hfrow : restoredRow χ ω₁ ω₂ S pool β P W₁ W₂ b X₁ X₂ = ∑ slot, f slot := by
    unfold restoredRow restoredRowOn weightedSum
    apply Finset.sum_congr rfl
    intro slot _
    by_cases hi : Function.Injective slot <;> simp only [f,hi,ite_true,ite_false]
  have hgrow : restoredRow χ ω₁ ω₂ S' pool β P W₁ W₂ b X₁ X₂ = ∑ slot, g slot := by
    unfold restoredRow restoredRowOn weightedSum
    apply Finset.sum_congr rfl
    intro slot _
    by_cases hi : Function.Injective slot <;> simp only [g,hi,ite_true,ite_false]
  rw [hfrow,hgrow]
  calc
    _ = ∑ slot ∈ (Finset.univ : Finset (ι → S)).image extend, g slot := by
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl (fun slot _ => hterm slot)
      · exact fun slot _ slot' _ h => hext h
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro slot _ hout
      have hpzero : (∏ i, naturalCoefficients χ S' pool β P i (slot i)) = 0 := by
        by_contra hn
        have hcoeff (i : ι) : naturalCoefficients χ S' pool β P i (slot i) ≠ 0 :=
          Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ _)
        have hmem (i : ι) : (slot i).val ∈ S := by
          have hpool : (slot i).val.val ∈ pool i := by
            by_contra hh
            exact hcoeff i (by simp only [naturalCoefficients, slotTerm, hh, ite_false])
          obtain ⟨Q, hQ, hQi⟩ := Finset.mem_image.mp (hp i hpool)
          exact (Subtype.ext hQi : Q = (slot i).val) ▸ hQ
        let original : ι → S := fun i => ⟨(slot i).val, hmem i⟩
        apply hout
        refine Finset.mem_image.mpr ⟨original, Finset.mem_univ _, ?_⟩
        funext i
        exact Subtype.ext rfl
      dsimp only [g]
      rw [hpzero]
      simp only [mul_zero, ite_self]

#print axioms colored_fixed_row_enclosure
#print axioms colored_row_enclosure
end
end QRH.Cycle092.TwistedRawBallRootProducer
