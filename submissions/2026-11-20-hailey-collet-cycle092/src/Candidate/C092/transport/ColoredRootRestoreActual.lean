/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual same-row phase-aligned signed energy equals the original bare-anchor
colored restoration input, with the true common mark norm presentations. -/
import Candidate.C092.transport.ColoredRootRestoreSource
import Candidate.C092.transport.OrderedPairPhaseDictionary
set_option autoImplicit false
namespace QRH.Cycle092.ColoredRootRestore
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve
open HeckeInverseAmplification ProbeHighRowFamily CenteredMomentLattice
open CenteredMomentCommonMaskEnergy CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentTwist CenteredMomentWholeSlotDeletion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower.KernelAssignmentReindex Candidate.FourthPower.KernelCollisionEnergy
open QRH.SilDensitySplit.CubeFree.FP.KernelRowPools
open QRH.SilDensitySplit.CubeFree.FP.RestoredInitialSource
open QRH.Cycle092.ReferenceShortP3 QRH.Cycle092.OrderedPairPhase
open QRH.Cycle092.RegularColoredForward QRH.Cycle092.OrdinaryColumn
local notation "O"=>HeckeFamily.O
local notation "Id"=>Ideal O

/-- Exact equality on the SAME original finite rows and common physical
marks. The only presentation used is the actual first-anchor mark norm. -/
theorem signed_energy_eq_bare {ι:Type} (T:Finset ι)
    (M:Id) [NeZero M] (Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M≤Hr) (base η₁ η₂:Character)
    (θ:T→RayQuotient.Characters M Hr) (rows:Finset FreeRow)
    (S:Finset QRH.Record1252270103KernelMass.PrimeIdeal) (pool:T→Finset Id) (slotWeight:T→Id→ℂ) (P:T→ℝ)
    (mark:ι→FreeRow→ℂ) (tMark:ℝ) (W₁ W₂:ℝ→ℂ) {b M₁ M₂ X₁ X₂ Y₁ Y₂:ℝ}
    (hb:0≤b) (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂)
    (hprod:Y₁*Y₂=X₁*X₂)
    (hx₁:X₁≤M₁) (hx₂:X₂≤M₂) (hy₁:Y₁≤M₁) (hy₂:Y₂≤M₂)
    (hs₁:Function.support W₁⊆Set.Iic b) (hs₂:Function.support W₂⊆Set.Iic b)
    (henclose:∀ I:Id,Supported I → ((I.absNorm:ℝ)≤b*M₁ ∨ (I.absNorm:ℝ)≤b*M₂) →
      primeSupport I⊆primeValues S)
    (hmark:∀ u∈rows,∀ i:T,‖mark i.val u‖=‖normalizedSlot η₁
      (fixedBadMask*idealGenerator 1) 1 u.val (pool i)
      (fun I=>idealCoeff (relativeCharacter M Hr hHr base (θ i)) I*slotWeight i I) tMark (P i)‖) :
    signedPairEnergyOn T rows η₁ η₂ W₁ W₂ 0 0 X₁ X₂ Y₁ Y₂ mark =
    ∑ u∈rows,‖fullSigned S (bareCharacter u.val) (idealCoeff η₁) (idealCoeff η₂)
      (fun i=>supportedPool (pool i))
      (fun i=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M Hr hHr
        (base.product η₁.inverse) (θ i)) I*slotWeight i I) tMark) P
      (supportedRectangle S b M₁ M₂) W₁ W₂ X₁ X₂ Y₁ Y₂ 1 1‖^2 := by
  unfold signedPairEnergyOn
  apply Finset.sum_congr rfl
  intro u hu
  have hf:=fullSigned_physical_norm M Hr hHr base η₁ η₂ θ u.val u.property.1 S pool slotWeight P
    (fun i:T=>mark i.val u) tMark W₁ W₂ hb hX₁ hX₂ hY₁ hY₂ hx₁ hx₂ hy₁ hy₂ hs₁ hs₂ henclose (hmark u hu)
  rw [Finset.prod_coe_sort T (fun i=>mark i u)] at hf
  have he : signedPairOn T η₁ η₂ W₁ W₂ 0 0 X₁ X₂ Y₁ Y₂ mark u =
      (original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ 0 X₁*
        original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ 0 X₂-
      original η₁ (fixedBadMask*idealGenerator 1) 1 u.val W₁ 0 Y₁*
        original η₂ (fixedBadMask*idealGenerator 1) 1 u.val W₂ 0 Y₂)*∏ i∈T,mark i u := by
    rw [←pairRow_sub_eq_signed T η₁ η₂ W₁ W₂ 0 0 X₁ X₂ Y₁ Y₂ mark u
      hX₁.le hX₂.le hY₁.le hY₂.le hprod]
    unfold pairRowOn
    ring
  rw [he,←hf]

/-- Both original ordinary pitches are retained by the checked phase-aligned
comparison. Its native restored input has exactly coefficients +1 and -1. -/
theorem aligned_energy_eq_bare {ι:Type} (T:Finset ι)
    (M:Id) [NeZero M] (Hr:Subgroup (O⧸M)ˣ)
    (hHr:RayOrthogonality.globalUnits M≤Hr) (base η₁ η₂:Character)
    (θ:T→RayQuotient.Characters M Hr) (rows:Finset FreeRow)
    (S:Finset QRH.Record1252270103KernelMass.PrimeIdeal) (pool:T→Finset Id) (slotWeight:T→Id→ℂ) (P:T→ℝ)
    (mark:ι→FreeRow→ℂ) (tMark:ℝ) (W₁ W₂:ℝ→ℂ) (a b:ℝ) (ha:0<a) (hb:0≤b)
    (hs₁:Function.support W₁⊆Set.Icc a b) (hs₂:Function.support W₂⊆Set.Icc a b)
    (hW₁:ContDiff ℝ ∞ W₁) (hW₂:ContDiff ℝ ∞ W₂)
    (t₁ t₂ M₁ M₂ X₁ X₂ Y₁ Y₂:ℝ)
    (hX₁:0<X₁) (hX₂:0<X₂) (hY₁:0<Y₁) (hY₂:0<Y₂) (hprod:Y₁*Y₂=X₁*X₂)
    (hx₁:X₁≤M₁) (hx₂:X₂≤M₂) (hy₁:Y₁≤M₁) (hy₂:Y₂≤M₂)
    (henclose:∀ I:Id,Supported I → ((I.absNorm:ℝ)≤b*M₁ ∨ (I.absNorm:ℝ)≤b*M₂) →
      primeSupport I⊆primeValues S)
    (hmark:∀ u∈rows,∀ i:T,‖mark i.val u‖=‖normalizedSlot η₁
      (fixedBadMask*idealGenerator 1) 1 u.val (pool i)
      (fun I=>idealCoeff (relativeCharacter M Hr hHr base (θ i)) I*slotWeight i I) tMark (P i)‖) :
    alignedPairEnergyOn T rows η₁ η₂ W₁ W₂ t₁ t₂ X₁ X₂ Y₁ Y₂ mark =
    ∑ u∈rows,‖fullSigned S (bareCharacter u.val) (idealCoeff η₁) (idealCoeff η₂)
      (fun i=>supportedPool (pool i))
      (fun i=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M Hr hHr
        (base.product η₁.inverse) (θ i)) I*slotWeight i I) tMark) P
      (supportedRectangle S b M₁ M₂)
      (normPowerProfile W₁ a b ha hs₁ hW₁ t₁) (normPowerProfile W₂ a b ha hs₂ hW₂ t₂)
      X₁ X₂ Y₁ Y₂ 1 1‖^2 := by
  rw [alignedEnergy_eq_profile_signedEnergy T rows η₁ η₂ W₁ W₂ a b ha hs₁ hs₂ hW₁ hW₂
    t₁ t₂ X₁ X₂ Y₁ Y₂ mark hX₁ hX₂ hY₁ hY₂ hprod]
  exact signed_energy_eq_bare T M Hr hHr base η₁ η₂ θ rows S pool slotWeight P mark tMark _ _
    hb hX₁ hX₂ hY₁ hY₂ hprod hx₁ hx₂ hy₁ hy₂
    ((normPowerProfile_support _ _ _ _ _ _ _).trans (fun x hx=>(hs₁ hx).2))
    ((normPowerProfile_support _ _ _ _ _ _ _).trans (fun x hx=>(hs₂ hx).2)) henclose hmark

#print axioms signed_energy_eq_bare
#print axioms aligned_energy_eq_bare
end
end QRH.Cycle092.ColoredRootRestore
