/- Copyright (c) 2026 Hailey Collet and Sil. Apache-2.0.
Every original nonzero packed colored leaf is the literal two-anchor
GroupedPair energy with one unchanged original physical marked subproduct.
No sixth-free or clean-row restriction precedes the common-profile grouping.
-/
import Candidate.C092.transport.RegularColoredFrameLabel
import Candidate.C092.transport.RegularColoredForwardOrdinary
import Candidate.C092.transport.GroupedPairClassControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentEnergyCapacityRemoval CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentWholeSlotDeletion CenteredMomentTwist
open QRH.SilDensitySplit.CubeFree.Packet.Reduce
open QRH.SilDensitySplit.CubeFree.FP
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable (M : Id) [NeZero M]
local instance c092LocalInst_Candidate_C092_transport_RegularColoredFrameLeaf_5f761bb3ab79022b_001 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M ≤ Hray)

/-- This dictionary holds on every original nonzero packed row; no clean
or sixth-free row assumption is made before the common profile grouping. -/
theorem frameNativeLeaf_pairEnergy {α : Type} [Fintype α]
    (W : ℝ→ℂ) (η₀ : Character) (θ : α→RayQuotient.Characters M Hray) (Z : ℝ)
    (w σ freq : α→ℝ) (t : ℝ) (η ω₁ ω₂ : Character)
    (keep : O→Prop) (hkeep : ∀ z, keep z → z ≠ 0) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a)
    (hs₁ : Function.support (W₁:ℝ→ℂ) ⊆ Set.Icc a b)
    (hs₂ : Function.support (W₂:ℝ→ℂ) ⊆ Set.Icc a b)
    (t₁ t₂ : ℝ) (A : Finset α) (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    coloredNativeLeaf M Hray hHray W η₀ θ Z w σ freq t η ω₁ ω₂ keep Φ K W₁ W₂ t₁ t₂ A X₁ X₂ =
      GroupedPair.pairEnergy (η.product ω₁) (η.product ω₂)
        (fixedBadMask*OAI.ConcretePrimeRowBridge.idealGenerator 1) 1 1
        (fun z=>∏ i∈A, normalizedSlot η (fixedBadMask*OAI.ConcretePrimeRowBridge.idealGenerator 1)
          1 z (CenteredMomentPrimeSlot.primePool M Hray 2 (Z^(w i)))
          (slotBeta M Hray hHray W η₀ θ Z w σ freq i) t (Z^(w i)))
        t₁ t₂ W₁ W₂ X₁ X₂ keep Φ K := by
  unfold coloredNativeLeaf radialEnergy GroupedPair.pairEnergy
  apply tsum_congr
  intro z
  by_cases hz : keep z
  · simp only [hz,ite_true]
    rw [GroupedPair.row_eq_original _ _ _ _ _ _ _ _ _ _ _ _ _ hX₁ hX₂]
    rw [norm_mul,norm_mul,norm_prod]
    have h₁ := colored_ordinary_polynomial_norm η ω₁ z (hkeep z hz) W₁ a b ha hs₁ (W₁.smooth ⊤) t₁ X₁ hX₁
    have h₂ := colored_ordinary_polynomial_norm η ω₂ z (hkeep z hz) W₂ a b ha hs₂ (W₂.smooth ⊤) t₂ X₂ hX₂
    simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t₁] at h₁
    simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t₂] at h₂
    rw [norm_mul,norm_mul,norm_prod,h₁,h₂]
    simp_rw [natural_slot_eq_original η z (hkeep z hz)]
    rfl
  · simp only [hz,ite_false]

#print axioms frameNativeLeaf_pairEnergy
end
end QRH.Cycle092.RegularColoredForward
