/- Copyright (c) 2026 Sil. Apache-2.0.
Compact descendant conclusions over an ABSTRACT first Source. Their fields
are exactly the original conjunctions. Generic proofs use only numerical
support caps and are reused by the root-specialized theorems.
No extra analytic premise.
Modified by Sil (2026-10-26): the residual SupportBounds/FrozenBounds of the u-freezing supplier lane (supplierData/residualSource/Frozen, not ported) are dropped; the module carries the lane-free generic caps used by the first live source: injected_prod_le and allocated_size_caps (moved from the replaced OuterFreshSource/OuterFreshSelectedWindow) and double_product_le.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane).
-/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.FP.RepairedCapEvent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.FP.RepairedDescendantBounds
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge
open QRH.Record1252270103KernelMass
open CenteredMomentSourceMass CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocationBox CenteredMomentSourceLiveColumn
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedFirstActualNonexceptional
open MixedInnerExceptionalBlock MixedOriginalNormCap MixedOriginalTail
local notation "Id" => Ideal HeckeFamily.O
local instance instDecEqDescendantBounds {κ : Type*} : DecidableEq κ := Classical.decEq _

/-- FP `OuterFreshSource.injected_prod_le` (generic; the OuterFresh lane is not ported). -/
theorem injected_prod_le {ι κ : Type*} [Fintype ι] [Fintype κ] (inc : κ → ι)
    (hinj : Function.Injective inc) (f : ι → ℝ) (hf : ∀ i, 1 ≤ f i) :
    (∏ j : κ, f (inc j)) ≤ ∏ i, f i := by
  have he : (∏ i ∈ (Finset.univ : Finset κ).image inc, f i) = ∏ j : κ, f (inc j) := by
    rw [Finset.prod_image (fun j _ k _ h => hinj h)]
  rw [← he]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
    (fun i _ => zero_le_one.trans (hf i)) (fun i _ _ => hf i)

/-- FP `OuterFreshSelectedWindow.allocated_size_caps` (generic, no frozen data): genuine
extraction creates no extra slot, scale, profile or norm cap. -/
theorem allocated_size_caps {ι : Type*} [Fintype ι] {a b : ℝ} (r : Source ι a b) (hb : 0 ≤ b)
    (cover : OriginalEnclosure r) (G : Id) (B : actualAllocations (tuplePools r) G) :
    let live := allocatedLiveSource r hb cover G B
    Fintype.card (liveIndices B.val) ≤ Fintype.card ι ∧
      (∏ i, 2*live.P i) ≤ ∏ i, 2*r.P i ∧ (∏ i, live.M i) ≤ ∏ i, r.M i ∧
      sourceNormCap live.P b live.T live.d ≤ sourceNormCap r.P b r.T r.d := by
  refine ⟨?_, ?_, ?_, live_norm_cap (allocationSource r hb cover G B)⟩
  · rw [Fintype.card_coe]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_univ)
  · exact injected_prod_le (fun i : liveIndices B.val => i.val) Subtype.val_injective
      (fun i => 2*r.P i) (fun i => by linarith [r.hP i])
  · exact injected_prod_le (fun i : liveIndices B.val => i.val) Subtype.val_injective r.M r.hM

/-- The doubled slot product from the dimension cap and the product cap. -/
theorem double_product_le {κ : Type*} [Fintype κ] (P : κ → ℝ) (hP : ∀ i, 1 ≤ P i) (Z : ℝ)
    (hZ : 0 ≤ Z) (htwo : (2:ℝ)^Fintype.card κ ≤ Z) (hp : (∏ i, P i) ≤ Z) :
    (∏ i, 2*P i) ≤ Z^(2:ℝ) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  apply (mul_le_mul htwo hp (Finset.prod_nonneg (fun i _ => zero_le_one.trans (hP i))) hZ).trans_eq
  rw [Real.rpow_two]
  ring

end
end Qrh.MarkedAnchor.Ordinary.FP.RepairedDescendantBounds
