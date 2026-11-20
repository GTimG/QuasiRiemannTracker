/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact original finite-pool and puncture centralization for the two ordinary
colors. All identities precede norms and preserve the signed rectangles. -/
import Candidate.C092.transport.RegularColoredForwardTuple
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedCanonicalSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.RegularColoredForward
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass
open CenteredMomentSourceMass CenteredMomentSourceRectangle CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentCommonMaskExpansion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower.KernelAssignmentReindex
open KernelRowExpansion KernelRowProfiles KernelRowPools KernelMarkedRows
open MixedCommonRestriction MixedCommonCoefficient MixedTupleRows MixedCompletedRows MixedLiveRows
open QRH.Cycle092.TwistedRawSource
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance c092LocalInst_Candidate_C092_transport_RegularColoredForwardPuncture_39065b0c460a3612_001 : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

/-- Insert actual ordinary colors in the native finite-domain completion.
Omitted rows vanish by original support and character zeros. -/
theorem colored_row_complete (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ) (S : Finset PrimeIdeal)
    (D : Finset (Id × Id)) (r : Id × Id → ℂ) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b) (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (hD : rectangle b X₁ X₂ ⊆ D) (hoff : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (hS : ∀ I, Supported I →
      ((I.absNorm : ℝ) ≤ b*X₁ ∨ (I.absNorm : ℝ) ≤ b*X₂) → primeSupport I ⊆ primeValues S) :
    row χ ω₁ ω₂ D r W₁ W₂ X₁ X₂ =
      row χ ω₁ ω₂ (supportedRectangle S b X₁ X₂) r W₁ W₂ X₁ X₂ :=
  normalized_row_complete χ S D (fun n => r n * color ω₁ ω₂ n)
    W₁ W₂ b X₁ X₂ hX₁ hX₂ hs₁ hs₂ hD hoff hS

/-- Ordinary-only H punctures move into the common character by exact ideal
coefficient equality. Both independent ordinary colors remain on their own coordinates. -/
theorem colored_hole_absorption (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (hH : H ⊆ S) (D : Finset (Id × Id)) (live : S → Bool)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    row χ ω₁ ω₂ D (restrictedValue S (KernelPunctureRows.augmented S H live)) W₁ W₂ X₁ X₂ =
      row (χ.excludePrimes (holes H) (holes_prime H)) ω₁ ω₂ D (restrictedValue S live) W₁ W₂ X₁ X₂ := by
  unfold row normalizedRow
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  rw [ordinary_mask S H hH]
  unfold pairCharacter
  rw [←common_character_mask]
  ring

/-- The ordinary puncture does not change marked coefficients that already
vanish there. Thus the native common mask is not silently added to a mark-only ν. -/
theorem colored_family_hole_absorption (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (hH : H ⊆ S)
    (pool : ι → Finset Id) (β : ι → Id → ℂ) (P : ι → ℝ)
    (hβ : ∀ i, ∀ Q ∈ H, β i Q.val = 0) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) :
    weightedSum (naturalCoefficients χ S pool β P)
      (fun slot => row χ ω₁ ω₂ (supportedRectangle S b X₁ X₂)
        (restrictedValue S (KernelPunctureRows.augmented S H (KernelLabelledSlots.marked S slot)))
        W₁ W₂ X₁ X₂) =
    weightedSum (naturalCoefficients (χ.excludePrimes (holes H) (holes_prime H)) S pool β P)
      (fun slot => row (χ.excludePrimes (holes H) (holes_prime H)) ω₁ ω₂
        (supportedRectangle S b X₁ X₂) (sourceValue false S slot) W₁ W₂ X₁ X₂) := by
  rw [natural_hole_absorption χ S H pool β P hβ]
  apply congrArg (weightedSum (naturalCoefficients χ S pool β P))
  funext slot
  simpa only [sourceValue,Bool.false_eq_true,ite_false] using
    colored_hole_absorption χ ω₁ ω₂ S H hH _ (KernelLabelledSlots.marked S slot) W₁ W₂ X₁ X₂

/-- Zero-extension of the actual marked pools, preserving every ordinary
color. A missing marked atom annihilates its own original slotWeight. -/
theorem colored_centered_pool_completion (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (pool : ι → Finset Id) (hpool : ∀ i, pool i ⊆ primeValues S)
    (A B : Finset Id) (β : ι → Id → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id × Id) :
    (∑ v ∈ Fintype.piFinset (pools pool A B),
      coloredTuple (punctureProduct S H) ω₁ ω₂ (centeredCoefficient pool β P W₁ W₂ X₁ X₂ Y₁ Y₂ d) v *
        idealCoeff χ (finiteTupleProduct v)) =
    ∑ v ∈ Fintype.piFinset (pools (fun _ : ι => primeValues S) A B),
      coloredTuple (punctureProduct S H) ω₁ ω₂ (centeredCoefficient pool β P W₁ W₂ X₁ X₂ Y₁ Y₂ d) v *
        idealCoeff χ (finiteTupleProduct v) := by
  have hsub : Fintype.piFinset (pools pool A B) ⊆
      Fintype.piFinset (pools (fun _ : ι => primeValues S) A B) := by
    intro v hv
    apply Fintype.mem_piFinset.mpr
    intro j
    cases j with
    | inl i => exact hpool i (Fintype.mem_piFinset.mp hv (Sum.inl i))
    | inr j => exact Fintype.mem_piFinset.mp hv (Sum.inr j)
  apply Finset.sum_subset hsub
  intro v hv hn
  by_contra he
  have hc : centeredCoefficient pool β P W₁ W₂ X₁ X₂ Y₁ Y₂ d v ≠ 0 := by
    intro hz
    exact he (by simp only [coloredTuple,hz,mul_zero,zero_mul])
  have hp : (∏ i, slotWeight pool β P i (v (Sum.inl i))) ≠ 0 :=
    (mul_ne_zero_iff.mp hc).2
  apply hn
  apply Fintype.mem_piFinset.mpr
  intro j
  cases j with
  | inl i =>
    by_contra hi
    change v (Sum.inl i) ∉ pool i at hi
    exact (Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)) (by simp only [slotWeight,ite_eq_right hi])
  | inr j => exact Fintype.mem_piFinset.mp hv (Sum.inr j)

/-- Centralize the actual inherited source profile on its actual finite pools.
The whole nonzero puncture is retained through its radical character, and
all signed/reference profiles retain their original common normalization. -/
theorem colored_punctured_pool_profile (χ : Character) (ω₁ ω₂ : Id →*₀ ℂ)
    (S H : Finset PrimeIdeal) (R : Id) (hR : R ≠ 0)
    (pool : ι → Finset Id) (hpool : ∀ i, pool i ⊆ primeValues S)
    (A B : Finset Id) (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (d : Id × Id) :
    MixedLiveNormalization.normalization (X₁*X₂) P *
      (∑ v ∈ Fintype.piFinset (pools pool A B),
        coloredTuple (punctureProduct S H) ω₁ ω₂
          (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1) v *
          idealCoeff χ (finiteTupleProduct v)) =
    ∑ v ∈ Fintype.piFinset (pools (fun _ : ι => primeValues S) A B),
      coloredTuple (punctureProduct S H) ω₁ ω₂
        (centeredCoefficient pool (fun i I => ν i I * Wslot i (I.absNorm/P i)) P
          W₁ W₂ X₁ X₂ Y₁ Y₂ d) v *
        idealCoeff (χ.excludePrimes (primeSupport R) (fun _ h => IdealMobiusDivisorSum.support_prime h))
          (finiteTupleProduct v) := by
  rw [←colored_centered_pool_completion _ ω₁ ω₂ S H pool hpool A B]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have he := profile_centralization pool ν Wslot P R W₁ W₂ X₁ X₂ Y₁ Y₂ d v
    (fun i hi => False.elim (hi (Fintype.mem_piFinset.mp hv (Sum.inl i))))
  rw [←radical_character_mask χ R hR]
  unfold coloredTuple MixedLiveNormalization.normalization
  calc
    _ = tupleWeight (punctureProduct S H) v * ordinaryColor ω₁ ω₂ v *
      (((Real.sqrt (X₁*X₂) : ℂ)⁻¹ * ∏ i, (Real.sqrt (P i) : ℂ)⁻¹) *
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 1 v) *
        idealCoeff χ (finiteTupleProduct v) := by ring
    _ = _ := by rw [he]; ring

#print axioms colored_row_complete
#print axioms colored_hole_absorption
#print axioms colored_family_hole_absorption
#print axioms colored_centered_pool_completion
#print axioms colored_punctured_pool_profile
end
end QRH.Cycle092.RegularColoredForward
