import Candidate.Cycle63.Moment.JointColumnExtraction
import Candidate.Cycle63.Physical.BufferedPlain
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SlotNormalization

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredMomentWholeSlotDeletion
open CenteredMomentSlotNormalization CenteredMomentEligibleEnergy
open CenteredMomentDivisorRetained CenteredMomentDivisorAllocation
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_positive_row_factors (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i) :
    positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ =
      ((Real.sqrt X₁ : ℂ)⁻¹*rowTwistedSum η m A z W₁ t X₁)*
      ((Real.sqrt X₂ : ℂ)⁻¹*rowTwistedSum η m A z W₂ t X₂)*
      ∏ i, normalizedSlot η m A z (S i) (β i) t (P i) := by
  rw [←selectedProduct_univ η m A z W₁ W₂ S β P t X₁ X₂
    (mul_pos hX₁ hX₂).le (fun i => (hP i).le)]
  unfold selectedProduct
  rw [Real.sqrt_mul hX₁.le, Complex.ofReal_mul, mul_inv_rev]
  ring

theorem actual_retained_row_factors (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i) :
    retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂ =
      ((Real.sqrt (clippedScale X₁) : ℂ)⁻¹*rowTwistedSum η m A z W₁ t X₁)*
      ((Real.sqrt (clippedScale X₂) : ℂ)⁻¹*rowTwistedSum η m A z W₂ t X₂)*
      ∏ i, normalizedSlot η m A z (S i) (β i) t (P i) := by
  unfold retainedPositiveRow
  rw [actual_positive_row_factors η m A z _ _ S β P t _ _
    (zero_lt_one.trans_le (clippedScale_ge_one X₁))
    (zero_lt_one.trans_le (clippedScale_ge_one X₂)) hP,
    clipped_rowTwistedSum η m A z W₁ t X₁ hX₁,
    clipped_rowTwistedSum η m A z W₂ t X₂ hX₂]

theorem actual_retained_row_squared_factors (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i) :
    ‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 =
      ‖(Real.sqrt (clippedScale X₁) : ℂ)⁻¹*rowTwistedSum η m A z W₁ t X₁‖^2*
      ‖(Real.sqrt (clippedScale X₂) : ℂ)⁻¹*rowTwistedSum η m A z W₂ t X₂‖^2*
      ∏ i, ‖normalizedSlot η m A z (S i) (β i) t (P i)‖^2 := by
  rw [actual_retained_row_factors η m A z W₁ W₂ S β P t X₁ X₂ hX₁ hX₂ hP]
  simp only [norm_mul, mul_pow, norm_prod, Finset.prod_pow]

theorem actual_retained_row_bound (η : Character) (m A z : O)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i)
    (B₁ B₂ : ℝ) (B : ι → ℝ)
    (h₁ : ‖(Real.sqrt (clippedScale X₁) : ℂ)⁻¹*rowTwistedSum η m A z W₁ t X₁‖^2 ≤ B₁)
    (h₂ : ‖(Real.sqrt (clippedScale X₂) : ℂ)⁻¹*rowTwistedSum η m A z W₂ t X₂‖^2 ≤ B₂)
    (hslot : ∀ i, ‖normalizedSlot η m A z (S i) (β i) t (P i)‖^2 ≤ B i) :
    ‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 ≤ B₁*B₂*∏ i, B i := by
  rw [actual_retained_row_squared_factors η m A z W₁ W₂ S β P t X₁ X₂ hX₁ hX₂ hP]
  exact mul_le_mul
    (mul_le_mul h₁ h₂ (sq_nonneg _) ((sq_nonneg _).trans h₁))
    (Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _) (fun i _ => hslot i))
    (Finset.prod_nonneg (fun _ _ => sq_nonneg _))
    (mul_nonneg ((sq_nonneg _).trans h₁) ((sq_nonneg _).trans h₂))

#print axioms actual_positive_row_factors
#print axioms actual_retained_row_factors
#print axioms actual_retained_row_squared_factors
#print axioms actual_retained_row_bound
end
end OAI.SevenEighths.Cycle63Moment
