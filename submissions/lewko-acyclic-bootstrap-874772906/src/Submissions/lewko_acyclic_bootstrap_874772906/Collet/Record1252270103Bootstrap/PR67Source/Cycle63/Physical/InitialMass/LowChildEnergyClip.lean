import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.InductionEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.Bands
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The energy at the clipped plain scales is at most the energy at the literal plain scales: the clipped profiles
dilate the plain profiles by the clipping factor, which divides every row by a factor at least one; the lengths of the
clipped and of the literal scales agree. Released under Apache 2.0. -/
set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentRetainedProfile CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
open CenteredMomentEnergyBands

/-- The length of the clipped plain scale is the length of the plain scale: the length already clips at one. -/
theorem length_clippedScale (Z X : ℝ) : length Z (clippedScale X) = length Z X := by
  unfold length clippedScale
  rw [← max_assoc, max_self]

/-- The energy of the rows at the literal plain scales `X₁`, `X₂` is the product of the two clipping factors times the
energy at the clipped plain scales, with the plain profiles dilated by the clipping factors. The identity holds for
every weight `Φ`, because the rows are compared one by one. -/
theorem energy_eq_clip_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (hP : ∀ i, 0 < P i)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (keep : O → Prop) (Φ : 𝓢(ℝ, ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K =
      (clipDilation X₁ * clipDilation X₂) *
        energy η m A t (dilated W₁ (clipDilation X₁)) (dilated W₂ (clipDilation X₂)) S β P
          (clippedScale X₁) (clippedScale X₂) keep Φ K := by
  unfold energy
  rw [← tsum_mul_left]
  refine tsum_congr (fun z => ?_)
  split_ifs
  · have h := retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t X₁ X₂ (X₁ * X₂) hX₁ hX₂ (mul_pos hX₁ hX₂)
    have hc : clippedScale X₁ * clippedScale X₂ / (X₁ * X₂) = clipDilation X₁ * clipDilation X₂ := by
      unfold clipDilation
      rw [div_mul_div_comm]
    rw [hc] at h
    have h' : ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖ ^ 2 =
        (clipDilation X₁ * clipDilation X₂) * ‖positiveSlotRow η m A z (dilated W₁ (clipDilation X₁))
          (dilated W₂ (clipDilation X₂)) S β P t (clippedScale X₁) (clippedScale X₂)‖ ^ 2 := h
    rw [h']
    ring
  · simp

/-- The energy at the clipped plain scales is at most the energy at the literal plain scales, when the weight is
real and nonnegative. -/
theorem energy_clipped_le {ι : Type*} [Fintype ι] [DecidableEq ι] (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (hP : ∀ i, 0 < P i)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (keep : O → Prop) (Φ : 𝓢(ℝ, ℂ)) (K : ℝ)
    (hnn : 0 ≤ energy η m A t (dilated W₁ (clipDilation X₁)) (dilated W₂ (clipDilation X₂)) S β P
      (clippedScale X₁) (clippedScale X₂) keep Φ K) :
    energy η m A t (dilated W₁ (clipDilation X₁)) (dilated W₂ (clipDilation X₂)) S β P
      (clippedScale X₁) (clippedScale X₂) keep Φ K ≤ energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K := by
  rw [energy_eq_clip_mul η m A t W₁ W₂ S β P hP X₁ X₂ hX₁ hX₂ keep Φ K]
  have hc : 1 ≤ clipDilation X₁ * clipDilation X₂ :=
    one_le_mul_of_one_le_of_one_le (clipDilation_ge_one _ hX₁) (clipDilation_ge_one _ hX₂)
  exact le_mul_of_one_le_left hnn hc

/-- A bound for the energy at the literal plain scales is a bound for the energy at the clipped plain scales. -/
theorem energy_clipped_le_of_le {ι : Type*} [Fintype ι] [DecidableEq ι] (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (hP : ∀ i, 0 < P i)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (keep : O → Prop) (Φ : 𝓢(ℝ, ℂ)) (K Bd : ℝ)
    (hnn : 0 ≤ energy η m A t (dilated W₁ (clipDilation X₁)) (dilated W₂ (clipDilation X₂)) S β P
      (clippedScale X₁) (clippedScale X₂) keep Φ K)
    (hB : energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K ≤ Bd) :
    energy η m A t (dilated W₁ (clipDilation X₁)) (dilated W₂ (clipDilation X₂)) S β P
      (clippedScale X₁) (clippedScale X₂) keep Φ K ≤ Bd :=
  (energy_clipped_le η m A t W₁ W₂ S β P hP X₁ X₂ hX₁ hX₂ keep Φ K hnn).trans hB

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
