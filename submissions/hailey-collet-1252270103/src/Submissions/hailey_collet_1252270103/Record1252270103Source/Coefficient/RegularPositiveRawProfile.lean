/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Uses the checked Cycle61 profile normalization and OpenAI/math retained rows.
These identities retain both original profiles and every marked coefficient. -/
import Submissions.hailey_collet_1252270103.Cycle61.Physical.HighProfiles.Source
import Submissions.hailey_collet_1252270103.Cycle61.Moment.BufferedRetainedRows

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set HeckeFamily CenteredMomentFiniteProfileExceptional
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentHeckeHeight Cycle61HighProfiles
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A surviving literal positive row has both original ordinary supports. -/
theorem positive_row_surviving_scales {ap bp : ℝ} (p : Profiles ap bp)
    (η : Character) (m z : O) (pool : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ) (X : Fin 2 → ℝ)
    (hX : ∀ j, 0 < X j)
    (hne : positiveSlotRow η m 1 z (p.profile 0) (p.profile 1)
      pool β P t (X 0) (X 1) ≠ 0) : ∀ j, 1 ≤ X j * bp := by
  have hs (j : Fin 2) : Function.support (p.profile j : ℝ → ℂ) ⊆ Iic bp :=
    fun _ hx => (p.support j hx).2
  have h0 : 1 ≤ X 0 * bp := by
    by_contra h
    have hz := strict_subunit_rowTwistedSum_zero η m 1 z (p.profile 0)
      bp t (X 0) (hX 0) (hs 0) (lt_of_not_ge h)
    exact hne (by simp [positiveSlotRow, hz])
  have h1 : 1 ≤ X 1 * bp := by
    by_contra h
    have hz := strict_subunit_rowTwistedSum_zero η m 1 z (p.profile 1)
      bp t (X 1) (hX 1) (hs 1) (lt_of_not_ge h)
    exact hne (by simp [positiveSlotRow, hz])
  intro j
  fin_cases j
  · exact h0
  · exact h1

/-- Separate homogeneous normalization of the two retained plain profiles. -/
theorem retained_plain_normalized_norm_sq {ap bp : ℝ} (hap : 0 < ap)
    (S : Finset (ℕ × ℕ)) (hS : (0, 0) ∈ S) (p : Profiles ap bp)
    (η : Character) (m z : O) (pool : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t : ℝ) (X : Fin 2 → ℝ)
    (hX : ∀ j, 0 < X j) (hret : ∀ j, 1 ≤ X j * bp) :
    ‖retainedPositiveRow η m 1 z (p.profile 0) (p.profile 1)
      pool β P t (X 0) (X 1)‖ ^ 2 =
    (clippedControl hap S p X hX 0 * clippedControl hap S p X hX 1) ^ 2 *
      ‖retainedPositiveRow η m 1 z
        ((normalizedPlains hap S p X hX).profile 0)
        ((normalizedPlains hap S p X hX).profile 1)
        pool β P t (X 0) (X 1)‖ ^ 2 := by
  have he (j : Fin 2) : (p.profile j : ℝ → ℂ) =
      clippedControl hap S p X hX j •
        ((normalizedPlains hap S p X hX).profile j : ℝ → ℂ) :=
    congrArg (fun W : 𝓢(ℝ, ℂ) => (W : ℝ → ℂ))
      (normalizedPlains_reconstruct hap S hS p X hX hret j).symm
  conv_lhs => rw [he 0, he 1]
  rw [retainedPositiveRow_smul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (clippedControl_nonneg hap S p X hX 0)
      (clippedControl_nonneg hap S p X hX 1)), mul_pow]

/-- Clipping costs a fixed profile factor even at positive subunit scales. -/
theorem clipped_plain_product_rpow (X Y b ν : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (hretX : 1 ≤ X * b) (hretY : 1 ≤ Y * b)
    (hν : 0 ≤ ν) (hν' : ν ≤ 1) :
    (clippedScale X * clippedScale Y) ^ ν ≤ (max 1 b) ^ 2 * (X * Y) ^ ν := by
  have hb : 0 < max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  have hx : clippedScale X ≤ max 1 b * X := by
    have h := clipDilation_le b X hX hretX
    exact (div_le_iff₀ hX).mp h
  have hy : clippedScale Y ≤ max 1 b * Y := by
    have h := clipDilation_le b Y hY hretY
    exact (div_le_iff₀ hY).mp h
  have hp : clippedScale X * clippedScale Y ≤ (max 1 b) ^ 2 * (X * Y) := by
    convert mul_le_mul hx hy (zero_le_one.trans (clippedScale_ge_one Y))
      (mul_nonneg hb.le hX.le) using 1 <;> ring
  have hbase : 1 ≤ (max 1 b) ^ 2 := one_le_pow₀ (le_max_left _ _)
  calc
    _ ≤ ((max 1 b) ^ 2 * (X * Y)) ^ ν :=
      Real.rpow_le_rpow (mul_nonneg (zero_le_one.trans (clippedScale_ge_one X))
        (zero_le_one.trans (clippedScale_ge_one Y))) hp hν
    _ = ((max 1 b) ^ 2) ^ ν * (X * Y) ^ ν :=
      Real.mul_rpow (sq_nonneg _) (mul_nonneg hX.le hY.le)
    _ ≤ (max 1 b) ^ 2 * (X * Y) ^ ν := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (mul_nonneg hX.le hY.le) _)
      simpa using Real.rpow_le_rpow_of_exponent_le hbase hν'

#print axioms positive_row_surviving_scales
#print axioms retained_plain_normalized_norm_sq
#print axioms clipped_plain_product_rpow
end
end OAI.SevenEighths.Record1252270103Source
