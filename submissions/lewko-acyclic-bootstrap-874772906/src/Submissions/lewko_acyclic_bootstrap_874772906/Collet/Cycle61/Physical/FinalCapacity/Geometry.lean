import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondActualWidth
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalCapacity
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondActualWidth CenteredMomentCanonicalFirst
open CenteredMomentSourceRow CenteredMomentSupport CenteredMomentPartitionNorm
open CenteredMomentSectorLocalization
open CenteredMomentAmplificationChildSourceCaps
local notation "O" => HeckeFamily.O

/-- The actual common frequency ideal divides each genuine common allocation. -/
theorem actual_common_norm_le (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) :
    normValue (commonFrequencyGenerator C D) ≤ (C.absNorm:ℝ) := by
  have hd := (commonFrequencyGenerator_dvd C D hC hD hCD).1
  have hi : Ideal.span {commonFrequencyGenerator C D} ∣ C := by
    have hh := Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hd)
    simpa only [primary_span_supported C hC] using hh
  unfold normValue
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC.1)) (map_dvd Ideal.absNorm hi)

/-- The same actual common frequency ideal divides the right allocation. -/
theorem actual_common_norm_le_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) :
    normValue (commonFrequencyGenerator C D) ≤ (D.absNorm:ℝ) := by
  have hd := (commonFrequencyGenerator_dvd C D hC hD hCD).2
  have hi : Ideal.span {commonFrequencyGenerator C D} ∣ D := by
    have hh := Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hd)
    simpa only [primary_span_supported D hD] using hh
  unfold normValue
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.1)) (map_dvd Ideal.absNorm hi)

/-- The unit subset has positive ideal norm; its logarithm cannot enlarge
 the common frequency shift. -/
theorem actual_unit_log_nonneg (C D : Ideal O) (hC : Supported C)
    (U : Finset (CommonIndex C D)) (Z : ℝ) (hZ : 1 < Z) :
    0 ≤ Real.logb Z ((∏ P ∈ U,P.val).absNorm:ℝ) := by
  have hn : (∏ P ∈ U,P.val) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun P _ => (commonPrime_supported_ideal C D hC P).1)
  exact Real.logb_nonneg hZ (norm_ge_one _ hn)

/-- This is the literal second-transform shift, with the actual common
 frequency generator and actual partition unit ideal. -/
theorem actual_common_shift_le (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (normValue (commonFrequencyGenerator C D))-
      Real.logb Z ((∏ P ∈ U,P.val).absNorm:ℝ) ≤ Real.logb Z (C.absNorm:ℝ) := by
  have hg := Real.logb_le_logb_of_le hZ
    (normValue_pos _ (commonFrequencyGenerator_ne_zero C D hC))
    (actual_common_norm_le C D hC hD hCD)
  linarith [actual_unit_log_nonneg C D hC U Z hZ]

/-- Right-source cancellation uses the very same generator and partition U. -/
theorem actual_common_shift_le_right (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C = primeSupport D) (U : Finset (CommonIndex C D))
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (normValue (commonFrequencyGenerator C D))-
      Real.logb Z ((∏ P ∈ U,P.val).absNorm:ℝ) ≤ Real.logb Z (D.absNorm:ℝ) := by
  have hg := Real.logb_le_logb_of_le hZ
    (normValue_pos _ (commonFrequencyGenerator_ne_zero C D hC))
    (actual_common_norm_le_right C D hC hD hCD)
  linarith [actual_unit_log_nonneg C D hC U Z hZ]

#print axioms actual_common_norm_le_right
#print axioms actual_common_shift_le_right
#print axioms actual_common_norm_le
#print axioms actual_unit_log_nonneg
#print axioms actual_common_shift_le
end
end OAI.SevenEighths.Cycle61FinalCapacity
