/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighEndpointCertificate.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Endpoint

namespace OAI

noncomputable section
namespace SevenEighths.Endpoint

def evaluatePerturbedHighEndpointExponent (δ y : ℝ) : ℝ :=
  balancedExponent δ y + 214651 / 5000000000 +
    (42930200831 / 250000000000000) *
      (-1 / 2 + δ + δ * (1 / 2 - y) + 3 * balancedRowCount δ y / 2) +
    (12457523527 / 15625000000000) * (2 / 3 - balancedRowCount δ y)

private def evaluateQuadraticCoefficient (y : ℝ) : ℝ :=
  38381036152738950 + 98112671277888624 * y +
    70349424015981576 * y ^ 2 + 24024727795678656 * y ^ 3

private def evaluateLinearCoefficient (y : ℝ) : ℝ :=
  -29828491018092129 - 47206874749477924 * y - 3166469409426772 * y ^ 2

private def evaluateConstantCoefficient (y : ℝ) : ℝ :=
  5795432885635430 + 5325532921935260 * y

private def evaluateEndpointPolynomial (δ y : ℝ) : ℝ :=
  evaluateQuadraticCoefficient y * δ ^ 2 +
    evaluateLinearCoefficient y * δ + evaluateConstantCoefficient y

theorem verify_perturbed_endpoint_polynomial_identity (δ y : ℝ)
    (hJ : balanceDenominator δ y ≠ 0) :
    162000000000000000 * balanceDenominator δ y *
      (-evaluatePerturbedHighEndpointExponent δ y - 1 / 1250000000000) =
      evaluateEndpointPolynomial δ y := by
  unfold evaluatePerturbedHighEndpointExponent balancedExponent
    balancedRowCount balancedCutoff evaluateEndpointPolynomial
    evaluateQuadraticCoefficient evaluateLinearCoefficient evaluateConstantCoefficient
  field_simp
  simp only [balanceDenominator, denominator, primeWeight]
  ring

theorem verify_perturbed_endpoint_square_identity (δ y : ℝ) :
    4 * evaluateQuadraticCoefficient y * evaluateEndpointPolynomial δ y =
      (2 * evaluateQuadraticCoefficient y * δ + evaluateLinearCoefficient y) ^ 2 +
        979807389619512241359 + 275799814009247843319007787580888 * y +
        1303439473219357232720782491774728 * y ^ 2 +
        1756569235069508453488622075444704 * y ^ 3 +
        501751386744843713686464752902256 * y ^ 4 := by
  unfold evaluateEndpointPolynomial evaluateQuadraticCoefficient
    evaluateLinearCoefficient evaluateConstantCoefficient
  ring

theorem bound_perturbed_endpoint_polynomial (δ y : ℝ) (hy : 0 ≤ y) :
    0 ≤ evaluateEndpointPolynomial δ y := by
  have hcoefficient : 0 < evaluateQuadraticCoefficient y := by
    unfold evaluateQuadraticCoefficient
    positivity
  have hidentity := verify_perturbed_endpoint_square_identity δ y
  have hright : 0 ≤
      (2 * evaluateQuadraticCoefficient y * δ + evaluateLinearCoefficient y) ^ 2 +
        979807389619512241359 + 275799814009247843319007787580888 * y +
        1303439473219357232720782491774728 * y ^ 2 +
        1756569235069508453488622075444704 * y ^ 3 +
        501751386744843713686464752902256 * y ^ 4 := by
    positivity
  by_contra hnegative
  have hnegative' : evaluateEndpointPolynomial δ y < 0 := lt_of_not_ge hnegative
  have hproduct : 4 * evaluateQuadraticCoefficient y *
      evaluateEndpointPolynomial δ y < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hnegative'
  linarith

theorem bound_perturbed_high_endpoint_exponent (δ y : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 3 / 4)
    (hy : 0 ≤ y) (hy' : y ≤ 1 / 2) :
    evaluatePerturbedHighEndpointExponent δ y ≤ -(1 / 1250000000000) := by
  have hJbounds := balanceDenominator_bounds hδ (by linarith) hy hy'
  have hJ : 0 < balanceDenominator δ y := by linarith [hJbounds.1]
  have hidentity := verify_perturbed_endpoint_polynomial_identity δ y hJ.ne'
  have hpolynomial := bound_perturbed_endpoint_polynomial δ y hy
  have hfactor : 0 < 162000000000000000 * balanceDenominator δ y := by positivity
  nlinarith

theorem bound_high_endpoint_exponent_with_slot_length_shift (t δ y : ℝ)
    (ht : 0 ≤ t) (ht' : t ≤ 42930200831 / 250000000000000)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 3 / 4)
    (hy : 0 ≤ y) (hy' : y ≤ 1 / 2) :
    balancedExponent δ y + 214651 / 5000000000 +
      t * (-1 / 2 + δ + δ * (1 / 2 - y) + 3 * balancedRowCount δ y / 2) +
      (12457523527 / 15625000000000) * (2 / 3 - balancedRowCount δ y) ≤
      -(1 / 1250000000000) := by
  have hJbounds := balanceDenominator_bounds hδ (by linarith) hy hy'
  have hJ : 0 < balanceDenominator δ y := by linarith [hJbounds.1]
  have hcutoff : 1 ≤ balancedCutoff δ y := by
    unfold balancedCutoff
    have hratio : 0 ≤ δ * primeWeight y / (2 * balanceDenominator δ y) := by
      unfold primeWeight
      positivity
    linarith
  have hrow : 1 - δ ≤ balancedRowCount δ y := by
    have hproduct := mul_nonneg
      (show 0 ≤ (5 / 6 : ℝ) - δ by linarith)
      (sub_nonneg.mpr hcutoff)
    unfold balancedRowCount
    nlinarith
  have hq : 0 ≤ δ * (1 / 2 - y) :=
    mul_nonneg hδ (sub_nonneg.mpr hy')
  have hslope : 0 ≤
      -1 / 2 + δ + δ * (1 / 2 - y) + 3 * balancedRowCount δ y / 2 := by
    linarith
  have hcost := mul_le_mul ht' (le_refl _) hslope (le_trans ht ht')
  have hendpoint := bound_perturbed_high_endpoint_exponent δ y hδ hδ' hy hy'
  unfold evaluatePerturbedHighEndpointExponent at hendpoint
  linarith

end SevenEighths.Endpoint

end

end OAI
