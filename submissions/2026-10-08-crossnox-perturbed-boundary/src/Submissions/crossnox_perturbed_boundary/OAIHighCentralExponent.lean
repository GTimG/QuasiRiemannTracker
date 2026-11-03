/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighCentralExponent.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.CentralMixedMargins
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountEndpoint
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorExponent
import Submissions.crossnox_perturbed_boundary.OAIHighEndpointCertificate

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily
open AsymmetricGeometry
open HeckeDetectorRowCount ProbeCentralExponent

def mixedSourceExponentWithPerturbedLengths
    (t a v d R q : ℝ) : ℝ :=
  (xBase - t / 2) * (1 / 2 - 17 / 50) + a + 17 / 50 - 1 -
    a * (yBase - t / 2) - v * (17 / 50) + v * R +
    v * (a - 1 / 2) + (1 / 6 + t) * (17 / 50 - 1 / 2 + q) +
    (d - v) * R

lemma mixed_source_perturbation_identity
    (t a v d R q : ℝ) :
    mixedSourceExponentWithPerturbedLengths t a v d R q =
      mixedSourceExponent a (v - 3 * t / 2) (d - 3 * t / 2) R q +
        t * (-1 / 2 + (2 * a - 1) + q + 3 * R / 2) +
        skew * (a + 4 / 25) := by
  unfold mixedSourceExponentWithPerturbedLengths mixedSourceExponent
    ProbeCentralExponent.sourceExponent
  simp only [xBase, yBase]
  ring

lemma physical_scale_identity_with_perturbed_lengths
    (Z a e t : ℝ) (hZ : 0 < Z) :
    (Z ^ (xBase - t / 2 : ℝ)) ^ (4 / 25 : ℝ) *
      Z ^ (a + 16 * e - 33 / 50) *
      (Z ^ (yBase - t / 2 : ℝ)) ^ (-a - 6 * e) =
      Z ^ ((25 / 48) * a - 181 / 300 + (105 / 8) * e +
        t * (a / 2 + 3 * e - 2 / 25) + skew * (a + 4 / 25 + 6 * e)) := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  simp only [xBase, yBase]
  ring

lemma balanced_mixed_saving_with_perturbed_lengths
    (δ x loss ζ μ v d t other saving : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 3 / 4)
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 2)
    (hl : 0 ≤ loss) (hl' : loss ≤ 1 / 32)
    (hζ : 0 ≤ ζ) (hv : v ≤ rowBase + 3 * t / 2 + ζ)
    (hμ : 0 ≤ μ) (hdv : d - v ≤ μ) (ht : 0 ≤ t)
    (ht' : t ≤ AsymmetricGeometry.lengthShift)
    (hbudget : (rowBase + 3 * t / 2) * loss + 2 * ζ +
      (3 / 2) * μ + other + saving ≤ highMargin) :
    mixedSourceExponentWithPerturbedLengths t ((1 + δ) / 2) v d
      (Endpoint.balancedRowCount δ (1 / 2 - x) + loss) (δ * x) +
      other ≤ lowBase-boundaryReduction - saving := by
  let h := rowBase + 3 * t / 2
  let R0 := Endpoint.balancedRowCount δ (1 / 2 - x)
  let R := Endpoint.balancedRowCount δ (1 / 2 - x) + loss
  have hr := balanced_count_range δ x 0 loss hδ (by linarith) hx hx'
    (by norm_num) (by norm_num) hl hl'
  simp only [zero_div, add_zero] at hr
  change 1 - δ ≤ R ∧ R ≤ 3 / 2 at hr
  have hR : 0 ≤ R := by linarith [hr.1]
  have hslo : 0 ≤ R + δ / 2 - 17 / 50 := by linarith [hr.1]
  have hshi : R + δ / 2 - 17 / 50 ≤ 2 := by linarith [hr.2]
  have he := Endpoint.bound_high_endpoint_exponent_with_slot_length_shift
    t δ (1 / 2 - x) ht ht' hδ hδ' (by linarith) (by linarith)
  have hendpoint : mixedSourceExponentWithPerturbedLengths t ((1 + δ) / 2)
      h h R0 (δ * x) ≤ lowBase-boundaryReduction - highMargin := by
    have hid : mixedSourceExponentWithPerturbedLengths t ((1 + δ) / 2)
        h h R0 (δ * x) = lowBase + Endpoint.balancedExponent δ (1 / 2 - x) +
          t * (-1 / 2 + δ + δ * x + 3 * R0 / 2) + skew * (2 / 3 - R0) := by
      unfold mixedSourceExponentWithPerturbedLengths h R0 Endpoint.balancedExponent
      simp only [xBase, yBase, rowBase, lowBase]
      ring
    rw [hid]
    dsimp [R0] at *
    nlinarith only [he]
  have hfrequency := mul_le_mul_of_nonneg_right
    (show v - h ≤ ζ by dsimp [h]; linarith) hslo
  have hfrequency_cap := mul_le_mul_of_nonneg_left hshi hζ
  have hslack := mul_le_mul_of_nonneg_right hdv hR
  have hslack_cap := mul_le_mul_of_nonneg_left hr.2 hμ
  have hid : mixedSourceExponentWithPerturbedLengths t ((1 + δ) / 2) v d R (δ * x) =
      mixedSourceExponentWithPerturbedLengths t ((1 + δ) / 2) h h R0 (δ * x) +
        h * loss + (v - h) * (R + δ / 2 - 17 / 50) + (d - v) * R := by
    unfold mixedSourceExponentWithPerturbedLengths h R R0
    ring
  change h * loss + 2 * ζ + (3 / 2) * μ + other + saving ≤ highMargin at hbudget
  change mixedSourceExponentWithPerturbedLengths t ((1 + δ) / 2) v d R (δ * x) +
    other ≤ lowBase-boundaryReduction - saving
  rw [hid]
  linarith

lemma perturbed_class_exponent_identity (N : ℕ)
    (a v d R q e eps loss mesh overhead t : ℝ) :
    ((25 / 48) * a - 181 / 300 + (105 / 8) * e +
      t * (a / 2 + 3 * e - 2 / 25) + skew * (a + 4 / 25 + 6 * e)) +
      (overhead + d * R + v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) +
        loss + (1 / 6 + t) * (-(4 / 25 : ℝ) + q + mesh)) =
    mixedSourceExponentWithPerturbedLengths t a v d R q +
      ProbeCentralExponent.realLoss N v e eps loss mesh + overhead +
        t * (3 * e + mesh) + 6 * skew * e := by
  unfold mixedSourceExponentWithPerturbedLengths ProbeCentralExponent.realLoss
  simp only [xBase, yBase]
  ring

lemma balanced_adaptive_saving_with_perturbed_lengths (N : ℕ)
    (a q ε εm slotMesh ν ζ μ v d e eps loss mesh overhead t saving : ℝ)
    (ha : 1 / 2 < a) (ha' : a ≤ 7 / 8)
    (hq : 0 ≤ q) (hq' : q ≤ (2 * a - 1) / 2)
    (hε : 0 ≤ ε) (hεm : 0 ≤ εm)
    (hslot : 0 ≤ slotMesh) (hν : 0 ≤ ν)
    (hcount : 159 * ε + εm + slotMesh + 7 * ν ≤ 1 / 32)
    (hζ : 0 ≤ ζ) (hv : v ≤ rowBase + 3 * t / 2 + ζ)
    (hv1 : v ≤ 1)
    (hμ : 0 ≤ μ) (hdv : d - v ≤ μ) (ht : 0 ≤ t)
    (ht' : t ≤ AsymmetricGeometry.lengthShift)
    (he : 0 ≤ e) (heps : 0 ≤ eps)
    (hbudget : (rowBase + 3 * t / 2) * (159 * ε + εm + slotMesh + 7 * ν) +
      2 * ζ + (3 / 2) * μ +
      (26 * e + (N + 8) * eps + loss + mesh / 6) + overhead + saving +
      t * (3 * e + mesh) + 6 * skew * e ≤ highMargin) :
    mixedSourceExponentWithPerturbedLengths t a v d
      (adaptiveRowExponent (2 * a - 1) q 0 ε εm slotMesh ν) q +
      ProbeCentralExponent.realLoss N v e eps loss mesh + overhead +
        t * (3 * e + mesh) + 6 * skew * e ≤ lowBase-boundaryReduction - saving := by
  have hδ : 0 < 2 * a - 1 := by linarith
  have hδ' : 2 * a - 1 ≤ 3 / 4 := by linarith
  have hx : 0 ≤ q / (2 * a - 1) := div_nonneg hq hδ.le
  have hx' : q / (2 * a - 1) ≤ 1 / 2 :=
    (div_le_iff₀ hδ).mpr (by linarith)
  have hl : 0 ≤ 159 * ε + εm + slotMesh + 7 * ν := by positivity
  have haeq : (1 + (2 * a - 1)) / 2 = a := by ring
  have hqeq : (2 * a - 1) * (q / (2 * a - 1)) = q :=
    mul_div_cancel₀ q hδ.ne'
  have hr := ProbeCentralExponent.realLoss_bound N v e eps loss mesh
    hv1 he heps
  have hb := balanced_mixed_saving_with_perturbed_lengths
    (2 * a - 1) (q / (2 * a - 1))
    (159 * ε + εm + slotMesh + 7 * ν) ζ μ v d t
    (ProbeCentralExponent.realLoss N v e eps loss mesh + overhead +
      t * (3 * e + mesh) + 6 * skew * e) saving
    hδ.le hδ' hx hx' hl hcount hζ hv hμ hdv ht ht' (by linarith)
  rw [haeq, hqeq] at hb
  simp only [adaptiveRowExponent,
    ite_eq_left (show 2 * a - 1 ≤ 5 / 6 by linarith), zero_div, add_zero]
  simp only [add_assoc] at hb ⊢
  exact hb

end SevenEighths.ProbeHighRowFamily

end

end OAI
