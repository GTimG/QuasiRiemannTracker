/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAILowSlotScales.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAILowSourceScales
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSlotScales

namespace OAI

noncomputable section

open scoped Classical

namespace SevenEighths.ProbePhysical

open AsymmetricGeometry

open CompletedGauss

local notation "O" => ActualEisensteinCubic.O

lemma perturbed_lowUnselectedProduct_norm_bound
    {K : ℕ} (ell : Fin K → ℝ) (hell : ∀ i, 0 ≤ ell i)
    (t : ℝ) (hsum : ∑ i, ell i ≤ 1 / 6 + t)
    (b Z : ℝ) (hb : 1 ≤ b) (hZ : 1 ≤ Z)
    (slots : Fin K → Finset O)
    (hslots : ∀ i x, x ∈ slots i → elementNorm x ≤ b * Z ^ (ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏ i : J, (a i).val) ≤ b ^ K * Z ^ (1 / 6 + t) := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑ i ∈ J, ell i ≤ 1 / 6 + t :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hell i)).trans hsum
  have hc : J.card ≤ K := by
    simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _ ≤ ∏ i : J, b * Z ^ (ell i.val) :=
      Finset.prod_le_prod₀
        (fun _ _ => by unfold elementNorm; positivity)
        (fun i _ => hslots i.val _ (a i).property)
    _ = b ^ J.card * Z ^ (∑ i ∈ J, ell i) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_coe, ← Real.rpow_sum_of_pos hz,
        Finset.sum_coe_sort]
    _ ≤ b ^ K * Z ^ (1 / 6 + t) :=
      mul_le_mul (pow_le_pow_right₀ hb hc)
        (Real.rpow_le_rpow_of_exponent_le hZ hsub)
        (by positivity) (by positivity)

theorem eventually_perturbed_original_slot_scales
    {K : ℕ} (C : CalibrationData) (ell : Fin K → ℝ)
    (hell : ∀ i, 0 ≤ ell i) (t : ℝ)
    (ht : 0 ≤ t) (htSmall : t < 1 / 24)
    (hsum : ∑ i, ell i ≤ 1 / 6 + t)
    (b : ℝ) (hb : 1 ≤ b) :
    ∀ᶠ Z : ℝ in Filter.atTop,
      1 ≤ Z ∧
      ∀ (slots : Fin K → Finset O)
        (_hslots : ∀ i x, x ∈ slots i → x ≠ 0),
        (∀ i x, x ∈ slots i → elementNorm x ≤ b * Z ^ (ell i)) →
        ∀ (J : Finset (Fin K)) (a : LowUnselectedTuple slots J),
          let L := elementNorm (∏ i : J, (a i).val)
          1 ≤ Z ^ (yBase - t / 2) / L ∧
          1 ≤ (Z ^ (yBase - t / 2) / L) ^ 2 /
            lowPhysicalScale C (Z ^ (xBase - t / 2) / L)
              (Z ^ (yBase - t / 2) / L) ∧
          ∀ δ : ℝ, 0 ≤ δ →
            lowGramFactor C (Z ^ (xBase - t / 2) / L)
              (Z ^ (yBase - t / 2) / L) δ ≤
              Real.sqrt (3 * elementNorm C.generator / L) *
                Z ^ (lowBase - t / 4 +
                  (yBase / 2 - t / 4) * δ) := by
  filter_upwards [eventually_perturbed_compensated_source_scales
    C (b ^ K) t ht htSmall] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro slots hslots hnorm J a
  exact hZ.2.2 _ (lowUnselectedProduct_norm_ge_one slots hslots J a)
    (perturbed_lowUnselectedProduct_norm_bound
      ell hell t hsum b Z hb hZ.1 slots hnorm J a)

end SevenEighths.ProbePhysical

end

end OAI
