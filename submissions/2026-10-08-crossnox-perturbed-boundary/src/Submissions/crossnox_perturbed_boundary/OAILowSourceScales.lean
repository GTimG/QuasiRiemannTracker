/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAILowSourceScales.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIAsymmetricGeometry
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Detector.LowSourceScales

namespace OAI

noncomputable section

namespace SevenEighths.ProbePhysical

open AsymmetricGeometry

lemma perturbed_source_scale_ratio
    (Z t : ℝ) (hZ : 0 < Z) :
    Z ^ (yBase - t / 2) / Z ^ (xBase - t / 2) =
      Z ^ ratioExponent := by
  rw [← Real.rpow_sub hZ]
  congr 1
  dsimp only [xBase, yBase, ratioExponent, compensatedCap, lowBase]
  ring

lemma perturbed_source_scale_square
    (Z t : ℝ) (hZ : 0 < Z) :
    Z ^ (compensatedCap - t / 2) * Z ^ (yBase - t / 2) =
      (Z ^ (xBase - t / 2)) ^ 2 := by
  rw [← Real.rpow_add hZ, ← Real.rpow_natCast,
    ← Real.rpow_mul hZ.le]
  congr 1
  push_cast
  dsimp only [xBase, yBase, ratioExponent, compensatedCap, lowBase]
  ring

lemma perturbed_source_compensated_scale_admissible
    (q Z L t : ℝ) (hq : 1 ≤ q) (hZ : 1 ≤ Z)
    (hL : 1 ≤ L) (hql : q ≤ Z ^ ratioExponent)
    (hLl : L ≤ Z ^ (compensatedCap - t / 2))
    (_ht : 0 ≤ t) (_htSmall : t ≤ 1 / 6) :
    1 ≤ Z ^ (yBase - t / 2) / L ∧
      q * Z ^ (xBase - t / 2) ≤ Z ^ (yBase - t / 2) ∧
      L * Z ^ (yBase - t / 2) ≤
        q ^ 2 * (Z ^ (xBase - t / 2)) ^ 2 := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0 < L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa only [one_mul] using hLl.trans
      (Real.rpow_le_rpow_of_exponent_le hZ
        (show compensatedCap - t / 2 ≤ yBase - t / 2 by
          norm_num [compensatedCap, yBase, skew]))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz _)).mp
    rwa [perturbed_source_scale_ratio Z t hz]
  · calc
      _ ≤ Z ^ (compensatedCap - t / 2) * Z ^ (yBase - t / 2) :=
        mul_le_mul_of_nonneg_right hLl (by positivity)
      _ = (Z ^ (xBase - t / 2)) ^ 2 :=
        perturbed_source_scale_square Z t hz
      _ ≤ _ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma perturbed_source_gram_power
    (Z t δ : ℝ) (hZ : 0 < Z) :
    Z ^ (xBase - t / 2) *
      (Z ^ ratioExponent) ^ (1 / 6 : ℝ) *
      (Z ^ (yBase - t / 2)) ^ δ =
        Z ^ (2 * lowBase - t / 2 + (yBase - t / 2) * δ) := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  dsimp only [xBase, yBase, ratioExponent, compensatedCap, lowBase]
  ring

lemma perturbed_source_gram_sqrt_power
    (Z t δ : ℝ) (hZ : 0 < Z) :
    Real.sqrt (Z ^ (2 * lowBase - t / 2 +
      (yBase - t / 2) * δ)) =
      Z ^ (lowBase - t / 4 +
        (yBase / 2 - t / 4) * δ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
  congr 1
  dsimp only [xBase, yBase, ratioExponent, compensatedCap, lowBase]
  ring

lemma perturbed_source_compensated_gram_scale
    (q Z L t δ : ℝ) (hq : 1 ≤ q) (hZ : 1 ≤ Z)
    (hL : 1 ≤ L) (hql : q ≤ Z ^ ratioExponent)
    (hLl : L ≤ Z ^ (compensatedCap - t / 2))
    (ht : 0 ≤ t) (htSmall : t ≤ 1 / 6) (hδ : 0 ≤ δ) :
    (q * (Z ^ (xBase - t / 2) / L) *
        (Z ^ (yBase - t / 2) / L) /
        (Z ^ (yBase - t / 2) / L)) *
      (1 +
        ((Z ^ (yBase - t / 2) / L) ^ 2 /
          (q * (Z ^ (xBase - t / 2) / L) *
            (Z ^ (yBase - t / 2) / L))) ^ (1 / 6 : ℝ) +
        ((Z ^ (yBase - t / 2) / L) ^ 2 /
          (q * (Z ^ (xBase - t / 2) / L) *
            (Z ^ (yBase - t / 2) / L))) ^ 2 /
          (Z ^ (yBase - t / 2) / L)) *
      (Z ^ (yBase - t / 2) / L) ^ δ ≤
        (3 * q / L) *
          Z ^ (2 * lowBase - t / 2 + (yBase - t / 2) * δ) := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_, hqp, htail⟩ :=
    perturbed_source_compensated_scale_admissible
      q Z L t hq hZ hL hql hLl ht htSmall
  have hb := compensated_gram_scale_bound q
    (Z ^ (xBase - t / 2)) (Z ^ (yBase - t / 2)) L δ
    hq0 (by positivity) (by positivity) hL hδ hqp htail
  apply hb.trans
  have hratio :
      Z ^ (yBase - t / 2) /
        (q * Z ^ (xBase - t / 2)) ≤ Z ^ ratioExponent := by
    rw [← perturbed_source_scale_ratio Z t hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow
    (by positivity : 0 ≤ Z ^ (yBase - t / 2) /
      (q * Z ^ (xBase - t / 2)))
    hratio (show 0 ≤ (1 / 6 : ℝ) by norm_num)
  calc
    _ ≤ 3 * (q * Z ^ (xBase - t / 2) / L) *
        (Z ^ ratioExponent) ^ (1 / 6 : ℝ) *
        (Z ^ (yBase - t / 2)) ^ δ := by gcongr
    _ = (3 * q / L) *
        (Z ^ (xBase - t / 2) *
          (Z ^ ratioExponent) ^ (1 / 6 : ℝ) *
          (Z ^ (yBase - t / 2)) ^ δ) := by ring
    _ = _ := by rw [perturbed_source_gram_power Z t δ hz]

lemma perturbed_lowGramFactor_source_bound
    (C : CalibrationData) (Z L t δ : ℝ) (hZ : 1 ≤ Z)
    (hL : 1 ≤ L)
    (hql : elementNorm C.generator ≤ Z ^ ratioExponent)
    (hLl : L ≤ Z ^ (compensatedCap - t / 2))
    (ht : 0 ≤ t) (htSmall : t ≤ 1 / 6) (hδ : 0 ≤ δ) :
    lowGramFactor C (Z ^ (xBase - t / 2) / L)
      (Z ^ (yBase - t / 2) / L) δ ≤
        Real.sqrt (3 * elementNorm C.generator / L) *
          Z ^ (lowBase - t / 4 +
            (yBase / 2 - t / 4) * δ) := by
  apply (Real.sqrt_le_sqrt (perturbed_source_compensated_gram_scale
    _ Z L t δ (calibration_elementNorm_ge_one C) hZ hL hql hLl
    ht htSmall hδ)).trans_eq
  rw [Real.sqrt_mul
      (show 0 ≤ 3 * elementNorm C.generator / L by
        unfold elementNorm
        positivity),
    perturbed_source_gram_sqrt_power Z t δ
      (lt_of_lt_of_le zero_lt_one hZ)]

lemma eventually_perturbed_compensated_source_scales
    (C : CalibrationData) (B t : ℝ)
    (ht : 0 ≤ t) (htSmall : t < 1 / 24) :
    ∀ᶠ Z : ℝ in Filter.atTop,
      1 ≤ Z ∧ elementNorm C.generator ≤ Z ^ ratioExponent ∧
      ∀ L : ℝ, 1 ≤ L → L ≤ B * Z ^ (1 / 6 + t) →
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
  have hmargin : 0 < (1 / 16 + 3 * skew - 3 * t / 2) := by
    have hs : 0 ≤ skew := by norm_num [skew]
    linarith
  have hq := (tendsto_rpow_atTop (show 0 < ratioExponent by norm_num [ratioExponent, skew])).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop hmargin).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), hq, hb]
    with Z hZ hq hb
  refine ⟨hZ, hq, ?_⟩
  intro L hL hLB
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L ≤ Z ^ (compensatedCap - t / 2) := calc
    L ≤ B * Z ^ (1 / 6 + t) := hLB
    _ ≤ Z ^ (1 / 16 + 3 * skew - 3 * t / 2) * Z ^ (1 / 6 + t) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = Z ^ (compensatedCap - t / 2) := by
      rw [← Real.rpow_add hz]
      congr 1
      dsimp only [compensatedCap]
      ring
  obtain ⟨hy, hp, _⟩ :=
    perturbed_source_compensated_scale_admissible _ Z L t
      (calibration_elementNorm_ge_one C) hZ hL hq hLl
      ht (by linarith)
  refine ⟨hy, ?_, fun δ hδ =>
    perturbed_lowGramFactor_source_bound C Z L t δ hZ hL hq hLl
      ht (by linarith) hδ⟩
  rw [lowPhysicalScale, compensated_gram_ratio _ _ _ _
    (calibration_elementNorm_pos C) (by positivity) (by positivity) hl]
  exact (le_div_iff₀
    (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr
      (by simpa using hp)

end SevenEighths.ProbePhysical

end

end OAI
