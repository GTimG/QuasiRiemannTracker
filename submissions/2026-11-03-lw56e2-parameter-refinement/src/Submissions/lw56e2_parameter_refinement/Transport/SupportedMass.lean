/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/SupportedMass.lean
Original SHA-256: 131e017f1f8cc2f55cc326d9c4262c0bae9804011c35b252f67bdf544976283d
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Decay of finite sums with lower support

This module proves finite-sum inequalities, not only exponent identities.
The factor q^(-2) is split as q^(-1/2) * q^(-3/2), and a lower
support threshold is used on the first factor. The product theorem is
uniform for finite dependent tuple spaces.

For the manuscript's supported ideals, the remaining q^(-3/2) mass can
be supplied by
OAI.SevenEighths.ProbeGramCommon.supportedIdeal_rpow_finite_bound.
That arithmetic theorem is not imported here: the uniform mass bound is an
explicit hypothesis of the generic interface below. No statement about the
actual reflected row energy is asserted.
-/

namespace LW56e2.Transport.SupportedMass

open scoped BigOperators Classical

noncomputable section

theorem supported_term_le {q T : ℝ} (hT : 0 < T) (hq : T ≤ q) :
    q ^ (-2 : ℝ) ≤ T ^ (-(1 / 2 : ℝ)) * q ^ (-(3 / 2 : ℝ)) := by
  have hq0 : 0 < q := lt_of_lt_of_le hT hq
  have hm : q ^ (-(1 / 2 : ℝ)) ≤ T ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hT hq (by norm_num)
  calc
    q ^ (-2 : ℝ) = q ^ (-(1 / 2 : ℝ)) * q ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add hq0]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hq0.le _)

theorem finite_supported_mass_le {ι : Type*} (F : Finset ι)
    (q : ι → ℝ) {T : ℝ} (hT : 0 < T)
    (hsupport : ∀ i ∈ F, T ≤ q i) :
    (∑ i ∈ F, q i ^ (-2 : ℝ)) ≤
      T ^ (-(1 / 2 : ℝ)) * ∑ i ∈ F, q i ^ (-(3 / 2 : ℝ)) := by
  calc
    _ ≤ ∑ i ∈ F, T ^ (-(1 / 2 : ℝ)) * q i ^ (-(3 / 2 : ℝ)) :=
      Finset.sum_le_sum (fun i hi => supported_term_le hT (hsupport i hi))
    _ = _ := (Finset.mul_sum ..).symm

/-- The threshold is required only at points where the weight is nonzero. -/
theorem finite_weighted_supported_mass_le {ι : Type*} (F : Finset ι)
    (q w : ι → ℝ) {T : ℝ} (hT : 0 < T)
    (hw : ∀ i ∈ F, 0 ≤ w i)
    (hsupport : ∀ i ∈ F, w i ≠ 0 → T ≤ q i) :
    (∑ i ∈ F, w i * q i ^ (-2 : ℝ)) ≤
      T ^ (-(1 / 2 : ℝ)) *
        ∑ i ∈ F, w i * q i ^ (-(3 / 2 : ℝ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hwi : w i = 0
  · simp [hwi]
  · have ht := mul_le_mul_of_nonneg_left
      (supported_term_le hT (hsupport i hi hwi)) (hw i hi)
    calc
      _ ≤ w i * (T ^ (-(1 / 2 : ℝ)) * q i ^ (-(3 / 2 : ℝ))) := ht
      _ = _ := by ring

theorem threshold_power_identity {a Z : ℝ} (ha : 0 < a) (hZ : 0 < Z)
    (ell : ℝ) :
    (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) =
      a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell / 2) := by
  rw [Real.mul_rpow ha.le (Real.rpow_nonneg hZ.le _),
    ← Real.rpow_mul hZ.le]
  congr 2
  ring

theorem finite_scaled_supported_mass_le {ι : Type*} (F : Finset ι)
    (q : ι → ℝ) {a Z : ℝ} (ha : 0 < a) (hZ : 0 < Z) (ell : ℝ)
    (hsupport : ∀ i ∈ F, a * Z ^ ell ≤ q i) :
    (∑ i ∈ F, q i ^ (-2 : ℝ)) ≤
      (a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell / 2)) *
        ∑ i ∈ F, q i ^ (-(3 / 2 : ℝ)) := by
  have ht : 0 < a * Z ^ ell := mul_pos ha (Real.rpow_pos_of_pos hZ _)
  simpa only [threshold_power_identity ha hZ ell] using
    finite_supported_mass_le F q ht hsupport

/-- A bounded three-halves mass gives an actual scale-decaying weighted sum. -/
theorem weighted_mass_decay {ι : Type*} (F : Finset ι)
    (q w : ι → ℝ) {a Z C ell : ℝ}
    (ha : 0 < a) (hZ : 0 < Z)
    (hw : ∀ i ∈ F, 0 ≤ w i)
    (hsupport : ∀ i ∈ F, w i ≠ 0 → a * Z ^ ell ≤ q i)
    (hmass : (∑ i ∈ F, w i * q i ^ (-(3 / 2 : ℝ))) ≤ C) :
    (∑ i ∈ F, w i * q i ^ (-2 : ℝ)) ≤
      (C * a ^ (-(1 / 2 : ℝ))) * Z ^ (-ell / 2) := by
  have ht : 0 < a * Z ^ ell := mul_pos ha (Real.rpow_pos_of_pos hZ _)
  calc
    _ ≤ (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) *
        ∑ i ∈ F, w i * q i ^ (-(3 / 2 : ℝ)) :=
      finite_weighted_supported_mass_le F q w ht hw hsupport
    _ ≤ (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) * C :=
      mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg ht.le _)
    _ = _ := by
      rw [threshold_power_identity ha hZ ell]
      ring

/-- Direct interface for a supplied uniform finite three-halves mass bound.
For supported ideals, the source theorem at exponent -3/2 has exactly this
form. This theorem itself is valid for any index type and real norm function. -/
theorem uniform_mass_bound_gives_decay {ι : Type*} (q : ι → ℝ)
    (hbase : ∃ C : ℝ, 0 < C ∧ ∀ F : Finset ι,
      (∑ i ∈ F, q i ^ (-(3 / 2 : ℝ))) ≤ C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Finset ι) (a Z ell : ℝ),
      0 < a → 0 < Z → (∀ i ∈ F, a * Z ^ ell ≤ q i) →
      (∑ i ∈ F, q i ^ (-2 : ℝ)) ≤
        (C * a ^ (-(1 / 2 : ℝ))) * Z ^ (-ell / 2) := by
  obtain ⟨C, hC, hb⟩ := hbase
  refine ⟨C, hC, ?_⟩
  intro F a Z ell ha hZ hsupport
  simpa only [one_mul] using
    weighted_mass_decay F q (fun _ => 1) ha hZ
      (fun _ _ => zero_le_one) (fun i hi _ => hsupport i hi)
      (by simpa only [one_mul] using hb F)

theorem product_decay {ι : Type*} (J : Finset ι)
    (mass C ell : ι → ℝ) {Z : ℝ} (hZ : 0 < Z)
    (hmass : ∀ i ∈ J, 0 ≤ mass i)
    (hbound : ∀ i ∈ J, mass i ≤ C i * Z ^ (-ell i / 2)) :
    (∏ i ∈ J, mass i) ≤
      (∏ i ∈ J, C i) * Z ^ (-(∑ i ∈ J, ell i) / 2) := by
  calc
    _ ≤ ∏ i ∈ J, C i * Z ^ (-ell i / 2) :=
      Finset.prod_le_prod₀ hmass hbound
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hZ]
      congr 2
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_neg_distrib]

/-- Product of supported masses, expressed as a sum over actual finite tuples. -/
theorem tuple_mass_decay {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (q w : ∀ i, α i → ℝ) (a C ell : ι → ℝ) {Z : ℝ}
    (hZ : 0 < Z) (ha : ∀ i, 0 < a i)
    (hq : ∀ i j, 0 ≤ q i j) (hw : ∀ i j, 0 ≤ w i j)
    (hsupport : ∀ i j, w i j ≠ 0 → a i * Z ^ ell i ≤ q i j)
    (hmass : ∀ i, (∑ j, w i j * q i j ^ (-(3 / 2 : ℝ))) ≤ C i) :
    (∑ t : ∀ i, α i, ∏ i, w i (t i) * q i (t i) ^ (-2 : ℝ)) ≤
      (∏ i, C i * a i ^ (-(1 / 2 : ℝ))) *
        Z ^ (-(∑ i, ell i) / 2) := by
  rw [← Fintype.prod_sum
    (fun (i : ι) (j : α i) => w i j * q i j ^ (-2 : ℝ))]
  apply product_decay Finset.univ _ _ ell hZ
  · intro i hi
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (hw i j) (Real.rpow_nonneg (hq i j) _))
  · intro i hi
    exact weighted_mass_decay Finset.univ (q i) (w i) (ha i) hZ
      (fun j _ => hw i j) (fun j _ => hsupport i j) (hmass i)

theorem half_decay_exponent_nonpos {p d : ℝ}
    (hp : p < 1 / 30) (hd : 0 ≤ d) :
    -d / 2 + max 0 (5 * Geometry.ell p - 1 + d) / 8 ≤ 0 := by
  have hm := Geometry.positive_part_le_subset hp hd
  linarith

/-- Absorbs the specified half-row loss against the support-derived half decay.
This does not assert that a row energy satisfies the specified loss formula. -/
theorem support_decay_absorbs_row_loss {p d Z mass C : ℝ}
    (hp : p < 1 / 30) (hd : 0 ≤ d) (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hmass : mass ≤ C * Z ^ (-d / 2)) :
    mass * Z ^ (max 0 (5 * Geometry.ell p - 1 + d) / 8) ≤ C := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have he := half_decay_exponent_nonpos hp hd
  have hr : Z ^ (-d / 2 + max 0 (5 * Geometry.ell p - 1 + d) / 8) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hZ he
  calc
    _ ≤ (C * Z ^ (-d / 2)) *
        Z ^ (max 0 (5 * Geometry.ell p - 1 + d) / 8) :=
      mul_le_mul_of_nonneg_right hmass (Real.rpow_nonneg hZ0.le _)
    _ = C * Z ^ (-d / 2 + max 0 (5 * Geometry.ell p - 1 + d) / 8) := by
      rw [Real.rpow_add hZ0]
      ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left hr hC
    _ = C := mul_one C

/-- Finite tuple mass with the specified half-row loss fully absorbed. A
subset of physical slots is represented by taking the index type to be that
finite subset. The theorem does not require a bound on the subset cardinality. -/
theorem tuple_mass_with_row_loss {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (q w : ∀ i, α i → ℝ) (a C ell : ι → ℝ) {p Z : ℝ}
    (hp : p < 1 / 30) (hZ : 1 ≤ Z)
    (ha : ∀ i, 0 < a i) (hC : ∀ i, 0 ≤ C i)
    (hell : ∀ i, 0 ≤ ell i)
    (hq : ∀ i j, 0 ≤ q i j) (hw : ∀ i j, 0 ≤ w i j)
    (hsupport : ∀ i j, w i j ≠ 0 → a i * Z ^ ell i ≤ q i j)
    (hmass : ∀ i, (∑ j, w i j * q i j ^ (-(3 / 2 : ℝ))) ≤ C i) :
    (∑ t : ∀ i, α i, ∏ i, w i (t i) * q i (t i) ^ (-2 : ℝ)) *
        Z ^ (max 0 (5 * Geometry.ell p - 1 + (∑ i, ell i)) / 8) ≤
      ∏ i, C i * a i ^ (-(1 / 2 : ℝ)) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  exact support_decay_absorbs_row_loss hp
    (Finset.sum_nonneg (fun i _ => hell i)) hZ
    (Finset.prod_nonneg (fun i _ =>
      mul_nonneg (hC i) (Real.rpow_nonneg (ha i).le _)))
    (tuple_mass_decay q w a C ell hZ0 ha hq hw hsupport hmass)

end

end LW56e2.Transport.SupportedMass
