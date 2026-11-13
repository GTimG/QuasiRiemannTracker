/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Grouping

/-!
# Inverse.Poisson.Counting — column counts and label multiplicity

* `prodSpan_injective`: squarefree columns are determined by their ideal.
* `column_card_le`: at most `128 x` columns of norm `≤ x`.
* `column_harmonic_le`: `∑_{N U ≤ x} 1/N U ≤ 256 (log₂ x + 2)` (dyadic blocks).
* `fibre_sum_le`: a fibred weighted sum is bounded by the maximal fibre weight times the row sum.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic
open OAI.FirstPassCubeLabels (primeProductNorm)

local notation "O" => ActualEisensteinCubic.O

/-- Abstract fibre bound (the weighted separation step with squares already formed). -/
theorem fibre_sum_le {L : Type*} (S : Finset L) (yof : L → O) (w : L → ℝ) (F : O → ℝ)
    (T : Finset O) (M : ℝ) (hw : ∀ l ∈ S, 0 ≤ w l) (hF : ∀ y, 0 ≤ F y)
    (hmap : ∀ l ∈ S, yof l ∈ T)
    (hfib : ∀ y ∈ T, ∑ l ∈ S.filter (fun l => yof l = y), w l ≤ M) :
    ∑ l ∈ S, w l * F (yof l) ≤ M * ∑ y ∈ T, F y := by
  rw [← Finset.sum_fiberwise_of_maps_to hmap, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have h : ∑ l ∈ S.filter (fun l => yof l = y), w l * F (yof l) =
      (∑ l ∈ S.filter (fun l => yof l = y), w l) * F y := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    rw [(Finset.mem_filter.mp hl).2]
  rw [h]
  exact mul_le_mul_of_nonneg_right (hfib y hy) (hF y)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

/-- The column ideal `∏_U (p_i)`. -/
def colIdeal (U : Finset ι) : Ideal O := ∏ i ∈ U, Ideal.span {p i}

theorem colIdeal_eq_span (U : Finset ι) : colIdeal p U = Ideal.span {∏ i ∈ U, p i} :=
  Ideal.prod_span_singleton U p

theorem primeProductNorm_eq_absNorm (U : Finset ι) :
    primeProductNorm p U = (Ideal.absNorm (colIdeal p U) : ℝ) := by
  rw [colIdeal_eq_span, FirstPassCubeLabels.primeProductNorm,
    eisEmbedding_norm_sq_eq_absNorm_span]

include hp in
theorem colIdeal_ne_bot (U : Finset ι) : colIdeal p U ≠ ⊥ := by
  rw [colIdeal_eq_span, Ne, Ideal.span_singleton_eq_bot]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)

include hinj in
theorem prodSpan_injective : Function.Injective (colIdeal p) := by
  have hmem : ∀ U V : Finset ι, colIdeal p U = colIdeal p V → ∀ i ∈ U, i ∈ V := by
    intro U V hUV i hi
    have hprime : Prime (Ideal.span {p i}) :=
      Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
    have hdvd : Ideal.span {p i} ∣ colIdeal p V := by
      rw [← hUV]; exact Finset.dvd_prod_of_mem _ hi
    obtain ⟨j, hj, hij⟩ := (hprime.dvd_finset_prod_iff _).mp hdvd
    have hle : Ideal.span {p j} ≤ Ideal.span {p i} := Ideal.le_of_dvd hij
    have heq : Ideal.span {p j} = Ideal.span {p i} :=
      (inferInstance : (Ideal.span {p j}).IsMaximal).eq_of_le
        (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top hle
    have := hinj heq
    rw [← this]; exact hj
  intro U V hUV
  ext i
  exact ⟨hmem U V hUV i, hmem V U hUV.symm i⟩

include hp in
theorem one_le_primeProductNorm_single (i : ι) : 2 ≤ primeProductNorm p {i} := by
  rw [primeProductNorm_eq_absNorm]
  have hne : colIdeal p {i} ≠ ⊤ := by
    simp only [colIdeal, Finset.prod_singleton]
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top
  have h1 : Ideal.absNorm (colIdeal p {i}) ≠ 1 := by
    intro h; exact hne (Ideal.absNorm_eq_one_iff.mp h)
  have h0 : Ideal.absNorm (colIdeal p {i}) ≠ 0 := by
    intro h
    exact colIdeal_ne_bot p hp {i} (Ideal.absNorm_eq_zero_iff.mp h)
  have : 2 ≤ Ideal.absNorm (colIdeal p {i}) := by omega
  exact_mod_cast this

include hp in
theorem two_pow_card_le_primeProductNorm (U : Finset ι) :
    (2 : ℝ) ^ U.card ≤ primeProductNorm p U := by
  induction U using Finset.induction_on with
  | empty => simp [FirstPassCubeLabels.primeProductNorm]
  | @insert i U hi ih =>
    rw [Finset.card_insert_of_notMem hi, Finset.insert_eq,
      FirstPassCubeLabels.primeProductNorm_union p {i} U (Finset.disjoint_singleton_left.mpr hi)]
    have h2 := one_le_primeProductNorm_single p hp i
    calc (2 : ℝ) ^ (U.card + 1) = 2 * 2 ^ U.card := by ring
      _ ≤ primeProductNorm p {i} * primeProductNorm p U :=
        mul_le_mul h2 ih (by positivity) (by linarith)

include hp in
theorem one_le_primeProductNorm (U : Finset ι) : 1 ≤ primeProductNorm p U :=
  le_trans (one_le_pow₀ (by norm_num)) (two_pow_card_le_primeProductNorm p hp U)

include hp hinj in
/-- At most `128 x` squarefree columns of norm `≤ x`. -/
theorem column_card_le (pool : Finset ι) (x : ℝ) (hx : 1 ≤ x) :
    ((pool.powerset.filter (fun U => primeProductNorm p U ≤ x)).card : ℝ) ≤ 128 * x := by
  set S := pool.powerset.filter (fun U => primeProductNorm p U ≤ x)
  have hcard : (S.image (colIdeal p)).card = S.card :=
    Finset.card_image_of_injective S (prodSpan_injective p hinj)
  rw [← hcard]
  apply DescentFiberCost.finite_ideal_count_real _ x hx
  · intro I hI
    obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hI
    exact colIdeal_ne_bot p hp U
  · intro I hI
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hI
    rw [← primeProductNorm_eq_absNorm]
    exact (Finset.mem_filter.mp hU).2

include hp hinj in
/-- Dyadic harmonic bound: `∑_{N U ≤ x} 1/N U ≤ 256 (log₂ x + 2)`. -/
theorem column_harmonic_le (pool : Finset ι) (x : ℝ) (hx : 1 ≤ x) :
    ∑ U ∈ pool.powerset.filter (fun U => primeProductNorm p U ≤ x),
      (primeProductNorm p U)⁻¹ ≤ 256 * (Real.logb 2 x + 2) := by
  set S := pool.powerset.filter (fun U => primeProductNorm p U ≤ x)
  set n : ℕ := Nat.floor (Real.logb 2 x)
  let j : Finset ι → ℕ := fun U => Nat.floor (Real.logb 2 (primeProductNorm p U))
  have hj : ∀ U ∈ S, j U ∈ Finset.range (n + 1) := by
    intro U hU
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.floor_le_floor
    exact Real.logb_le_logb_of_le (by norm_num) (by linarith [one_le_primeProductNorm p hp U])
      (Finset.mem_filter.mp hU).2
  rw [← Finset.sum_fiberwise_of_maps_to hj]
  have hblock : ∀ k ∈ Finset.range (n + 1),
      ∑ U ∈ S.filter (fun U => j U = k), (primeProductNorm p U)⁻¹ ≤ 256 := by
    intro k _
    have hlow : ∀ U ∈ S.filter (fun U => j U = k), (2 : ℝ) ^ k ≤ primeProductNorm p U := by
      intro U hU
      have hjk := (Finset.mem_filter.mp hU).2
      have hpos := one_le_primeProductNorm p hp U
      have h1 : (k : ℝ) ≤ Real.logb 2 (primeProductNorm p U) := by
        rw [← hjk]; exact Nat.floor_le (Real.logb_nonneg (by norm_num) hpos)
      have := (Real.le_logb_iff_rpow_le (by norm_num) (by linarith)).mp h1
      simpa [Real.rpow_natCast] using this
    have hhigh : ∀ U ∈ S.filter (fun U => j U = k), primeProductNorm p U ≤ 2 ^ (k + 1) := by
      intro U hU
      have hjk := (Finset.mem_filter.mp hU).2
      have hpos := one_le_primeProductNorm p hp U
      have h1 : Real.logb 2 (primeProductNorm p U) < (k : ℝ) + 1 := by
        rw [← hjk]; exact Nat.lt_floor_add_one _
      have := (Real.logb_lt_iff_lt_rpow (by norm_num) (by linarith)).mp h1
      have h2 : (2 : ℝ) ^ ((k : ℝ) + 1) = 2 ^ (k + 1) := by
        rw [← Real.rpow_natCast]; push_cast; rfl
      linarith
    have hcount : ((S.filter (fun U => j U = k)).card : ℝ) ≤ 128 * 2 ^ (k + 1) := by
      have hsub : S.filter (fun U => j U = k) ⊆
          pool.powerset.filter (fun U => primeProductNorm p U ≤ 2 ^ (k + 1)) := by
        intro U hU
        refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hU).1).1,
          hhigh U hU⟩
      calc ((S.filter (fun U => j U = k)).card : ℝ)
          ≤ ((pool.powerset.filter (fun U => primeProductNorm p U ≤ 2 ^ (k + 1))).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ 128 * 2 ^ (k + 1) := column_card_le p hp hinj pool _ (one_le_pow₀ (by norm_num))
    calc ∑ U ∈ S.filter (fun U => j U = k), (primeProductNorm p U)⁻¹
        ≤ ∑ U ∈ S.filter (fun U => j U = k), ((2 : ℝ) ^ k)⁻¹ := by
          apply Finset.sum_le_sum
          intro U hU
          exact inv_anti₀ (by positivity) (hlow U hU)
      _ = ((S.filter (fun U => j U = k)).card : ℝ) * ((2 : ℝ) ^ k)⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 128 * 2 ^ (k + 1) * ((2 : ℝ) ^ k)⁻¹ :=
          mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = 256 := by rw [pow_succ]; field_simp; ring
  calc ∑ k ∈ Finset.range (n + 1), ∑ U ∈ S.filter (fun U => j U = k), (primeProductNorm p U)⁻¹
      ≤ ∑ _k ∈ Finset.range (n + 1), (256 : ℝ) := Finset.sum_le_sum hblock
    _ = 256 * ((n : ℝ) + 1) := by rw [Finset.sum_const, Finset.card_range]; push_cast; ring
    _ ≤ 256 * (Real.logb 2 x + 2) := by
      have hn : (n : ℝ) ≤ Real.logb 2 x := Nat.floor_le (Real.logb_nonneg (by norm_num) hx)
      linarith

end
end Qrh.MarkedAnchor.Inverse.Poisson
