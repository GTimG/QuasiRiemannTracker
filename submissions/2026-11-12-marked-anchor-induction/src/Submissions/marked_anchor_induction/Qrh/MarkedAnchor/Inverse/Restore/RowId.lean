/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Dict
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.ChildCol

/-!
# Inverse.Restore.RowId — the separated row as child slot product × child polynomial

* **`twSlots_norm_eq`**: with the per-prime identity `hw` (`SlotTerm.slot_term_pos/neg`), the twisted
  injective slot sum of the separated main column has the norm of the canonical injective slot
  product `injSlots u L' β' X` (`TupleSum.twSlots_eq_tuple` + `Dict.injSlots_eq_tuple`; the
  constants are unimodular).
* `childLogTest_cpow`: `childLogTest Φ θ · x^{-1/2} = childLogTest (Φ · x^{-1/2}) θ`.
* Columns at scales `< 1`: `polynomial_unit_profile` (a bump `Φ₀` with `Φ₀ 1 = 1`, `Φ₀ = 0` on
  `[2, ∞)` and at `0` has polynomial `1` at scale `1`: only `(1)` has norm `< 2`) and
  `polynomial_small_bound` (at scales `Y ≤ 1` every inverse polynomial with a profile supported
  below `b` is bounded by a constant depending on `b` and `sup ‖W‖` only).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic
open OAI.SevenEighths.InverseMoment (childLogTest)
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-- **The separated slot sum is the canonical injective slot product (in norm).** -/
theorem twSlots_norm_eq {σ ι : Type} [DecidableEq σ] [Fintype ι] [DecidableEq ι]
    (val : ι ↪ Ideal O) (c : ι → ℂ) (n : ι → ℝ) (hn : ∀ i, 0 < n i) (I : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (Hp θ : ℝ) (hHp : 0 < Hp) (u : O)
    (β' : {i // i ∈ I} → Ideal O → ℂ) (X : {i // i ∈ I} → ℝ) (κ : {i // i ∈ I} → ℂ)
    (hκ : ∀ j, ‖κ j‖ = 1)
    (hw : ∀ j : {i // i ∈ I}, ∀ P ∈ lists j.1,
      CanonicalRowCompletion.idealRowHom u (val P) *
        Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
          ((lists j.1).map val) (β' j) (X j) (val P) =
        κ j * (a j.1 P * (c P * FourierBridge.logPhase θ (Real.log (n P))))) :
    ‖twSlots c n Finset.univ I lists a Hp θ‖ =
      ‖injSlots u (fun j => (lists j.1).map val) β' X‖ := by
  rw [twSlots_eq_tuple c n hn Finset.univ I lists a Hp θ hHp,
    injSlots_eq_tuple val I lists (fun i P => a i P * (c P * FourierBridge.logPhase θ
      (Real.log (n P)))) u β' X κ hw]
  simp only [Finset.subset_univ, if_true]
  rw [norm_mul, norm_mul, FourierBridge.logPhase_norm, norm_prod]
  simp only [hκ, Finset.prod_const_one]

theorem childLogTest_cpow (Φ : ℝ → ℂ) (θ : ℝ) :
    (fun x : ℝ => childLogTest Φ θ x * ((x : ℂ) ^ (-(1/2 : ℂ)))) =
      childLogTest (fun x => Φ x * ((x : ℂ) ^ (-(1/2 : ℂ)))) θ := by
  funext x
  unfold childLogTest
  ring

theorem childLogTest_zero (Φ : ℝ → ℂ) : childLogTest Φ 0 = Φ := by
  funext x
  unfold childLogTest FourierBridge.logPhase
  simp

/-- A unit bump has inverse polynomial `1` at scale `1`. -/
theorem polynomial_unit_profile (χ : Character) (Φ₀ : ℝ → ℂ) (h1 : Φ₀ 1 = 1)
    (h2 : ∀ x, 2 ≤ x → Φ₀ x = 0) :
    polynomial χ true Φ₀ 1 0 0 = 1 := by
  unfold polynomial
  have htop : (⊤ : Ideal O) ≠ 0 := by
    rw [Ideal.zero_eq_bot]; exact top_ne_bot
  rw [tsum_eq_single (⟨⊤, htop⟩ : NonzeroIdeal)]
  · simp only [summand, coefficient, if_true, HeckeDyadic.norm, ← Ideal.one_eq_top,
      UniqueFactorizationMonoid.moebius_one, map_one, Nat.cast_one,
      Int.cast_one, div_one, h1, HeckeDyadic.shift, zero_mul, sub_zero, neg_zero,
      Complex.cpow_zero, Complex.one_cpow, mul_one]
    simp
  · intro I hI
    have hI0 : Ideal.absNorm I.val ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact I.property
    have hI1 : Ideal.absNorm I.val ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      intro h
      exact hI (Subtype.ext h)
    have h2N : (2 : ℝ) ≤ HeckeDyadic.norm I / 1 := by
      rw [div_one]
      unfold HeckeDyadic.norm
      have : 2 ≤ Ideal.absNorm I.val := by omega
      exact_mod_cast this
    simp only [summand, h2 _ h2N, mul_zero, zero_mul]

/-- **Columns at scales `≤ 1` are uniformly bounded.** -/
theorem polynomial_small_bound (b Mw : ℝ) (hb : 0 < b) (hMw : 0 ≤ Mw) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (W : ℝ → ℂ), (∀ x, ‖W x‖ ≤ Mw) → (∀ x, b < x → W x = 0) →
      ∀ (χ : Character) (Y : ℝ), 0 < Y → Y ≤ 1 →
      ‖polynomial χ true W Y 0 0‖ ≤ Cb := by
  have hfin : {I : NonzeroIdeal | HeckeDyadic.norm I ≤ b}.Finite := by
    have hf := Ideal.finite_setOf_absNorm_le (S := O) ⌈b⌉₊
    apply (Set.Finite.preimage (f := fun I : NonzeroIdeal => I.val)
      Subtype.val_injective.injOn hf).subset
    intro I hI
    simp only [Set.mem_setOf_eq] at hI ⊢
    unfold HeckeDyadic.norm at hI
    have : (Ideal.absNorm I.val : ℝ) ≤ ⌈b⌉₊ := hI.trans (Nat.le_ceil b)
    exact_mod_cast this
  set S := hfin.toFinset with hS
  refine ⟨Real.sqrt b * (S.card * Mw), by positivity, ?_⟩
  intro W hW hWs χ Y hY hY1
  unfold polynomial
  have hsupp : ∀ I : NonzeroIdeal, I ∉ S → summand χ true W Y 0 0 I = 0 := by
    intro I hIS
    rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hIS
    have hNY : b < HeckeDyadic.norm I / Y := by
      rw [lt_div_iff₀ hY]
      have := HeckeDyadic.norm_pos I
      nlinarith
    simp only [summand, hWs _ hNY, mul_zero, zero_mul]
  rw [tsum_eq_sum (s := S) (fun I hI => hsupp I hI)]
  by_cases hsmall : Y < 1 / b
  · -- every summand vanishes
    have hz : ∀ I : NonzeroIdeal, summand χ true W Y 0 0 I = 0 := by
      intro I
      have hN1 : 1 ≤ HeckeDyadic.norm I := by
        unfold HeckeDyadic.norm
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
      have hNY : b < HeckeDyadic.norm I / Y := by
        rw [lt_div_iff₀ hY]
        rw [lt_div_iff₀ hb] at hsmall
        nlinarith
      simp only [summand, hWs _ hNY, mul_zero, zero_mul]
    simp only [hz, Finset.sum_const_zero, mul_zero, norm_zero]
    positivity
  push_neg at hsmall
  have hterm : ∀ I ∈ S, ‖summand χ true W Y 0 0 I‖ ≤ Mw := by
    intro I _
    unfold summand
    rw [norm_mul, norm_mul]
    have hc := coefficient_norm_le χ true I.val
    have hcp : ‖(((HeckeDyadic.norm I / Y : ℝ) : ℂ) ^ (-shift 0 0))‖ = 1 := by
      simp [HeckeDyadic.shift]
    rw [hcp, mul_one]
    calc ‖coefficient χ true I.val‖ * ‖W (HeckeDyadic.norm I / Y)‖ ≤ 1 * Mw := by
          gcongr
          exact hW _
      _ = Mw := one_mul _
  have hsum : ‖∑ I ∈ S, summand χ true W Y 0 0 I‖ ≤ S.card * Mw := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have hYb : 1 / b ≤ Y := hsmall
  have hpow : ‖((Y : ℂ) ^ (-(1/2 : ℂ)))‖ ≤ Real.sqrt b := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    have hre : (-(1/2 : ℂ)).re = -(1/2 : ℝ) := by norm_num
    rw [hre, Real.rpow_neg hY.le, ← Real.sqrt_eq_rpow]
    rw [inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr hY), ← Real.sqrt_mul hb.le]
    rw [Real.one_le_sqrt]
    rw [div_le_iff₀ hb] at hYb
    linarith
  rw [norm_mul]
  exact mul_le_mul hpow hsum (norm_nonneg _) (Real.sqrt_nonneg _)

/-- At scales `Y < 1/b` an inverse polynomial with profile vanishing beyond `b` is `0`. -/
theorem polynomial_eq_zero_of_small (χ : Character) (W : ℝ → ℂ) (b Y : ℝ) (hY : 0 < Y)
    (hWs : ∀ x, b < x → W x = 0) (hbY : b * Y < 1) : polynomial χ true W Y 0 0 = 0 := by
  unfold polynomial
  have hz : ∀ I : NonzeroIdeal, summand χ true W Y 0 0 I = 0 := by
    intro I
    have hN1 : 1 ≤ HeckeDyadic.norm I := by
      unfold HeckeDyadic.norm
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
    have hNY : b < HeckeDyadic.norm I / Y := by
      rw [lt_div_iff₀ hY]; nlinarith
    simp only [summand, hWs _ hNY, mul_zero, zero_mul]
  simp only [hz, tsum_zero, mul_zero]

/-- A smooth unit bump at `1`: supported in `[1/2, 3/2]`, `Φ₀ 1 = 1`. -/
theorem exists_unit_bump :
    ∃ Φ₀ : ℝ → ℂ, ContDiff ℝ ∞ Φ₀ ∧ Function.support Φ₀ ⊆ Set.Icc (1/2 : ℝ) (3/2) ∧
      Φ₀ 1 = 1 := by
  obtain ⟨V, _, hV, _, hsupp, hV0⟩ := FourierBridge.exists_complex_smooth_cutoff 0 le_rfl
  refine ⟨fun x => V (2 * (x - 1)), ?_, ?_, ?_⟩
  · exact hV.comp ((contDiff_const.mul (contDiff_id.sub contDiff_const)))
  · intro x hx
    have hx' : 2 * (x - 1) ∈ tsupport V := subset_tsupport V hx
    have h := hsupp hx'
    simp only [zero_add, Set.mem_Icc] at h
    constructor <;> linarith [h.1, h.2]
  · simp [hV0]

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.twSlots_norm_eq
#print axioms Qrh.MarkedAnchor.Inverse.Restore.polynomial_unit_profile
#print axioms Qrh.MarkedAnchor.Inverse.Restore.polynomial_small_bound
#print axioms Qrh.MarkedAnchor.Inverse.Restore.exists_unit_bump
