/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.InverseNormalized

/-! Slots shorter than the fixed dictionary modulus have a bounded response.
This is a constant depending on fixed data, not a power cost per slot. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily CanonicalRowCompletion Deletion26
local notation "O" => HeckeFamily.O

theorem directPrimeSlot_small_norm (u : O) (L : Finset (Ideal O))
    (β : Ideal O → ℂ) (P M B : ℝ) (hP : 1 ≤ P) (hPM : P ≤ M) (hB : 0 ≤ B)
    (hL : ∀ I ∈ L, I ≠ 0) (hN : ∀ I ∈ L, (I.absNorm:ℝ) ≤ 2*P)
    (hβ : ∀ I ∈ L, ‖β I‖ ≤ B) :
    ‖directPrimeSlot u L β P‖ ≤ 256*M*B := by
  have hM : 0 ≤ M := by linarith
  have hcard := DescentFiberCost.finite_ideal_count_real L (2*M) (by linarith)
    hL (fun I hI => (hN I hI).trans (by linarith))
  have hinv : (Real.sqrt P)⁻¹ ≤ 1 := by
    have hs : 1 ≤ Real.sqrt P := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa using hP)
    exact inv_le_one_of_one_le₀ hs
  have hsum : ‖∑ I ∈ L, β I*idealRowHom u I‖ ≤ (L.card:ℝ)*B := by
    calc _ ≤ ∑ I ∈ L, ‖β I*idealRowHom u I‖ := norm_sum_le _ _
      _ ≤ ∑ _I ∈ L, B := Finset.sum_le_sum (fun I hI => by
        rw [norm_mul]
        exact (mul_le_mul (hβ I hI) (idealRowHom_norm _ _) (norm_nonneg _) hB).trans_eq (mul_one B))
      _ = _ := by simp
  unfold directPrimeSlot
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  calc _ ≤ (1:ℝ)*((L.card:ℝ)*B) :=
      mul_le_mul hinv hsum (norm_nonneg _) (by norm_num)
    _ ≤ 256*M*B := by nlinarith

end
end Qrh.JointDetector.RepeatedMarks

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

theorem finite_short_factor_cost {ι Row : Type*} [Fintype ι] [DecidableEq ι]
    (rows : Finset Row) (large : Finset ι) (F : ι → Row → ℂ) (D : Row → ℂ)
    (M bound : ℝ) (K : ℕ) (hM : 1 ≤ M) (hK : Fintype.card ι ≤ K)
    (hsmall : ∀ u ∈ rows, ∀ i ∈ (Finset.univ : Finset ι) \ large, ‖F i u‖ ≤ M)
    (hlarge : (∑ u ∈ rows, ‖D u*(∏ i ∈ large, F i u)‖^2) ≤ bound) :
    (∑ u ∈ rows, ‖D u*(∏ i, F i u)‖^2) ≤ M^(2*K)*bound := by
  let small := (Finset.univ : Finset ι) \ large
  have hcard : small.card ≤ K := (Finset.card_le_card
    (Finset.sdiff_subset : small ⊆ Finset.univ)).trans (by simpa using hK)
  have hMN : 0 ≤ M := zero_le_one.trans hM
  have hsmallprod (u : Row) (hu : u ∈ rows) : ‖∏ i ∈ small, F i u‖ ≤ M^K := by
    calc _ ≤ ∏ i ∈ small, ‖F i u‖ := by rw [norm_prod]
      _ ≤ ∏ _i ∈ small, M := Finset.prod_le_prod₀
        (fun _ _ => norm_nonneg _) (fun i hi => hsmall u hu i hi)
      _ = M^small.card := by simp
      _ ≤ M^K := pow_le_pow_right₀ hM hcard
  have hsplit (u : Row) : (∏ i, F i u) =
      (∏ i ∈ large, F i u)*(∏ i ∈ small, F i u) := by
    simpa only [small,mul_comm] using
      (Finset.prod_sdiff (s₁ := large) (s₂ := Finset.univ) (f := fun i => F i u) (Finset.subset_univ large)).symm
  have hpoint (u : Row) (hu : u ∈ rows) :
      ‖D u*(∏ i, F i u)‖^2 ≤ M^(2*K)*‖D u*(∏ i ∈ large,F i u)‖^2 := by
    rw [hsplit,← mul_assoc,norm_mul,mul_pow]
    have hs := pow_le_pow_left₀ (norm_nonneg _) (hsmallprod u hu) 2
    have he : (M^K)^2=M^(2*K) := by rw [←pow_mul]; congr 1; omega
    rw [he] at hs
    nlinarith [sq_nonneg ‖D u*(∏ i ∈ large,F i u)‖]
  calc _ ≤ ∑ u ∈ rows, M^(2*K)*‖D u*(∏ i ∈ large,F i u)‖^2 :=
      Finset.sum_le_sum hpoint
    _ = M^(2*K)*(∑ u ∈ rows, ‖D u*(∏ i ∈ large,F i u)‖^2) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hlarge (pow_nonneg hMN _)

end
end Qrh.JointDetector.RepeatedMarks
