/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SmallSlots

/-! Trivial response bound for every original subproduct. The fixed
coefficient constant can be absorbed after the finite slot type is known;
there is no individual exceptional-character slope hypothesis. -/
namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Set OAI OAI.SevenEighths HeckeFamily CanonicalRowCompletion Deletion26
open CenteredMomentCommonMaskExpansion CenteredMomentWholeSlotDeletion
open CenteredMomentSecondHeightFamily CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O

theorem directPrimeSlot_sq_bound (u : O) (L : Finset (Ideal O))
    (β : Ideal O → ℂ) (P B : ℝ) (hP : 1 ≤ P) (hB : 0 ≤ B)
    (hL : ∀ I ∈ L, I ≠ 0) (hN : ∀ I ∈ L, (I.absNorm:ℝ) ≤ 2*P)
    (hβ : ∀ I ∈ L, ‖β I‖ ≤ B) :
    ‖directPrimeSlot u L β P‖^2 ≤ (256*B)^2*P := by
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hcard := DescentFiberCost.finite_ideal_count_real L (2*P) (by linarith) hL hN
  have hsum : ‖∑ I ∈ L, β I*idealRowHom u I‖ ≤ (L.card:ℝ)*B := by
    calc _ ≤ ∑ I ∈ L, ‖β I*idealRowHom u I‖ := norm_sum_le _ _
      _ ≤ ∑ _I ∈ L, B := Finset.sum_le_sum (fun I hI => by
        rw [norm_mul]
        exact (mul_le_mul (hβ I hI) (idealRowHom_norm _ _) (norm_nonneg _) hB).trans_eq (mul_one B))
      _ = _ := by simp
  have hs : 0<Real.sqrt P := Real.sqrt_pos_of_pos hP0
  have hnorm : ‖directPrimeSlot u L β P‖ ≤ (Real.sqrt P)⁻¹*(256*P*B) := by
    unfold directPrimeSlot
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs.le]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs.le)
    exact hsum.trans (by nlinarith)
  have he : (Real.sqrt P)⁻¹*(256*P*B) = 256*B*Real.sqrt P := by
    apply mul_left_cancel₀ hs.ne'
    rw [mul_inv_cancel_left₀ hs.ne']
    nlinarith [Real.sq_sqrt hP0.le]
  rw [he] at hnorm
  have hh := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  simpa only [mul_pow,Real.sq_sqrt hP0.le] using hh

/-- Root masks are retained literally and only their norm-one bound is
used. This holds for a single slot of any nonnegative live width. -/
theorem normalizedSlot_root_sq_bound (η : Character) (m A root u : O)
    (L : Finset (Ideal O)) (β : Ideal O → ℂ) (t P B : ℝ)
    (hP : 1 ≤ P) (hB : 0 ≤ B) (hL : ∀ I ∈ L,I≠0)
    (hN : ∀ I ∈ L,(I.absNorm:ℝ)≤2*P)
    (hβ : ∀ I∈L,‖heightCoefficient β t I‖≤B) :
    ‖normalizedSlot η m A (u*root^6) L β t P‖^2 ≤ (256*B)^2*P := by
  rw [normalizedSlot_root_eq_direct]
  exact directPrimeSlot_sq_bound _ _ _ _ _ hP hB hL hN
    (fun I hI => maskedDirectCoefficient_norm η m A root β t I B (hβ I hI))

end
end Qrh.JointDetector.RepeatedMarks
