/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.CoprimeMass
import Candidate.Local.Qrh.JointDetector.IdealMultiplicity

/-!
# Divisor-selector mass for actual ideal rows

Only labels dividing the row ideal are charged. The total label set may be
arbitrarily large: the loss comes from the row ideal's divisor function.
No comparison of signed pair-mask matrix entries is used.
-/

namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

/-- The actual ideal-divisor selector, for an arbitrary finite label set. -/
def idealDivisorMask {R : Type*} (labels : Finset (Ideal O))
    (row : R → Ideal O) (e : labels) (r : R) : Prop := e.val ∣ row r

/-- Dividing labels inject into the full set of ordinary ideal divisors.
The finite label set itself is not counted. -/
theorem idealDivisorMask_incidence_le {R : Type*}
    (labels : Finset (Ideal O)) (row : R → Ideal O)
    (r : R) (hnonzero : row r ≠ ⊥) :
    (Finset.univ.filter fun e => idealDivisorMask labels row e r).card ≤
      (idealDivisors (row r)).card := by
  apply Finset.card_le_card_of_injOn (fun e : labels => e.val)
  · intro e he
    exact (mem_idealDivisors hnonzero).2 (Finset.mem_filter.mp he).2
  · intro e he f hf h
    exact Subtype.ext h

/-- The row norm range makes the divisor-selector incidence uniformly small. -/
theorem idealDivisorMask_incidence_small_power {R : Type*}
    (labels : Finset (Ideal O)) (row : R → Ideal O)
    (r : R) (hnonzero : row r ≠ ⊥)
    (ε : ℝ) (hε : 0 < ε) (B : ℝ) (hnorm : (Ideal.absNorm (row r) : ℝ) ≤ B) :
    ((Finset.univ.filter fun e => idealDivisorMask labels row e r).card : ℝ) ≤
      idealDivisorConstant ε hε * B ^ ε := by
  calc
    _ ≤ ((idealDivisors (row r)).card : ℝ) := by
      exact_mod_cast idealDivisorMask_incidence_le labels row r hnonzero
    _ ≤ idealDivisorConstant ε hε * (Ideal.absNorm (row r) : ℝ) ^ ε :=
      idealDivisorConstant_bound ε hε (row r) hnonzero
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hε.le)
      (idealDivisorConstant_pos ε hε).le

/-- Coherent divisor-selector Cauchy for arbitrary complex dual row vectors.
Nonzero rows may be non-squarefree and the unit row is retained. -/
theorem idealDivisor_mask_mass_le {R : Type*} [Fintype R]
    (labels : Finset (Ideal O)) (row : R → Ideal O)
    (a b : R → ℂ) (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε)
    (hnonzero : ∀ r, row r ≠ ⊥)
    (hnorm : ∀ r, (Ideal.absNorm (row r) : ℝ) ≤ B) :
    ∑ e : labels, Real.sqrt (maskedEnergy (idealDivisorMask labels row) a e) *
        Real.sqrt (maskedEnergy (idealDivisorMask labels row) b e) ≤
      idealDivisorConstant ε hε * B ^ ε *
        Real.sqrt (∑ r, ‖a r‖ ^ 2) * Real.sqrt (∑ r, ‖b r‖ ^ 2) := by
  exact coprime_mask_mass_le (idealDivisorMask labels row) a b
    (idealDivisorConstant ε hε * B ^ ε)
    (mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg hB ε))
    (fun r => idealDivisorMask_incidence_small_power labels row r (hnonzero r)
      ε hε B (hnorm r))

/-- Sum per-divisor complex bilinear values using the same row-divisor loss. -/
theorem idealDivisor_mask_bilinear_sum_le {R : Type*} [Fintype R]
    (labels : Finset (Ideal O)) (row : R → Ideal O)
    (a b : R → ℂ) (v : labels → ℂ) (B ε K : ℝ)
    (hB : 0 ≤ B) (hε : 0 < ε) (hK : 0 ≤ K)
    (hnonzero : ∀ r, row r ≠ ⊥)
    (hnorm : ∀ r, (Ideal.absNorm (row r) : ℝ) ≤ B)
    (hlocal : ∀ e, ‖v e‖ ≤
      K * Real.sqrt (maskedEnergy (idealDivisorMask labels row) a e) *
        Real.sqrt (maskedEnergy (idealDivisorMask labels row) b e)) :
    ‖∑ e : labels, v e‖ ≤
      K * (idealDivisorConstant ε hε * B ^ ε) *
        Real.sqrt (∑ r, ‖a r‖ ^ 2) * Real.sqrt (∑ r, ‖b r‖ ^ 2) := by
  exact coprime_mask_bilinear_sum_le (idealDivisorMask labels row) a b v
    (idealDivisorConstant ε hε * B ^ ε) K
    (mul_nonneg (idealDivisorConstant_pos ε hε).le (Real.rpow_nonneg hB ε)) hK
    (fun r => idealDivisorMask_incidence_small_power labels row r (hnonzero r)
      ε hε B (hnorm r)) hlocal

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.idealDivisorMask_incidence_le
#print axioms Qrh.JointDetector.idealDivisor_mask_mass_le
#print axioms Qrh.JointDetector.idealDivisor_mask_bilinear_sum_le
