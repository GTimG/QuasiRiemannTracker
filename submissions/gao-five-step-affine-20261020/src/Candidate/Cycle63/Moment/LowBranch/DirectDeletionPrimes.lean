/- The second-transform primes of a LOW child pay the width reduction of its direct deletion at the rate `κq`, except the
squarefree nonunit primes. Released under Apache 2.0. -/
import Mathlib

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle63Moment.LowBranch
noncomputable section
open scoped Classical BigOperators

/-- One prime of the second common part, with own exponent `a`, other exponent `b` and unit indicator `u`, pays
`κq (min a b - u)` of the width reduction from `(a - 1) + κq (a - min a b + u)`, unless it is squarefree and nonunit. -/
theorem prime_type_reserve {κq : ℝ} (hκq : 0 ≤ κq) (hκq2 : κq ≤ 1 / 2) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hneq : a ≠ b → 6 ∣ min a b) {u : ℝ} (hu : u = 0 ∨ u = 1)
    (hsq : ¬ (a = 1 ∧ b = 1 ∧ u = 0)) :
    κq * (((min a b : ℕ) : ℝ) - u) ≤ ((a : ℝ) - 1) + κq * (((a : ℝ) - ((min a b : ℕ) : ℝ)) + u) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have h6 : 6 ∣ a := by simpa [min_eq_left hlt.le] using hneq hlt.ne
    have ha6 : 6 ≤ a := Nat.le_of_dvd (by omega) h6
    have ha6' : (6 : ℝ) ≤ a := by exact_mod_cast ha6
    rw [min_eq_left hlt.le]
    rcases hu with rfl | rfl
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 2 - κq by linarith) (show (0 : ℝ) ≤ a - 6 by linarith)]
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - κq by linarith) (show (0 : ℝ) ≤ a - 1 by linarith)]
  · subst heq
    rw [min_self]
    rcases hu with rfl | rfl
    · have ha2 : 2 ≤ a := by
        by_contra h
        exact hsq ⟨by omega, by omega, rfl⟩
      have ha2' : (2 : ℝ) ≤ a := by exact_mod_cast ha2
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 2 - κq by linarith) (show (0 : ℝ) ≤ a - 2 by linarith)]
    · nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - κq by linarith) (show (0 : ℝ) ≤ a - 1 by linarith)]
  · have h6 : 6 ∣ b := by simpa [min_eq_right hgt.le] using hneq hgt.ne'
    have hb6 : 6 ≤ b := Nat.le_of_dvd (by omega) h6
    have hb6' : (6 : ℝ) ≤ b := by exact_mod_cast hb6
    have hab' : (b : ℝ) + 1 ≤ a := by exact_mod_cast hgt
    rw [min_eq_right hgt.le]
    rcases hu with rfl | rfl
    · nlinarith [mul_nonneg hκq (show (0 : ℝ) ≤ a - b by linarith),
        mul_nonneg (show (0 : ℝ) ≤ 1 / 2 - κq by linarith) (show (0 : ℝ) ≤ b by linarith)]
    · nlinarith [mul_nonneg hκq (show (0 : ℝ) ≤ a - b + 1 by linarith),
        mul_nonneg (show (0 : ℝ) ≤ 1 - κq by linarith) (show (0 : ℝ) ≤ b - 1 by linarith)]

/-- The primes of a second common part pay the width reduction `g - t` at the rate `κq`, up to the width `vN` of the
squarefree nonunit primes: `c` and `d` are the own and the other exponents of the primes `S`, `U ⊆ S` the unit set, and
`n i` the logarithm of the norm of the prime `i`; unequal exponents are multiples of six when the correlation is
nonzero. -/
theorem second_prime_reserve {ι : Type*} (S U : Finset ι) (c d : ι → ℕ) (n : ι → ℝ) {κq : ℝ}
    (hκq : 0 ≤ κq) (hκq2 : κq ≤ 1 / 2) (hn : ∀ i ∈ S, 0 ≤ n i) (hc : ∀ i ∈ S, 1 ≤ c i)
    (hd : ∀ i ∈ S, 1 ≤ d i) (hUS : U ⊆ S)
    (hneq : ∀ i ∈ S, c i ≠ d i → 6 ∣ min (c i) (d i)) :
    κq * ((∑ i ∈ S, ((min (c i) (d i) : ℕ) : ℝ) * n i) - (∑ i ∈ U, n i) -
        ∑ i ∈ S, if c i = 1 ∧ d i = 1 ∧ i ∉ U then n i else 0) ≤
      ((∑ i ∈ S, (c i : ℝ) * n i) - ∑ i ∈ S, n i) +
        κq * (((∑ i ∈ S, (c i : ℝ) * n i) - ∑ i ∈ S, ((min (c i) (d i) : ℕ) : ℝ) * n i) + ∑ i ∈ U, n i) := by
  have hUsum : ∑ i ∈ U, n i = ∑ i ∈ S, if i ∈ U then n i else 0 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hUS]
  have hterm : ∀ i ∈ S, κq * (((min (c i) (d i) : ℕ) : ℝ) * n i - (if i ∈ U then n i else 0) -
        (if c i = 1 ∧ d i = 1 ∧ i ∉ U then n i else 0)) ≤
      ((c i : ℝ) - 1) * n i + κq * (((c i : ℝ) - ((min (c i) (d i) : ℕ) : ℝ)) * n i +
        (if i ∈ U then n i else 0)) := by
    intro i hi
    by_cases hsq : c i = 1 ∧ d i = 1 ∧ i ∉ U
    · obtain ⟨h1, h2, h3⟩ := hsq
      simp [h1, h2, h3]
    · have hsq' : ¬ (c i = 1 ∧ d i = 1 ∧ (if i ∈ U then (1 : ℝ) else 0) = 0) := by
        intro h
        apply hsq
        refine ⟨h.1, h.2.1, ?_⟩
        intro hiU
        simp [hiU] at h
      have hu : (if i ∈ U then (1 : ℝ) else 0) = 0 ∨ (if i ∈ U then (1 : ℝ) else 0) = 1 := by
        by_cases hiU : i ∈ U
        · exact Or.inr (by simp [hiU])
        · exact Or.inl (by simp [hiU])
      have h := prime_type_reserve hκq hκq2 (hc i hi) (hd i hi) (hneq i hi) hu hsq'
      have hmul := mul_le_mul_of_nonneg_right h (hn i hi)
      rw [ite_eq_right hsq]
      by_cases hiU : i ∈ U
      · simp only [ite_eq_left hiU] at hmul ⊢
        nlinarith [hmul]
      · simp only [ite_eq_right hiU] at hmul ⊢
        nlinarith [hmul]
  have hsum := Finset.sum_le_sum hterm
  have eL : ∑ i ∈ S, κq * (((min (c i) (d i) : ℕ) : ℝ) * n i - (if i ∈ U then n i else 0) -
      (if c i = 1 ∧ d i = 1 ∧ i ∉ U then n i else 0)) =
      κq * ((∑ i ∈ S, ((min (c i) (d i) : ℕ) : ℝ) * n i) - (∑ i ∈ S, if i ∈ U then n i else 0) -
        ∑ i ∈ S, if c i = 1 ∧ d i = 1 ∧ i ∉ U then n i else 0) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have eR : ∑ i ∈ S, (((c i : ℝ) - 1) * n i + κq * (((c i : ℝ) - ((min (c i) (d i) : ℕ) : ℝ)) * n i +
      (if i ∈ U then n i else 0))) =
      ((∑ i ∈ S, (c i : ℝ) * n i) - ∑ i ∈ S, n i) +
        κq * (((∑ i ∈ S, (c i : ℝ) * n i) - ∑ i ∈ S, ((min (c i) (d i) : ℕ) : ℝ) * n i) +
          ∑ i ∈ S, if i ∈ U then n i else 0) := by
    simp only [sub_mul, one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hUsum]
  rw [eL, eR] at hsum
  exact hsum

end
end OAI.SevenEighths.Cycle63Moment.LowBranch
