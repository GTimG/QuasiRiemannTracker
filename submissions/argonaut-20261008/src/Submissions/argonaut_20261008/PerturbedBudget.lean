import Mathlib

/- A parameterized version of the finite budget construction in the official
   ParametersCentralBudget.lean. This proves scalar parameter existence only. -/
namespace OAI.SevenEighths.CentralPerturbation
noncomputable section

theorem exists_perturbed_central_budget (Δ B H : ℝ)
    (hΔ : 0 < Δ) (hB : 0 < B) (hH0 : 0 ≤ H) (hH1 : H ≤ 1) :
    ∃ t : ℝ, 0 < t ∧ t < Δ / 4 ∧ t ≤ 1 / 100000000 ∧
      ∀ N : ℕ, ∃ allowance : ℝ, 0 < allowance ∧
        ∀ ε e eps : ℝ, 0 ≤ ε → ε ≤ allowance → 0 ≤ e → e ≤ allowance →
          0 ≤ eps → eps ≤ allowance →
          159 * ε + t + t + 7 * t ≤ 1 / 32 ∧
          H * (159 * ε + t + t + 7 * t) + 2 * t + (3 / 2) * (2 * t) +
            (26 * e + (N + 8) * eps + t + t / 6) + (t + t + t) + t < B / 2 := by
  let t := min (Δ / 8) (min (1 / 100000000) (B / 64))
  have ht : 0 < t := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have htΔ : t ≤ Δ / 8 := min_le_left _ _
  have ht1 : t ≤ 1 / 100000000 := (min_le_right _ _).trans (min_le_left _ _)
  have htB : t ≤ B / 64 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨t, ht, by linarith, ht1, ?_⟩
  intro N
  let allowance := t / ((N : ℝ) + 2000)
  have hden : 0 < (N : ℝ) + 2000 := by positivity
  have ha : 0 < allowance := div_pos ht hden
  have ha0 : allowance ≤ t / 2000 :=
    div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hap : allowance * ((N : ℝ) + 2000) = t := by dsimp [allowance]; field_simp
  refine ⟨allowance, ha, ?_⟩
  intro ε e eps hε hεa he hea heps hepsa
  have hεt : 2000 * ε ≤ t := by linarith
  have het : 2000 * e ≤ t := by linarith
  have hepsN : ((N : ℝ) + 2000) * eps ≤ t := by
    have hh := mul_le_mul_of_nonneg_left hepsa hden.le
    nlinarith
  have heps8 : ((N : ℝ) + 8) * eps ≤ t := by nlinarith
  have hcount : 0 ≤ 159 * ε + t + t + 7 * t := by positivity
  have hheight : H * (159 * ε + t + t + 7 * t) ≤ 159 * ε + t + t + 7 * t :=
    mul_le_of_le_one_left hcount hH1
  constructor <;> nlinarith

theorem v6_residual_budget_positive : (0 : ℝ) < 5861 / 4700160000 := by norm_num

theorem exists_v6_central_budget (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ t : ℝ, 0 < t ∧ t < Δ / 4 ∧ t ≤ 1 / 100000000 ∧
      ∀ N : ℕ, ∃ allowance : ℝ, 0 < allowance ∧
        ∀ ε e eps : ℝ, 0 ≤ ε → ε ≤ allowance → 0 ≤ e → e ≤ allowance →
          0 ≤ eps → eps ≤ allowance →
          159 * ε + t + t + 7 * t ≤ 1 / 32 ∧
          (13 / 16 + 3 / 2000000) * (159 * ε + t + t + 7 * t) +
            2 * t + (3 / 2) * (2 * t) +
            (26 * e + (N + 8) * eps + t + t / 6) + (t + t + t) + t <
              (5861 / 4700160000) / 2 :=
  exists_perturbed_central_budget Δ (5861 / 4700160000) (13 / 16 + 3 / 2000000)
    hΔ v6_residual_budget_positive (by norm_num) (by norm_num)

#check exists_perturbed_central_budget
#print axioms exists_perturbed_central_budget
#check exists_v6_central_budget
#print axioms exists_v6_central_budget

end
end OAI.SevenEighths.CentralPerturbation
