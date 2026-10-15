import Submissions.argonaut_20261008.PerturbedBudget

namespace OAI.SevenEighths.CentralPerturbation
noncomputable section

theorem exists_perturbed_central_budget_with_slots (Δ B H E : ℝ)
    (hΔ : 0 < Δ) (hB : 0 < B) (hH0 : 0 ≤ H) (hH1 : H ≤ 1)
    (_hE0 : 0 ≤ E) (hE1 : E ≤ 1) :
    ∃ t : ℝ, 0 < t ∧ t < Δ / 4 ∧ t ≤ 1 / 100000000 ∧
      ∀ N : ℕ, ∃ allowance : ℝ, 0 < allowance ∧
        ∀ ε e eps : ℝ, 0 ≤ ε → ε ≤ allowance → 0 ≤ e → e ≤ allowance →
          0 ≤ eps → eps ≤ allowance →
          159 * ε + t + t + 7 * t ≤ 1 / 32 ∧
          H * (159 * ε + t + t + 7 * t) + 2 * t + (3 / 2) * (2 * t) +
            (26 * e + (N + 8) * eps + t + E * t) + (t + t + t) + t < B / 2 := by
  obtain ⟨t, ht, htΔ, ht1, hallow⟩ := exists_perturbed_central_budget
    Δ (B / 2) H hΔ (by positivity) hH0 hH1
  refine ⟨t, ht, htΔ, ht1, ?_⟩
  intro N
  obtain ⟨allowance, ha, hbudget⟩ := hallow N
  refine ⟨allowance, ha, ?_⟩
  intro ε e eps hε hεa he hea heps hepsa
  obtain ⟨hc, hb⟩ := hbudget ε e eps hε hεa he hea heps hepsa
  have hEt : E * t ≤ t := mul_le_of_le_one_left ht.le hE1
  have hh : 0 ≤ H * (159 * ε + t + t + 7 * t) :=
    mul_nonneg hH0 (by positivity)
  have hn : 0 ≤ ((N : ℝ) + 8) * eps := mul_nonneg (by positivity) heps
  refine ⟨hc, ?_⟩
  nlinarith

theorem exists_concrete_budget_with_slots (Δ : ℝ) (hΔ : 0 < Δ) :
    ∃ t : ℝ, 0 < t ∧ t < Δ / 4 ∧ t ≤ 1 / 100000000 ∧
      ∀ N : ℕ, ∃ allowance : ℝ, 0 < allowance ∧
        ∀ ε e eps : ℝ, 0 ≤ ε → ε ≤ allowance → 0 ≤ e → e ≤ allowance →
          0 ≤ eps → eps ≤ allowance →
          159 * ε + t + t + 7 * t ≤ 1 / 32 ∧
          (13 / 16 + 3 / 2000000) * (159 * ε + t + t + 7 * t) +
            2 * t + (3 / 2) * (2 * t) +
            (26 * e + (N + 8) * eps + t + (1 / 6 + 1 / 1000000) * t) +
            (t + t + t) + t < (5861 / 4700160000) / 2 :=
  exists_perturbed_central_budget_with_slots Δ (5861 / 4700160000)
    (13 / 16 + 3 / 2000000) (1 / 6 + 1 / 1000000) hΔ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#check exists_perturbed_central_budget_with_slots
#print axioms exists_perturbed_central_budget_with_slots
#check exists_concrete_budget_with_slots
#print axioms exists_concrete_budget_with_slots
end
end OAI.SevenEighths.CentralPerturbation
