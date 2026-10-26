import Mathlib.Tactic

namespace Cycle61.Arithmetic.Bernstein

noncomputable def basis2 (u : ℝ) : Fin 3 → ℝ :=
  ![(1-u)^2, 2*u*(1-u), u^2]

noncomputable def basis3 (v : ℝ) : Fin 4 → ℝ :=
  ![(1-v)^3, 3*v*(1-v)^2, 3*v^2*(1-v), v^3]

noncomputable def tensor (c : Fin 3 → Fin 4 → ℝ) (u v : ℝ) : ℝ :=
  ∑ i, ∑ j, c i j * (basis2 u i * basis3 v j)

theorem basis2_nonneg {u : ℝ} (hu : u ∈ Set.Icc 0 1) (i : Fin 3) :
    0 ≤ basis2 u i := by
  have hu0 : 0 ≤ u := hu.1
  have hu1 : 0 ≤ 1-u := by linarith [hu.2]
  fin_cases i <;> simp [basis2] <;> positivity

theorem basis3_nonneg {v : ℝ} (hv : v ∈ Set.Icc 0 1) (j : Fin 4) :
    0 ≤ basis3 v j := by
  have hv0 : 0 ≤ v := hv.1
  have h : 0 ≤ 1-v := by linarith [hv.2]
  fin_cases j <;> simp [basis3] <;> positivity

theorem basis2_partition (u : ℝ) : (∑ i, basis2 u i) = 1 := by
  simp [basis2, Fin.sum_univ_succ]
  ring

theorem basis3_partition (v : ℝ) : (∑ j, basis3 v j) = 1 := by
  simp [basis3, Fin.sum_univ_succ]
  ring

theorem tensor_partition (u v : ℝ) :
    (∑ i, ∑ j, basis2 u i * basis3 v j) = 1 := by
  simp_rw [← Finset.mul_sum]
  rw [basis3_partition]
  simp only [mul_one]
  exact basis2_partition u

theorem tensor_lower_bound {c : Fin 3 → Fin 4 → ℝ} {m u v : ℝ}
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hc : ∀ i j, m ≤ c i j) : m ≤ tensor c u v := by
  have hl : (∑ i : Fin 3, ∑ j : Fin 4, m * (basis2 u i * basis3 v j)) ≤
      tensor c u v := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (hc i j)
      (mul_nonneg (basis2_nonneg hu i) (basis3_nonneg hv j))
  simpa only [← Finset.mul_sum, basis2_partition, basis3_partition, mul_one] using hl

theorem tensor_pos {c : Fin 3 → Fin 4 → ℝ} {m u v : ℝ}
    (hm : 0 < m) (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hc : ∀ i j, m ≤ c i j) : 0 < tensor c u v :=
  hm.trans_le (tensor_lower_bound hu hv hc)

theorem normalize_mem {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Icc a b) :
    (x-a)/(b-a) ∈ Set.Icc 0 1 := by
  have h : 0 < b-a := sub_pos.mpr hab
  constructor
  · exact div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt h)
  · apply (div_le_one h).mpr
    linarith [hx.2]

end Cycle61.Arithmetic.Bernstein
