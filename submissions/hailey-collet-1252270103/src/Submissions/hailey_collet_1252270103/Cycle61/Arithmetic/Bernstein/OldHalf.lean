import Submissions.hailey_collet_1252270103.Cycle61.Arithmetic.Bernstein.Basis

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Cycle61.Arithmetic.Bernstein

/- Exact rational data from input/packet/references/37-endpoint-receipt.json.
Each identity below is proved by polynomial normalization in Lean. -/
noncomputable def oldHalfPower (δ p : ℝ) : ℝ :=
  (164704411363/300000000000) +
  (-349928192406836629/1012124700000000000)*p^1 +
  (-633454411363/750000000000)*δ^1 +
  (107120527459913371/843437250000000000)*δ^1*p^1 +
  (2803219410411998803/11382182315001000000)*δ^1*p^2 +
  (1/2)*δ^2 +
  (-499448321803/1686874500000)*δ^2*p^1 +
  (297270303197/1686874500000)*δ^2*p^2 +
  (-407040606394/3794060771667)*δ^2*p^3

noncomputable def oldHalfMinimum : ℝ := 130800958135492294036529/2529373847778000000000000

theorem oldHalfMinimum_pos : 0 < oldHalfMinimum := by
  norm_num [oldHalfMinimum]

noncomputable def oldHalfCoefficients0 : Fin 3 → Fin 4 → ℝ :=
  ![![(164704411363/300000000000 : ℝ), (2984099866382222693/6072748200000000000 : ℝ), (164635729623461629/379546762500000000 : ℝ), (152282898771236629/404849880000000000 : ℝ)],
    ![(1393724993171/6000000000000 : ℝ), (22177990710916496233/121454964000000000000 : ℝ), (14819387342378102103241/105390576990750000000000 : ℝ), (1613563104743770457725537/15176243086668000000000000 : ℝ)],
    ![(590430879541/3000000000000 : ℝ), (7730958273509144303/60727482000000000000 : ℝ), (463564320853744121541643/5691091157500500000000000 : ℝ), (130800958135492294036529/2529373847778000000000000 : ℝ)]]

theorem oldHalfCoefficients0_lower (i : Fin 3) (j : Fin 4) :
    oldHalfMinimum ≤ oldHalfCoefficients0 i j := by
  fin_cases i <;> fin_cases j <;> norm_num [oldHalfMinimum, oldHalfCoefficients0]

theorem oldHalfIdentity0 (δ p : ℝ) :
    oldHalfPower δ p = tensor oldHalfCoefficients0
      ((δ-(0))/((3/4)-(0))) ((p-(0))/((1/2)-(0))) := by
  norm_num [oldHalfPower, tensor, basis2, basis3,
    oldHalfCoefficients0, Fin.sum_univ_succ]
  ring

theorem oldHalfBox0_pos {δ p : ℝ}
    (hδ : δ ∈ Set.Icc (0) (3/4)) (hp : p ∈ Set.Icc (0) (1/2)) :
    0 < oldHalfPower δ p := by
  rw [oldHalfIdentity0]
  exact tensor_pos oldHalfMinimum_pos
    (normalize_mem (by norm_num) hδ) (normalize_mem (by norm_num) hp)
    oldHalfCoefficients0_lower

end Cycle61.Arithmetic.Bernstein
