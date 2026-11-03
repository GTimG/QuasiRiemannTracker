/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/DistinctSlots.lean
Original SHA-256: a66f1e533a17513af5dda81103c7fce5b54dc0b8264def911506acf0928f79d9
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersSlotLengths

/-! Distinct physical slot lengths at any prescribed positive finite size.
This resolves the injective-length API of the upstream actual prime-pool
estimates while retaining the tuned total and an explicit minimum length. -/

namespace LW56e2.Transport.PhysicalHigh
noncomputable section
open scoped BigOperators

theorem distinct_slots_for_size (total : ℝ) (htotal : 0 < total)
    (K : ℕ) (hK : 0 < K) :
    ∃ ell : Fin K → ℝ, Function.Injective ell ∧
      (∑ j, ell j) = total ∧
      (∀ j, total / (2 * K) ≤ ell j ∧ ell j < 2 * total / K) := by
  have hKp : 0 < (K : ℝ) := by exact_mod_cast hK
  let w : Fin K → ℝ := fun j => 1 + (j.val : ℝ) / K
  let A : ℝ := ∑ j, w j
  have hw (j : Fin K) : 1 ≤ w j ∧ w j < 2 := by
    have hj : (j.val : ℝ) < K := by exact_mod_cast j.isLt
    have hdiv : (j.val : ℝ) / K < 1 := (div_lt_one hKp).mpr hj
    dsimp only [w]
    constructor
    · linarith [div_nonneg (Nat.cast_nonneg j.val) hKp.le]
    · linarith
  have hAlo : (K : ℝ) ≤ A := by
    calc
      _ = ∑ _j : Fin K, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => (hw j).1
  have hAhi : A ≤ 2 * K := by
    calc
      _ ≤ ∑ _j : Fin K, (2 : ℝ) := Finset.sum_le_sum fun j _ => (hw j).2.le
      _ = _ := by simp; ring
  have hAp : 0 < A := hKp.trans_le hAlo
  let ell : Fin K → ℝ := fun j => total * w j / A
  refine ⟨ell, ?_, ?_, ?_⟩
  · intro j k he
    have hmul : total * w j = total * w k := (div_left_inj' hAp.ne').mp he
    have hwjk : w j = w k := mul_left_cancel₀ htotal.ne' hmul
    have hjk : (j.val : ℝ) / K = (k.val : ℝ) / K := by
      dsimp [w] at hwjk
      linarith
    have he' : (j.val : ℝ) = (k.val : ℝ) := (div_left_inj' hKp.ne').mp hjk
    apply Fin.ext
    exact_mod_cast he'
  · dsimp only [ell]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    change total * A / A = total
    exact mul_div_cancel_right₀ total hAp.ne'
  · intro j
    constructor
    · calc
        total / (2 * K) ≤ total / A :=
          div_le_div_of_nonneg_left htotal.le hAp hAhi
        _ ≤ total * w j / A :=
          div_le_div_of_nonneg_right (by nlinarith [(hw j).1]) hAp.le
    · calc
        ell j < 2 * total / A :=
          (div_lt_div_iff_of_pos_right hAp).mpr (by nlinarith [(hw j).2])
        _ ≤ 2 * total / K :=
          div_le_div_of_nonneg_left (by positivity) hKp hAlo

end
end LW56e2.Transport.PhysicalHigh
