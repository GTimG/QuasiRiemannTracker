/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
An early upper bank for the genuine prime/zero comparison. -/
import Candidate.C092.transport.LowActualSource

set_option autoImplicit false
namespace QRH.Cycle092.TerminalResponseCeiling
noncomputable section
open scoped Classical BigOperators
open Filter Set

/-- Finite upper exponents precede all arithmetic data and live bands. -/
theorem finite_upper_bank {price : ℝ} (hp : 0 < price) :
    ∃ J : ℕ, ∃ q : Fin J → ℝ,
      (∀ j, 0 ≤ q j ∧ q j ≤ 1) ∧
      ∀ ν : ℝ, 0 ≤ ν → ν ≤ 3/4 → ∃ j, ν ≤ q j ∧ q j ≤ ν+price := by
  let step := min price (1/8:ℝ)
  have hs : 0 < step := lt_min hp (by norm_num)
  let J := ⌊(3/4:ℝ)/step⌋₊+1
  let q : Fin J → ℝ := fun j => ((j.val:ℝ)+1)*step
  refine ⟨J,q,?_,?_⟩
  · intro j
    have hj : j.val ≤ ⌊(3/4:ℝ)/step⌋₊ := Nat.le_of_lt_succ j.isLt
    have hf := Nat.floor_le (div_nonneg (by norm_num : (0:ℝ)≤3/4) hs.le)
    have hb := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) hs.le).trans
      ((le_div_iff₀ hs).mp hf)
    refine ⟨by dsimp [q]; positivity,?_⟩
    have hstep : step ≤ (1/8:ℝ) := min_le_right _ _
    dsimp [q]
    nlinarith
  · intro ν hν hνhi
    let k := ⌊ν/step⌋₊
    have hk : k<J := Nat.lt_succ_of_le
      (Nat.floor_mono (div_le_div_of_nonneg_right hνhi hs.le))
    refine ⟨⟨k,hk⟩,?_,?_⟩
    · have h := (div_lt_iff₀ hs).mp (Nat.lt_floor_add_one (ν/step))
      dsimp [q,k]
      push_cast at h
      exact h.le
    · have h := (le_div_iff₀ hs).mp (Nat.floor_le (div_nonneg hν hs.le))
      have hstep : step ≤ price := min_le_left _ _
      dsimp [q,k]
      nlinarith

#print axioms finite_upper_bank
end
end QRH.Cycle092.TerminalResponseCeiling
