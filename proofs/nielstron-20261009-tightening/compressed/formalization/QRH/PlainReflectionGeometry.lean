/-
Real branch geometry adapted from OpenAI/math, revision
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Apache-2.0,
OAI/NumberTheory/DirichletL/Energy/ReferenceLowBranchGeometry.lean.
Modified here: lower κ endpoint 13/18 and resulting comparison constants.
This does not extend the analytic reflection or moment theorem itself.
-/
import QRH.Geometry

namespace QRH.PlainReflection

 theorem slot_budgets {width total z κ : ℝ} (hz : 0 ≤ z)
    (hk : (13 / 18 : ℝ) ≤ κ) (hlarge : 5 * width / 6 ≤ total + z)
    (hcap : total + z + (6 * κ - 1) * z ≤ width) :
    z ≤ width / 20 ∧ (6 * κ - 1) * z ≤ width / 6 := by
  have hmul : (10 / 3 : ℝ) * z ≤ (6 * κ - 1) * z :=
    mul_le_mul_of_nonneg_right (by linarith) hz
  constructor <;> nlinarith

 theorem reflected_low {width short along ell z κ ξ reflected : ℝ}
    (hM : 0 ≤ width) (hsM : short ≤ width / 4) (hze : z ≤ ell)
    (hk : (13 / 18 : ℝ) ≤ κ) (he : ell ≤ width / 20)
    (hbudget : (6 * κ - 1) * ell ≤ width / 6) (hξ : 0 ≤ ξ)
    (hhigh : 5 * width / 6 < short + max 0 along + z)
    (href : reflected ≤ max 0 (width - along + ξ)) :
    0 < along ∧ reflected + short + z ≤ 23 * width / 30 + ξ ∧
      reflected + short + 6 * κ * z ≤ 14 * width / 15 + ξ := by
  have haz : 0 < along := by
    by_contra hn
    have ha : along ≤ 0 := le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget : (6 * κ - 1) * z ≤ width / 6 :=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap : z ≤ width / 20 := hze.trans he
  refine ⟨haz, ?_⟩
  by_cases hr : 0 ≤ width - along + ξ
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

 theorem reflected_low_admissible {width ξ short reflected z κ : ℝ}
    (hξ : ξ ≤ width / 15)
    (ht : reflected + short + z ≤ 23 * width / 30 + ξ)
    (hc : reflected + short + 6 * κ * z ≤ 14 * width / 15 + ξ) :
    reflected + short + z ≤ 5 * width / 6 ∧
      reflected + short + 6 * κ * z ≤ width := by
  constructor <;> linarith

end QRH.PlainReflection
