/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Price

/-! Coupled HIGH tolerances. The specialization below is exactly the compiled
finite price. These algebraic comparisons do not assert a physical supplier
at a new tolerance; its analytic adapters must still be generalized. -/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorContinuum.Tolerances
noncomputable section

def sourcePad (q : ℝ) : ℝ := q / 10
def reserve (q : ℝ) : ℝ := 30 * q

def sig (q a0 a1 w : ℝ) : ℝ :=
  max 0 ((1-w)/2 + (a0-a1*w) - sourcePad q)

def shortCnt (q a0 a1 ν e w s M : ℝ) : ℝ :=
  M - ν*M*w - e*min s (M*sig q a0 a1 w)

def longCnt (q ν w M : ℝ) : ℝ :=
  M/6 + (5/6-ν)*M*(3*w/2+q)

def detEx (q a0 a1 ν e w P s M : ℝ) : ℝ :=
  ν*P + e*s + max (shortCnt q a0 a1 ν e w s M) (longCnt q ν w M) - M

theorem fixed_price (a0 a1 ν e w P s M : ℝ) :
    detEx (1/1000000000000) a0 a1 ν e w P s M =
      Qrh.TwoSlot.AnchorZeroLoss.High.detEx a0 a1 ν e w P s M := by
  unfold detEx shortCnt longCnt sig sourcePad
    Qrh.TwoSlot.AnchorZeroLoss.High.detEx
    Qrh.TwoSlot.AnchorZeroLoss.High.shortCnt
    Qrh.TwoSlot.AnchorZeroLoss.High.longCnt
    Qrh.TwoSlot.AnchorZeroLoss.High.sig
  norm_num [Qrh.TwoSlot.AnchorZeroLoss.High.WitnessShift.value,
    Qrh.TwoSlot.AnchorZeroLoss.High.fixedWitnessShift]

/-- Reducing the coupled tolerance improves both detector branches at every
fixed cutoff, without changing a coefficient or a selected width. -/
theorem detEx_mono {q q' a0 a1 ν e w P s M : ℝ}
    (hq : q ≤ q') (he : 0 ≤ e) (hM : 0 ≤ M) (hν : ν ≤ 5/6) :
    detEx q a0 a1 ν e w P s M ≤ detEx q' a0 a1 ν e w P s M := by
  have hs : sig q' a0 a1 w ≤ sig q a0 a1 w := by
    unfold sig sourcePad
    exact max_le_max le_rfl (by linarith)
  have hm := min_le_min_left s (mul_le_mul_of_nonneg_left hs hM)
  have hshort : shortCnt q a0 a1 ν e w s M ≤
      shortCnt q' a0 a1 ν e w s M := by
    unfold shortCnt
    linarith [mul_le_mul_of_nonneg_left hm he]
  have hlong : longCnt q ν w M ≤ longCnt q' ν w M := by
    unfold longCnt
    have hc : 0 ≤ (5/6-ν)*M := mul_nonneg (sub_nonneg.mpr hν) hM
    exact add_le_add_right (mul_le_mul_of_nonneg_left (by linarith :
      3*w/2+q ≤ 3*w/2+q') hc) _
  unfold detEx
  linarith [max_le_max hshort hlong]

/-- One positive parameter simultaneously supplies all required ratios and
can spend arbitrarily little of any prescribed stage reserve. -/
theorem exists_coupled {budget : ℝ} (hb : 0 < budget) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1/1000000000000 ∧
      0 < sourcePad q ∧ sourcePad q ≤ q/10 ∧
      0 < reserve q - (3*q/2+q) ∧ reserve q < budget := by
  let q := min (1/1000000000000 : ℝ) (budget/60)
  have hq : 0 < q := lt_min (by norm_num) (by positivity)
  have hqB : q ≤ budget/60 := min_le_right _ _
  refine ⟨q, hq, min_le_left _ _, ?_, le_rfl, ?_, ?_⟩
  · exact div_pos hq (by norm_num)
  · unfold reserve
    linarith
  · unfold reserve
    linarith

end
end Qrh.TwoSlot.AnchorContinuum.Tolerances
