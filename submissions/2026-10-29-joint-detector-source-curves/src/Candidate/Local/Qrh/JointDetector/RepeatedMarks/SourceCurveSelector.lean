/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Tactic

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveSelector
noncomputable section
set_option autoImplicit false

def amplitude (L C n Δ : ℝ) : ℝ := 2*n*Δ/(L-n*C)
def lowFactor (L C n : ℝ) : ℝ := (L+n*C)/(2*L)

theorem amplitude_pos {L C n Δ : ℝ} (hn : 0 < n) (hΔ : 0 < Δ)
    (hgap : 0 < L-n*C) : 0 < amplitude L C n Δ := by
  unfold amplitude
  positivity

theorem lowFactor_mem {L C n : ℝ} (hL : 0 < L) (hC : 0 ≤ C)
    (hn : 0 < n) (hgap : 0 < L-n*C) : lowFactor L C n ∈ Set.Ioo (0:ℝ) 1 := by
  unfold lowFactor
  constructor
  · apply div_pos _ (by positivity)
    linarith [mul_nonneg hn.le hC]
  · apply (div_lt_one (by positivity : 0 < 2*L)).2
    linarith

/-- Exact positive LOW reserve for a finite step; it is per excess width. -/
theorem low_reserve {L C n Δ : ℝ} (hL : L ≠ 0) (hgap : L-n*C ≠ 0) :
    (1-lowFactor L C n)*L*amplitude L C n Δ = n*Δ := by
  unfold lowFactor amplitude
  field_simp
  <;> ring

/-- The matched cut is exactly the prescribed constant density cut. -/
theorem matched_cut {L C n Δ : ℝ} (hL : 0 < L) (hC : 0 ≤ C)
    (hn : 0 < n) (hΔ : 0 < Δ) (hgap : 0 < L-n*C) :
    (lowFactor L C n*L*amplitude L C n Δ)/(Δ+C*amplitude L C n Δ) = n := by
  have hA := amplitude_pos hn hΔ hgap
  have he : 0 < Δ+C*amplitude L C n Δ := by positivity
  apply (div_eq_iff he.ne').2
  unfold lowFactor amplitude
  field_simp
  <;> ring

/-- In source coordinates the selector denominator has a fixed positive gap. -/
theorem coordinate_gap {B L q ε : ℝ} (hC : 6*B-L ≠ 0)
    (hq : q=L/(6*B-L)) : L-(q-ε)*(6*B-L)=ε*(6*B-L) := by
  rw [hq]
  field_simp
  <;> ring

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveSelector
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurveSelector.matched_cut
