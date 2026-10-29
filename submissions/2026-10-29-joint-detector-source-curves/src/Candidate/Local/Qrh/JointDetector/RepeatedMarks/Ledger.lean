/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.Price
import Submissions.sil_density_split_20261026.CubeFree.StepData

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open QRH.SilDensitySplit.CubeFree

/-- Common source geometry, with the price ledger deliberately separate.
A new weighted supplier does not inherit an obsolete HIGH inequality. -/
structure GeometricGates (D : StepData) : Prop where
  face : D.B ≤ D.B₀ ∧ D.B₀ < 1 ∧ D.L < D.L₀ ∧ 1 < D.L ∧ 0 < D.c ∧ D.c < 1/6 ∧ D.c₀ < 1/6
  kappa : D.κ = 3/4
  crossing : 0 ≤ D.s₀ ∧ (D.L₀-D.L)*D.s₀ ≤ D.B₀-D.B ∧ (0 < D.s₀ → D.s₀ ≤ D.c₀)
  envelope : 0 < D.Hmin ∧ D.Hmin < 1 ∧ 3 ≤ D.Hmax
  sel_spec : ∀ ε > 0, MonotoneOn (D.sel ε) (Set.Icc 0 D.c) ∧
    ∀ w, 0 ≤ w → w ≤ D.c → 0 ≤ D.sel ε w ∧ D.sel ε w ≤ w
  reference : ∃ ρ, ReferenceAt D ρ

theorem GeometricGates.with_ledger {D : StepData} (h : GeometricGates D)
    (hl : ∀ ε > 0, ∃ p : ℝ × ℝ × ℝ, LedgerAt D ε p.1 p.2.1 p.2.2) : StepGates D :=
  ⟨h.face,h.kappa,h.crossing,h.envelope,h.sel_spec,hl,h.reference⟩

/-- The reserve is uniform in BOTH density and amplitude. Its index is the
actual full weighted family, not a separately maximized count. -/
def HighReserve (F : WeightedFamily) (B L W u0 reserve : ℝ) : Prop :=
  ∀ i, reserve ≤ u0-F.term i (B-L*W) (W-u0) (1-6*u0)

theorem weighted_high_paid {F : WeightedFamily} {B L W u0 u P s t H mesh tl reserve : ℝ}
    (hP : P ≤ B-L*W+tl) (hs : s ≤ W-u)
    (hH : H=1+t-6*u) (ht : -tl ≤ t) (htl : 0 ≤ tl)
    (hu : u0 ≤ u) (hu1 : u ≤ u0+mesh)
    (hreserve : HighReserve F B L W u0 reserve)
    (hbudget : 5*mesh+2*tl ≤ reserve) : F.high P s H ≤ u := by
  apply F.high_le
  intro i
  have hn := F.density_mem i
  have hv := F.amplitude_mem i
  have hr := F.rate_mem i
  have hp := mul_le_mul_of_nonneg_left hP hn.1
  have hslot := mul_le_mul_of_nonneg_left hs hv.1
  have hfreq := mul_le_mul_of_nonpos_left ht (by linarith [hr.2] : F.rate i-1 ≤ 0)
  have hover : (6*(1-F.rate i)-F.amplitude i-1)*(u-u0) ≤ 5*mesh := by
    have hcoef : 6*(1-F.rate i)-F.amplitude i-1 ≤ 5 := by linarith [hr.1,hv.1]
    have h := mul_le_mul_of_nonneg_right hcoef (by linarith : 0 ≤ u-u0)
    linarith
  have herr : (F.density i+1-F.rate i)*tl ≤ 2*tl := by
    have hcoef : F.density i+1-F.rate i ≤ 2 := by linarith [hn.2,hr.1]
    exact mul_le_mul_of_nonneg_right hcoef htl
  have hnom := hreserve i
  unfold WeightedFamily.term at *
  rw [hH]
  nlinarith

end
end Qrh.JointDetector.RepeatedMarks
