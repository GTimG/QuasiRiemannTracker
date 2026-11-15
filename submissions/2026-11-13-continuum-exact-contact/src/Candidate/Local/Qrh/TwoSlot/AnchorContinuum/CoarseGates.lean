/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.StageCut
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Price.Gates
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Price

/-! Uniform coarse stage and tiny-core gates. These inequalities hold on a
whole box, so their use in a finite continuum partition needs no stage table. -/

set_option autoImplicit false
namespace Qrh.TwoSlot.AnchorContinuum
noncomputable section
open Set Qrh.TwoSlot.AnchorExtension.ChainData

theorem step_u_bounds {R r : ℝ} (hR : 3/4 ≤ R) (hrR : r ≤ R)
    (hstep : R-r ≤ 1/10000) :
    0 ≤ fu R r ∧ fu R r ≤ 1/10000 := by
  have hR0 : 0 < R := by linarith
  have hu : fu R r = (R-r)/(6*R) := by
    unfold fu
    field_simp
    <;> ring
  rw [hu]
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · rw [div_le_iff₀ (by positivity : 0 < 6*R)]
    linarith

/-- The entire source-gain output is bounded before any HIGH case split. -/
theorem output_upper {R z k r : ℝ} (hR : 3/4 ≤ R) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hz : 0 ≤ z) (hk : 45457/125000 ≤ k) :
    fY R z k r ≤ z + fu R r := by
  have hR0 : 0 < R := by linarith
  have hk0 : 0 < k := by linarith
  have hH : r/R ≤ 1 := (div_le_one hR0).mpr hrR
  have hu0 : 0 ≤ fu R r := by unfold fu; linarith
  have hi : 1/k ≤ 3 := (div_le_iff₀ hk0).mpr (by linarith)
  have h1 := mul_le_mul_of_nonneg_right hH hz
  have h2 := mul_le_mul_of_nonneg_right (show 1/k-2 ≤ 1 by linarith) hu0
  unfold fY
  linarith

/-- All coarse physical stage gates on one explicit, uniform step size. -/
theorem coarse_stage_hyp {R z k r : ℝ}
    (hR : R ∈ Icc (3/4:ℝ) (7/9)) (hr : r ∈ Icc (3/4:ℝ) R)
    (hz : z ∈ Icc (0:ℝ) (11/10000))
    (hk : 45457/125000 ≤ k ∧ k < 1/2) (hstep : R-r ≤ 1/10000) :
    Qrh.MarkedAnchor.Price.StageHyp R z k r := by
  obtain ⟨hu0,hu1⟩ := step_u_bounds hR.1 hr.2 hstep
  have hy := output_upper hR.1 (by linarith [hr.1]) hr.2 hz.1 hk.1
  have hs : fS R z k r ≤ (1-r)/2+z+fu R r := by unfold fS; linarith
  refine ⟨⟨by linarith [hR.1],hR.2⟩,⟨by linarith [hr.1],hr.2⟩,
    hk,hz.1,?_,hu1,?_,?_,?_⟩
  · linarith [hR.1,hz.2]
  · linarith [hr.1,hz.2]
  · linarith [hr.2,hR.2,hz.2]
  · linarith [hr.2,hR.2,hz.2]

/-- The complete tiny-core comparison has a uniform strict margin. -/
theorem tiny_gate {R z k r : ℝ}
    (hR : R ∈ Icc (3/4:ℝ) (7/9)) (hr : r ∈ Icc (3/4:ℝ) R)
    (hz : z ∈ Icc (0:ℝ) (11/10000)) (hk : 45457/125000 ≤ k)
    (hstep : R-r ≤ 1/10000) :
    Qrh.TwoSlot.AnchorZeroLoss.High.tinyEx r (fs R z k r) (fH R r) ≤
      fu R r-3/100 := by
  obtain ⟨hu0,hu1⟩ := step_u_bounds hR.1 hr.2 hstep
  have hy := output_upper hR.1 (by linarith [hr.1]) hr.2 hz.1 hk
  have hH : fH R r = 1-6*fu R r := by unfold fH fu; ring
  unfold Qrh.TwoSlot.AnchorZeroLoss.High.tinyEx fs fS
  rw [hH]
  linarith [hr.2,hR.2,hz.2]

/-- Instantiation for every short step of the strict continuum source curve. -/
theorem curve_coarse_gates {lam T gamma R r : ℝ}
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hT : 3/4 ≤ T) (hT1 : T ≤ 7/9)
    (hR : R ∈ Icc (3/4:ℝ) T) (hr : r ∈ Icc (3/4:ℝ) R)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1/100) (hstep : R-r ≤ 1/10000) :
    Qrh.MarkedAnchor.Price.StageHyp R (Curve.W lam T R) (Curve.cut lam T gamma R) r ∧
    Qrh.TwoSlot.AnchorZeroLoss.High.tinyEx r
      (fs R (Curve.W lam T R) (Curve.cut lam T gamma R) r) (fH R r) ≤ fu R r-3/100 := by
  obtain ⟨hz0,hz1⟩ := Curve.W_bounds hlam hlam1 hT hT1 hR
  have hk := Curve.cut_bounds hlam hlam1 hT hT1 hR hg hg1
  have hR' : R ∈ Icc (3/4:ℝ) (7/9) := ⟨hR.1,hR.2.trans hT1⟩
  exact ⟨coarse_stage_hyp hR' hr ⟨hz0,hz1.le⟩ hk hstep,
    tiny_gate hR' hr ⟨hz0,hz1.le⟩ hk.1 hstep⟩

end
end Qrh.TwoSlot.AnchorContinuum
