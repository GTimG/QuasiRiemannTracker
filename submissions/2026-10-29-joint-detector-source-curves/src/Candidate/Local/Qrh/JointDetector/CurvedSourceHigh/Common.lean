/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FractionCurveEval
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurvedStageHigh
import Candidate.Local.Qrh.JointDetector.CurvedSourceFractions.Common

namespace Qrh.JointDetector.CurvedSourceHigh
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open RepeatedMarks RepeatedMarks.FractionArithmetic

/-- The compact rational source prescription, interpreted exactly. -/
@[simp] theorem eval_source_phi : CurvedSourceFractions.phi.evalR=(999999999/1000000000:ℝ) := by
  norm_num [CurvedSourceFractions.phi,Fraction.evalR]

@[simp] theorem eval_clippedRay (p : FractionCurveData.Params) :
    (CurvedSourceFractions.clippedRay p).evalR=CurvedSourceStep.amplitudeFloor/
      CurvedSourceStep.matchedCut p.toReal (999999999/1000000000:ℝ) 0 := by
  simp only [CurvedSourceFractions.clippedRay,FractionCurveData.evalR_div,FractionCurveData.eval_amplitudeFloor,
    FractionCurveData.eval_matchedCut,eval_source_phi,FractionCurveData.evalR_zero]

/-- Geometry is independent of the integer sign certificates. -/
structure CellGeometry (cell : CurvedSourceStep.HighCell) : Prop where
  density_width : cell.lo < cell.hi
  density_pos : 0 < cell.lo
  density_upper : cell.hi ≤ 3/4
  alpha_lo_pos : 0 < cell.a0+cell.a1*cell.lo
  alpha_hi_pos : 0 < cell.a0+cell.a1*cell.hi
  alpha_lo_le : cell.a0+cell.a1*cell.lo ≤ cell.lo
  alpha_hi_le : cell.a0+cell.a1*cell.hi ≤ cell.hi
  width : cell.vl < cell.vh

/-- Reuse real geometry and transport only finite integer sign evidence. -/
theorem cell_of_fraction_signs
    (pf : FractionCurveData.Params) (cf : FractionCurveData.Cell)
    (p : CurvedSourceStep.Params) (cell : CurvedSourceStep.HighCell)
    (hp : pf.toReal=p) (hc : cf.toReal=cell) {combined : Bool}
    (hsigns : FractionCurveData.Signs pf cf combined) (g : CellGeometry cell) :
    CurvedSourceStep.HighCellCertificate p cell combined := by
  subst p
  subst cell
  exact hsigns.toHighCellCertificate g.density_width g.density_pos g.density_upper
    g.alpha_lo_pos g.alpha_hi_pos g.alpha_lo_le g.alpha_hi_le g.width

/-- One proof covers every affine ray cell, including the pure ray. -/
theorem ray_geometry (cell : CurvedSourceStep.HighCell)
    (hlo : 0 < cell.lo) (hhi : cell.lo < cell.hi) (hu : cell.hi ≤ 3/4)
    (hz : cell.a0 = 0) (hr : 0 < cell.a1) (hr1 : cell.a1 ≤ 1)
    (hw : cell.vl < cell.vh) : CellGeometry cell := by
  have hhip : 0 < cell.hi := hlo.trans hhi
  refine ⟨hhi,hlo,hu,?_,?_,?_,?_,hw⟩
  · rw [hz,zero_add]; exact mul_pos hr hlo
  · rw [hz,zero_add]; exact mul_pos hr hhip
  · rw [hz,zero_add]; nlinarith [mul_nonneg (sub_nonneg.mpr hr1) hlo.le]
  · rw [hz,zero_add]; nlinarith [mul_nonneg (sub_nonneg.mpr hr1) hhip.le]

/-- Constant amplitude cells use only their endpoint density bounds. -/
theorem constant_geometry (cell : CurvedSourceStep.HighCell)
    (hlo : 0 < cell.lo) (hhi : cell.lo < cell.hi) (hu : cell.hi ≤ 3/4)
    (hz : cell.a1 = 0) (ha : 0 < cell.a0)
    (hal : cell.a0 ≤ cell.lo) (hah : cell.a0 ≤ cell.hi)
    (hw : cell.vl < cell.vh) : CellGeometry cell := by
  exact ⟨hhi,hlo,hu,by simpa [hz] using ha,by simpa [hz] using ha,
    by simpa [hz] using hal,by simpa [hz] using hah,hw⟩

namespace CurvedGeometry
open CurvedSourceStep
variable {p : Params} {phi floor : ℝ} (g : GeometryCertificate p phi floor)
include g

theorem rayCell_geometry (ray : ℝ) (hr : 0 < ray) (hr1 : ray ≤ 1)
    (hupper : matchedCut p phi 0 < 3/4) : CellGeometry (rayCell p phi ray) := by
  have hb := matchedCut_bounds g.face.L_lt g.D_nonneg g.cut_intercept g.numerator_pos.le
    (show p.c-crossing p ∈ Set.Icc (0:ℝ) (p.c-crossing p) from ⟨g.width_pos.le,le_rfl⟩)
  exact ray_geometry _ (g.floor_pos.trans_le g.lower_cut) (hb.2.trans_lt hupper)
    le_rfl rfl hr hr1 g.width_pos

theorem earlyRayCell_geometry (ray : ℝ) (hr : 0 < ray) (hr1 : ray ≤ 1)
    (hsplit : amplitudeFloor/ray < 3/4) (hvc : 0 < clippingWidth p phi ray) :
    CellGeometry (earlyRayCell p phi ray) := by
  exact ray_geometry _ (div_pos (by norm_num [amplitudeFloor]) hr) hsplit
    le_rfl rfl hr hr1 hvc

theorem lateRayCell_geometry (ray : ℝ) (hr : 0 < ray) (hr1 : ray ≤ 1)
    (hsplit : amplitudeFloor/ray < 3/4)
    (hvc : clippingWidth p phi ray < p.c-crossing p) :
    CellGeometry (lateRayCell p phi ray) := by
  exact ray_geometry _ (div_pos (by norm_num [amplitudeFloor]) hr) hsplit
    le_rfl rfl hr hr1 hvc

/-- The clipped width lies in the source interval, uniformly in a stage. -/
theorem clippingWidth_mem (ray : ℝ) (hr : 0 < ray) (hD : 0 < p.D)
    (hlo : matchedCut p phi (p.c-crossing p) < amplitudeFloor/ray)
    (hhi : amplitudeFloor/ray ≤ matchedCut p phi 0) :
    clippingWidth p phi ray ∈ Set.Ico (0:ℝ) (p.c-crossing p) := by
  apply CurveCells.crossing_mem g.numerator_pos g.cut_intercept
    (mul_pos (sub_pos.mpr g.face.L_lt) hD) g.width_pos.le
    (div_pos (by norm_num [amplitudeFloor]) hr)
  · simpa [CurveCells.q,matchedCut] using hlo
  · simpa [CurveCells.q,matchedCut] using hhi

theorem constantCell_geometry (ray : ℝ) (hr : 0 < ray) (hr1 : ray ≤ 1)
    (hsplit : matchedCut p phi (p.c-crossing p) < amplitudeFloor/ray)
    (hupper : amplitudeFloor/ray ≤ 3/4) (hfloor : amplitudeFloor ≤ floor)
    (hvc : clippingWidth p phi ray < p.c-crossing p) :
    CellGeometry (constantCell p phi ray) := by
  apply constant_geometry _ (g.floor_pos.trans_le g.lower_cut) hsplit hupper rfl
    (by norm_num [constantCell,amplitudeFloor]) (hfloor.trans g.lower_cut) _ hvc
  exact le_div_self (by norm_num [constantCell,amplitudeFloor]) hr hr1
end CurvedGeometry

/-- The data cover and semantic stage cover are the same closed region. -/
theorem cellsCover_of_data {p : CurvedSourceStep.Params} {phi ray : ℝ} {combined : Bool}
    {n : ℕ} {cells : Fin n→CurvedSourceStep.HighCell}
    (h : CurvedSourceStep.DataCover p phi ray combined cells) :
    CurvedSourceStep.CellsCover p phi ray combined cells := h

@[simp] theorem oneBank_toReal (p : FractionCurveData.Params) (ray : Fraction) (i : Fin 1) :
    (CurvedSourceFractions.oneBank p ray i).toReal=CurvedSourceStep.oneCell p.toReal
      (999999999/1000000000:ℝ) ray.evalR i := by
  fin_cases i
  simpa [CurvedSourceFractions.oneBank,CurvedSourceStep.oneCell,Matrix.cons_val_zero,eval_source_phi]
    using FractionCurveData.toReal_rayCell p CurvedSourceFractions.phi ray

@[simp] theorem twoBank_toReal (p : FractionCurveData.Params) (ray : Fraction) (i : Fin 2) :
    (CurvedSourceFractions.twoBank p ray i).toReal=CurvedSourceStep.twoCells p.toReal
      (999999999/1000000000:ℝ) ray.evalR i := by
  fin_cases i
  · simpa [CurvedSourceFractions.twoBank,CurvedSourceStep.twoCells,Matrix.cons_val_zero,eval_source_phi]
      using FractionCurveData.toReal_constantCell p CurvedSourceFractions.phi ray
  · simpa [CurvedSourceFractions.twoBank,CurvedSourceStep.twoCells,Matrix.cons_val_one,
      Matrix.cons_val_zero,eval_source_phi] using FractionCurveData.toReal_lateRayCell p CurvedSourceFractions.phi ray

@[simp] theorem threeBank_toReal (p : FractionCurveData.Params) (ray : Fraction) (i : Fin 3) :
    (CurvedSourceFractions.threeBank p ray i).toReal=CurvedSourceStep.threeCells p.toReal
      (999999999/1000000000:ℝ) ray.evalR i := by
  fin_cases i
  · simpa [CurvedSourceFractions.threeBank,CurvedSourceStep.threeCells,Matrix.cons_val_zero,eval_source_phi]
      using FractionCurveData.toReal_constantCell p CurvedSourceFractions.phi ray
  · simpa [CurvedSourceFractions.threeBank,CurvedSourceStep.threeCells,Matrix.cons_val_one,
      Matrix.cons_val_zero,eval_source_phi] using FractionCurveData.toReal_lateRayCell p CurvedSourceFractions.phi ray
  · simpa [CurvedSourceFractions.threeBank,CurvedSourceStep.threeCells,Matrix.cons_val_two,
      Matrix.cons_val_one,Matrix.cons_val_zero,eval_source_phi] using FractionCurveData.toReal_earlyRayCell p CurvedSourceFractions.phi ray

end
end Qrh.JointDetector.CurvedSourceHigh

#print axioms Qrh.JointDetector.CurvedSourceHigh.cell_of_fraction_signs
