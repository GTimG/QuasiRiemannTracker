/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.CurvedSourceHigh.Common

namespace Qrh.JointDetector.CurvedSourceHigh
noncomputable section
set_option autoImplicit false
open RepeatedMarks RepeatedMarks.FractionArithmetic CurvedSourceStep

def sourcePhi : ℝ := 999999999/1000000000

structure RayLayout (p : Params) (ray : ℝ) (combined : Bool) : Prop where
  parent_slope : (3/2:ℝ) ≤ p.L0
  selected_cap : combined = true → p.c0 ≤ 1/10
  ray_pos : 0 < ray
  ray_le : ray ≤ 1
  cut_upper : matchedCut p sourcePhi 0 < 3/4
  pure_ray : combined = false → ray = 1
  combined_split : combined = true → amplitudeFloor/ray ≤ matchedCut p sourcePhi (p.c-crossing p)

structure ClipLayout (p : Params) (floor ray : ℝ) (early : Bool) : Prop where
  parent_slope : (3/2:ℝ) ≤ p.L0
  selected_cap : p.c0 ≤ 1/10
  ray_pos : 0 < ray
  ray_le : ray ≤ 1
  cut_upper : matchedCut p sourcePhi 0 < 3/4
  D_pos : 0 < p.D
  floor_lower : amplitudeFloor ≤ floor
  split_lower : matchedCut p sourcePhi (p.c-crossing p) < amplitudeFloor/ray
  split_upper : amplitudeFloor/ray ≤ matchedCut p sourcePhi 0
  width : if early then 0 < clippingWidth p sourcePhi ray else clippingWidth p sourcePhi ray = 0

macro "curved_layout" : tactic => `(tactic|
  constructor <;> norm_num [sourcePhi,matchedCut,cutNumerator,cutIntercept,crossing,
    QRH.SilDensitySplit.Hybrid.cross,amplitudeFloor,clippingWidth,CurveCells.crossingWidth])

theorem stage_ray {p : Params} {floor ray : ℝ} {combined : Bool}
    (g : GeometryCertificate p sourcePhi floor) (l : RayLayout p ray combined)
    (pf : FractionCurveData.Params) (rF : Fraction) (hp : pf.toReal=p) (hr : rF.evalR=ray)
    (hs : ∀ i, FractionCurveData.Signs pf (CurvedSourceFractions.oneBank pf rF i) combined) :
    StageHighCertificate p sourcePhi floor ray combined (oneCell p sourcePhi ray) := by
  refine ⟨g,l.parent_slope,l.selected_cap,?_,?_⟩
  · intro i
    have hc : (CurvedSourceFractions.oneBank pf rF i).toReal=(oneCell p sourcePhi ray) i := by
      rw [oneBank_toReal,hp,hr]; rfl
    apply cell_of_fraction_signs pf _ p _ hp hc (hs i)
    fin_cases i
    exact CurvedGeometry.rayCell_geometry g ray l.ray_pos l.ray_le l.cut_upper
  · cases hmode : combined
    · have heq := l.pure_ray hmode
      rw [heq]
      exact cellsCover_of_data g.pure_cover
    · exact cellsCover_of_data (g.ray_cover ray l.ray_pos (l.combined_split hmode))

theorem stage_two {p : Params} {floor ray : ℝ}
    (g : GeometryCertificate p sourcePhi floor) (l : ClipLayout p floor ray false)
    (pf : FractionCurveData.Params) (rF : Fraction) (hp : pf.toReal=p) (hr : rF.evalR=ray)
    (hs : ∀ i, FractionCurveData.Signs pf (CurvedSourceFractions.twoBank pf rF i) true) :
    StageHighCertificate p sourcePhi floor ray true (twoCells p sourcePhi ray) := by
  have hv := CurvedGeometry.clippingWidth_mem g ray l.ray_pos l.D_pos l.split_lower l.split_upper
  have hsplit := l.split_upper.trans_lt l.cut_upper
  refine ⟨g,l.parent_slope,fun _ => l.selected_cap,?_,?_⟩
  · intro i
    have hc : (CurvedSourceFractions.twoBank pf rF i).toReal=(twoCells p sourcePhi ray) i := by
      rw [twoBank_toReal,hp,hr]; rfl
    apply cell_of_fraction_signs pf _ p _ hp hc (hs i)
    fin_cases i
    · exact CurvedGeometry.constantCell_geometry g ray l.ray_pos l.ray_le l.split_lower
        hsplit.le l.floor_lower hv.2
    · exact CurvedGeometry.lateRayCell_geometry g ray l.ray_pos l.ray_le hsplit hv.2
  · exact cellsCover_of_data (g.two_cover ray l.ray_pos l.D_pos l.split_lower l.split_upper l.width)

theorem stage_three {p : Params} {floor ray : ℝ}
    (g : GeometryCertificate p sourcePhi floor) (l : ClipLayout p floor ray true)
    (pf : FractionCurveData.Params) (rF : Fraction) (hp : pf.toReal=p) (hr : rF.evalR=ray)
    (hs : ∀ i, FractionCurveData.Signs pf (CurvedSourceFractions.threeBank pf rF i) true) :
    StageHighCertificate p sourcePhi floor ray true (threeCells p sourcePhi ray) := by
  have hv := CurvedGeometry.clippingWidth_mem g ray l.ray_pos l.D_pos l.split_lower l.split_upper
  have hsplit := l.split_upper.trans_lt l.cut_upper
  refine ⟨g,l.parent_slope,fun _ => l.selected_cap,?_,?_⟩
  · intro i
    have hc : (CurvedSourceFractions.threeBank pf rF i).toReal=(threeCells p sourcePhi ray) i := by
      rw [threeBank_toReal,hp,hr]; rfl
    apply cell_of_fraction_signs pf _ p _ hp hc (hs i)
    fin_cases i
    · exact CurvedGeometry.constantCell_geometry g ray l.ray_pos l.ray_le l.split_lower
        hsplit.le l.floor_lower hv.2
    · exact CurvedGeometry.lateRayCell_geometry g ray l.ray_pos l.ray_le hsplit hv.2
    · exact CurvedGeometry.earlyRayCell_geometry g ray l.ray_pos l.ray_le hsplit l.width
  · exact cellsCover_of_data (g.three_cover ray l.ray_pos l.D_pos l.split_lower l.split_upper)

end
end Qrh.JointDetector.CurvedSourceHigh
#print axioms Qrh.JointDetector.CurvedSourceHigh.stage_three
