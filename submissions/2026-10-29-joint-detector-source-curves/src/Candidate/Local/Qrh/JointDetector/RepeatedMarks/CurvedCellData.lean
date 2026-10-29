/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurvedHighCells
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurveCells

namespace Qrh.JointDetector.RepeatedMarks.CurvedSourceStep
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set

def amplitudeFloor : ℝ := 250001/500000

def rayCell (p : Params) (phi ray : ℝ) : HighCell :=
  ⟨matchedCut p phi (p.c-crossing p),3/4,0,p.c-crossing p,0,ray,
    cutNumerator p phi,cutIntercept p,(p.L0-p.L)*p.D⟩
def clippingWidth (p : Params) (phi ray : ℝ) : ℝ :=
  CurveCells.crossingWidth (cutNumerator p phi) (cutIntercept p) ((p.L0-p.L)*p.D) (amplitudeFloor/ray)
def constantCell (p : Params) (phi ray : ℝ) : HighCell :=
  ⟨matchedCut p phi (p.c-crossing p),amplitudeFloor/ray,clippingWidth p phi ray,
    p.c-crossing p,amplitudeFloor,0,cutNumerator p phi,cutIntercept p,(p.L0-p.L)*p.D⟩
def lateRayCell (p : Params) (phi ray : ℝ) : HighCell :=
  ⟨amplitudeFloor/ray,3/4,clippingWidth p phi ray,p.c-crossing p,0,ray,
    amplitudeFloor/ray,1,0⟩
def earlyRayCell (p : Params) (phi ray : ℝ) : HighCell :=
  ⟨amplitudeFloor/ray,3/4,0,clippingWidth p phi ray,0,ray,
    cutNumerator p phi,cutIntercept p,(p.L0-p.L)*p.D⟩
def oneCell (p : Params) (phi ray : ℝ) : Fin 1 → HighCell := ![rayCell p phi ray]
def twoCells (p : Params) (phi ray : ℝ) : Fin 2 → HighCell :=
  ![constantCell p phi ray,lateRayCell p phi ray]
def threeCells (p : Params) (phi ray : ℝ) : Fin 3 → HighCell :=
  ![constantCell p phi ray,lateRayCell p phi ray,earlyRayCell p phi ray]

def DataCover (p : Params) (phi ray : ℝ) (combined : Bool)
    {n : ℕ} (cells : Fin n → HighCell) : Prop :=
  ∀ ν v : ℝ, v ∈ Icc (0:ℝ) (p.c-crossing p) →
    matchedCut p phi v ≤ ν → ν ≤ 3/4 → ∃ i : Fin n,
      ν ∈ Icc (cells i).lo (cells i).hi ∧
      v ∈ Icc (cells i).vl (cells i).vh ∧
      0 < (cells i).e0+(cells i).ev*v ∧
      (cells i).k/((cells i).e0+(cells i).ev*v) ≤ ν ∧
      (cells i).a0+(cells i).a1*ν =
        if combined then max amplitudeFloor (ray*ν) else ν

namespace GeometryCertificate
variable {p : Params} {phi floor : ℝ} (g : GeometryCertificate p phi floor)
include g

theorem numerator_pos : 0 < cutNumerator p phi :=
  mul_pos (mul_pos g.phi_pos g.L0_pos) g.A_pos

theorem density_slope_nonneg : 0 ≤ (p.L0-p.L)*p.D :=
  mul_nonneg (sub_pos.mpr g.face.L_lt).le g.D_nonneg

theorem pure_cover : DataCover p phi 1 false (oneCell p phi 1) := by
  intro ν v hv hν hνhi
  have hbounds := matchedCut_bounds g.face.L_lt g.D_nonneg g.cut_intercept g.numerator_pos.le hv
  have hE := matchedCut_den_pos g.face.L_lt g.D_nonneg g.cut_intercept hv.1
  refine ⟨0,?_,hv,hE,hν,?_⟩
  · exact ⟨hbounds.1.trans hν,hνhi⟩
  · simp [oneCell,rayCell,Matrix.cons_val_zero,ite_false,zero_add,one_mul]

theorem ray_cover (ray : ℝ) (hr : 0 < ray)
    (hsplit : amplitudeFloor/ray ≤ matchedCut p phi (p.c-crossing p)) :
    DataCover p phi ray true (oneCell p phi ray) := by
  intro ν v hv hν hνhi
  have hb := matchedCut_bounds g.face.L_lt g.D_nonneg g.cut_intercept g.numerator_pos.le hv
  have hE := matchedCut_den_pos g.face.L_lt g.D_nonneg g.cut_intercept hv.1
  have ha : amplitudeFloor ≤ ray*ν := by
    have hh := (div_le_iff₀ hr).1 (hsplit.trans (hb.1.trans hν))
    nlinarith only [hh]
  refine ⟨0,⟨hb.1.trans hν,hνhi⟩,hv,hE,hν,?_⟩
  simp [oneCell,rayCell,Matrix.cons_val_zero,ite_true,zero_add,max_eq_right ha]

theorem three_cover (ray : ℝ) (hr : 0 < ray) (hD : 0 < p.D)
    (hsplitlo : matchedCut p phi (p.c-crossing p) < amplitudeFloor/ray)
    (hsplithi : amplitudeFloor/ray ≤ matchedCut p phi 0) :
    DataCover p phi ray true (threeCells p phi ray) := by
  intro ν v hv hν hνhi
  have hev : 0 < (p.L0-p.L)*p.D := mul_pos (sub_pos.mpr g.face.L_lt) hD
  have hc := CurveCells.cell_cover g.numerator_pos g.cut_intercept hev
    (by norm_num [amplitudeFloor]) hr g.width_pos.le hv hν hνhi hsplitlo hsplithi
  have hb := matchedCut_bounds g.face.L_lt g.D_nonneg g.cut_intercept g.numerator_pos.le hv
  have hE := matchedCut_den_pos g.face.L_lt g.D_nonneg g.cut_intercept hv.1
  rcases hc with hc | hc | hc
  · refine ⟨0,?_,hc.1,hE,hν,?_⟩
    · exact ⟨hb.1.trans hν,hc.2.1.2⟩
    · simpa [threeCells,constantCell,Matrix.cons_val_zero,ite_true,zero_mul,add_zero]
        using hc.2.2.symm
  · refine ⟨1,hc.2.1,hc.1,by norm_num [threeCells,lateRayCell],?_,?_⟩
    · simpa [threeCells,lateRayCell,Matrix.cons_val_one,Matrix.cons_val_zero,
        zero_mul,add_zero,div_one] using hc.2.1.1
    · simpa [threeCells,lateRayCell,Matrix.cons_val_one,Matrix.cons_val_zero,ite_true,zero_add]
        using hc.2.2.symm
  · refine ⟨2,⟨hc.2.2.2.1,hνhi⟩,hc.2.1,hE,hν,?_⟩
    simpa [threeCells,earlyRayCell,Matrix.cons_val_two,Matrix.cons_val_one,
      Matrix.cons_val_zero,ite_true,zero_add] using hc.2.2.2.2.symm

theorem two_cover (ray : ℝ) (hr : 0 < ray) (hD : 0 < p.D)
    (hsplitlo : matchedCut p phi (p.c-crossing p) < amplitudeFloor/ray)
    (hsplithi : amplitudeFloor/ray ≤ matchedCut p phi 0)
    (hvc : clippingWidth p phi ray = 0) :
    DataCover p phi ray true (twoCells p phi ray) := by
  intro ν v hv hν hνhi
  obtain ⟨i,hi⟩ := g.three_cover ray hr hD hsplitlo hsplithi ν v hv hν hνhi
  fin_cases i
  · exact ⟨0,hi⟩
  · exact ⟨1,hi⟩
  · have hv0 : v = 0 := by
      have hh := hi.2.1.2
      change v ≤ clippingWidth p phi ray at hh
      rw [hvc] at hh
      exact le_antisymm hh hv.1
    have hc : amplitudeFloor/ray ≤ ν := by
      simpa [threeCells,earlyRayCell] using hi.1.1
    have heq := hi.2.2.2.2
    refine ⟨1,?_,?_,by norm_num [twoCells,lateRayCell],?_,?_⟩
    · exact ⟨hc,hνhi⟩
    · change v ∈ Icc (clippingWidth p phi ray) (p.c-crossing p)
      rw [hvc]
      exact hv
    · simpa [twoCells,lateRayCell,Matrix.cons_val_one,Matrix.cons_val_zero,
        zero_mul,add_zero,div_one] using hc
    · simpa [twoCells,lateRayCell,earlyRayCell,threeCells,
        Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero,ite_true,zero_add] using heq

end GeometryCertificate
#print axioms GeometryCertificate.three_cover
end
end Qrh.JointDetector.RepeatedMarks.CurvedSourceStep
