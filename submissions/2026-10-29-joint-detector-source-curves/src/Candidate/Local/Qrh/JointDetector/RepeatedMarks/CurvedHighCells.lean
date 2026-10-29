/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurveBox
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurveHighTemplates
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurvedGeometry
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurvedAmplitude

namespace Qrh.JointDetector.RepeatedMarks.CurvedSourceStep
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set BernsteinBox HighTemplates CurveHighTemplates CurveBernstein

/-- A literal density/width cell and its affine amplitude divider. Its lower
density is k/(e0+ev*v); ev=0 includes the fixed-boundary cells. -/
structure HighCell where
  lo : ℝ
  hi : ℝ
  vl : ℝ
  vh : ℝ
  a0 : ℝ
  a1 : ℝ
  k : ℝ
  e0 : ℝ
  ev : ℝ

def highReserve : ℝ := 1/10000000000000

def cellPower (p : Params) (cell : HighCell) (i : Fin 4) : Fin 4 → Fin 3 → ℝ :=
  let args := (p.B0,p.L0)
  match i.val with
  | 0 => CurveHighTemplates.capPower p.B0 p.L0 (1/10) cell.a0 cell.a1
      p.B p.L (crossing p) p.A p.D highReserve
  | 1 => CurveHighTemplates.budgetPower p.B0 p.L0 (1/10) cell.a0 cell.a1
      p.B p.L (crossing p) p.A p.D highReserve
  | 2 => CurveHighTemplates.tailPower p.B0 p.L0 (1/10) cell.a0 cell.a1
      p.B p.L (crossing p) p.A p.D highReserve
  | _ => CurveHighTemplates.selectedPower p.B0 p.L0 (1/10) cell.a0 cell.a1
      p.B p.L (crossing p) p.A p.D highReserve

/-- Finite sign certificates for one complete cell. No analytic count is
stored in this structure: the actual count rates are supplied by proved
moment/detector theorems and the symbolic transport. -/
structure HighCellCertificate (p : Params) (cell : HighCell) (combined : Bool) : Prop where
  density_width : cell.lo < cell.hi
  density_pos : 0 < cell.lo
  density_upper : cell.hi ≤ 3/4
  alpha_lo_pos : 0 < cell.a0+cell.a1*cell.lo
  alpha_hi_pos : 0 < cell.a0+cell.a1*cell.hi
  alpha_lo_le : cell.a0+cell.a1*cell.lo ≤ cell.lo
  alpha_hi_le : cell.a0+cell.a1*cell.hi ≤ cell.hi
  amplitude_cap : ∀ i j, 0 ≤ coefficients
    (affineCapPower p.B0 p.L0 (1/10) cell.a0 cell.a1 (crossing p)) cell.lo cell.hi i j
  amplitude_budget : ∀ i j, 0 ≤ coefficients
    (affineBudgetPower p.B0 p.L0 (1/10) cell.a0 cell.a1 (crossing p)) cell.lo cell.hi i j
  high : ∀ i : Fin 4, i.val < 3 ∨ combined = true →
    BoxCertificate (mapped (cellPower p cell i) cell.k cell.e0 cell.ev cell.hi)
      0 1 cell.vl cell.vh

namespace HighCellCertificate
variable {p : Params} {cell : HighCell} {combined : Bool}
    (h : HighCellCertificate p cell combined)
include h

theorem alpha_bounds {ν : ℝ} (hν : ν ∈ Icc cell.lo cell.hi) :
    0 < cell.a0+cell.a1*ν ∧ cell.a0+cell.a1*ν ≤ ν := by
  obtain ⟨r,hr,hh⟩ := SourceStep.linear_interval_margin h.alpha_lo_pos h.alpha_hi_pos
  have hlo : cell.a0+(cell.a1-1)*cell.lo ≤ 0 := by linarith [h.alpha_lo_le]
  have hhi : cell.a0+(cell.a1-1)*cell.hi ≤ 0 := by linarith [h.alpha_hi_le]
  have hu := affine_endpoint_upper hlo hhi hν
  exact ⟨hr.trans_le (hh ν hν),by linarith⟩

theorem amplitude_nonneg {ν : ℝ} (hν : ν ∈ Icc cell.lo cell.hi) :
    (∀ z ∈ Icc (0:ℝ) 1, 0 ≤ affineCapAmp p.B0 p.L0 (1/10) cell.a0 cell.a1 (crossing p) ν z) ∧
    (∀ z ∈ Icc (0:ℝ) 1, 0 ≤ affineBudgetAmp p.B0 p.L0 (1/10) cell.a0 cell.a1 (crossing p) ν z) := by
  constructor
  · intro z hz
    exact affineCap_nonneg _ _ _ _ _ _ _ _ _ _ h.density_width hν hz h.amplitude_cap
  · intro z hz
    exact affineBudget_nonneg _ _ _ _ _ _ _ _ _ _ h.density_width hν hz h.amplitude_budget

theorem polynomials_nonneg {ν v : ℝ} (hv : v ∈ Icc cell.vl cell.vh)
    (hE : 0 < cell.e0+cell.ev*v) (hνlo : cell.k/(cell.e0+cell.ev*v) ≤ ν)
    (hνhi : ν ≤ cell.hi) :
    ∀ i : Fin 4, i.val < 3 ∨ combined = true → 0 ≤ powerEval (cellPower p cell i) ν v := by
  intro i hi
  exact curved_nonneg_of_certificate (cellPower p cell i) cell.k cell.e0 cell.ev cell.hi
    cell.vl cell.vh ν v hv hE hνlo hνhi (h.high i hi)

end HighCellCertificate
#print axioms HighCellCertificate.polynomials_nonneg
end
end Qrh.JointDetector.RepeatedMarks.CurvedSourceStep
