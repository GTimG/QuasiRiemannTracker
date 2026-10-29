/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FractionCurveData
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FractionHighTemplates
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurvedCellData
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FastBernsteinShapes

namespace Qrh.JointDetector.RepeatedMarks.FractionCurveData
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 60000
open FractionArithmetic

@[simp] theorem evalR_nat (n : ℕ) : (OfNat.ofNat n : Fraction).evalR=(n:ℝ) :=
  Fraction.eval_nat n
@[simp] theorem evalR_zero : (0:Fraction).evalR=(0:ℝ) := Fraction.eval_zero
@[simp] theorem evalR_one : (1:Fraction).evalR=(1:ℝ) := Fraction.eval_one
@[simp] theorem evalR_ofNat (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : Fraction).evalR=(OfNat.ofNat n : ℝ) := Fraction.eval_ofNat n
@[simp] theorem evalR_add (a b : Fraction) : (a+b).evalR=a.evalR+b.evalR := Fraction.eval_add a b
@[simp] theorem evalR_sub (a b : Fraction) : (a-b).evalR=a.evalR-b.evalR := Fraction.eval_sub a b
@[simp] theorem evalR_mul (a b : Fraction) : (a*b).evalR=a.evalR*b.evalR := Fraction.eval_mul a b
@[simp] theorem evalR_neg (a : Fraction) : (-a).evalR= -a.evalR := Fraction.eval_neg a
@[simp] theorem evalR_div (a b : Fraction) : (a/b).evalR=a.evalR/b.evalR := Fraction.eval_div a b
@[simp] theorem evalR_pow (a : Fraction) (n : ℕ) : (a^n).evalR=a.evalR^n := Fraction.eval_pow a n

@[ext] theorem highCell_ext {a b : CurvedSourceStep.HighCell}
    (hlo : a.lo=b.lo) (hhi : a.hi=b.hi) (hvl : a.vl=b.vl) (hvh : a.vh=b.vh)
    (ha0 : a.a0=b.a0) (ha1 : a.a1=b.a1) (hk : a.k=b.k) (he0 : a.e0=b.e0)
    (hev : a.ev=b.ev) : a=b := by
  cases a
  cases b
  simp_all

/-- Interpret only the eight scalar source parameters. -/
def Params.toReal (p : Params) : CurvedSourceStep.Params :=
  ⟨p.B0.evalR,p.L0.evalR,p.c0.evalR,p.B.evalR,p.L.evalR,p.c.evalR,p.A.evalR,p.D.evalR⟩

/-- Interpret a literal curved density/amplitude cell. -/
def Cell.toReal (cell : Cell) : CurvedSourceStep.HighCell :=
  ⟨cell.lo.evalR,cell.hi.evalR,cell.vl.evalR,cell.vh.evalR,cell.a0.evalR,cell.a1.evalR,
    cell.k.evalR,cell.e0.evalR,cell.ev.evalR⟩

@[simp] theorem eval_crossing (p : Params) : (crossing p).evalR=CurvedSourceStep.crossing p.toReal := by
  simp [crossing,CurvedSourceStep.crossing,QRH.SilDensitySplit.Hybrid.cross,Params.toReal]
@[simp] theorem eval_cutNumerator (p : Params) (phi : Fraction) :
    (cutNumerator p phi).evalR=CurvedSourceStep.cutNumerator p.toReal phi.evalR := by
  simp [cutNumerator,CurvedSourceStep.cutNumerator,Params.toReal]
@[simp] theorem eval_cutIntercept (p : Params) :
    (cutIntercept p).evalR=CurvedSourceStep.cutIntercept p.toReal := by
  norm_num [cutIntercept,CurvedSourceStep.cutIntercept,Params.toReal,Fraction.evalR]
@[simp] theorem eval_matchedCut (p : Params) (phi v : Fraction) :
    (matchedCut p phi v).evalR=CurvedSourceStep.matchedCut p.toReal phi.evalR v.evalR := by
  norm_num [matchedCut,CurvedSourceStep.matchedCut,cutNumerator,cutIntercept,
    CurvedSourceStep.cutNumerator,CurvedSourceStep.cutIntercept,Params.toReal,Fraction.evalR]
@[simp] theorem eval_amplitudeFloor : amplitudeFloor.evalR=CurvedSourceStep.amplitudeFloor := by
  norm_num [amplitudeFloor,CurvedSourceStep.amplitudeFloor,Fraction.evalR]
@[simp] theorem eval_clippingWidth (p : Params) (phi ray : Fraction) :
    (clippingWidth p phi ray).evalR=CurvedSourceStep.clippingWidth p.toReal phi.evalR ray.evalR := by
  norm_num [clippingWidth,CurvedSourceStep.clippingWidth,CurveCells.crossingWidth,
    amplitudeFloor,CurvedSourceStep.amplitudeFloor,Params.toReal,crossing,CurvedSourceStep.crossing,QRH.SilDensitySplit.Hybrid.cross,cutNumerator,cutIntercept,CurvedSourceStep.cutNumerator,CurvedSourceStep.cutIntercept,matchedCut,CurvedSourceStep.matchedCut,clippingWidth,CurvedSourceStep.clippingWidth,CurveCells.crossingWidth,amplitudeFloor,CurvedSourceStep.amplitudeFloor,Fraction.evalR]

@[simp] theorem toReal_rayCell (p : Params) (phi ray : Fraction) :
    (rayCell p phi ray).toReal=CurvedSourceStep.rayCell p.toReal phi.evalR ray.evalR := by
  ext <;> norm_num [rayCell,Cell.toReal,CurvedSourceStep.rayCell,Params.toReal,crossing,CurvedSourceStep.crossing,QRH.SilDensitySplit.Hybrid.cross,cutNumerator,cutIntercept,CurvedSourceStep.cutNumerator,CurvedSourceStep.cutIntercept,matchedCut,CurvedSourceStep.matchedCut,clippingWidth,CurvedSourceStep.clippingWidth,CurveCells.crossingWidth,amplitudeFloor,CurvedSourceStep.amplitudeFloor,Fraction.evalR]
@[simp] theorem toReal_constantCell (p : Params) (phi ray : Fraction) :
    (constantCell p phi ray).toReal=CurvedSourceStep.constantCell p.toReal phi.evalR ray.evalR := by
  ext <;> norm_num [constantCell,Cell.toReal,CurvedSourceStep.constantCell,Params.toReal,crossing,CurvedSourceStep.crossing,QRH.SilDensitySplit.Hybrid.cross,cutNumerator,cutIntercept,CurvedSourceStep.cutNumerator,CurvedSourceStep.cutIntercept,matchedCut,CurvedSourceStep.matchedCut,clippingWidth,CurvedSourceStep.clippingWidth,CurveCells.crossingWidth,amplitudeFloor,CurvedSourceStep.amplitudeFloor,Fraction.evalR]
@[simp] theorem toReal_lateRayCell (p : Params) (phi ray : Fraction) :
    (lateRayCell p phi ray).toReal=CurvedSourceStep.lateRayCell p.toReal phi.evalR ray.evalR := by
  ext <;> norm_num [lateRayCell,Cell.toReal,CurvedSourceStep.lateRayCell,Params.toReal,crossing,CurvedSourceStep.crossing,QRH.SilDensitySplit.Hybrid.cross,cutNumerator,cutIntercept,CurvedSourceStep.cutNumerator,CurvedSourceStep.cutIntercept,matchedCut,CurvedSourceStep.matchedCut,clippingWidth,CurvedSourceStep.clippingWidth,CurveCells.crossingWidth,amplitudeFloor,CurvedSourceStep.amplitudeFloor,Fraction.evalR]
@[simp] theorem toReal_earlyRayCell (p : Params) (phi ray : Fraction) :
    (earlyRayCell p phi ray).toReal=CurvedSourceStep.earlyRayCell p.toReal phi.evalR ray.evalR := by
  ext <;> norm_num [earlyRayCell,Cell.toReal,CurvedSourceStep.earlyRayCell,Params.toReal,crossing,CurvedSourceStep.crossing,QRH.SilDensitySplit.Hybrid.cross,cutNumerator,cutIntercept,CurvedSourceStep.cutNumerator,CurvedSourceStep.cutIntercept,matchedCut,CurvedSourceStep.matchedCut,clippingWidth,CurvedSourceStep.clippingWidth,CurveCells.crossingWidth,amplitudeFloor,CurvedSourceStep.amplitudeFloor,Fraction.evalR]

theorem eval_affineCapPower (B L c a0 a1 s : Fraction) (i : Fin 6) (j : Fin 5) :
    (affineCapPower B L c a0 a1 s i j).evalR=
      HighTemplates.affineCapPower B.evalR L.evalR c.evalR a0.evalR a1.evalR s.evalR i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [affineCapPower,HighTemplates.affineCapPower,Fraction.evalR]

theorem eval_affineBudgetPower (B L c a0 a1 s : Fraction) (i : Fin 6) (j : Fin 5) :
    (affineBudgetPower B L c a0 a1 s i j).evalR=
      HighTemplates.affineBudgetPower B.evalR L.evalR c.evalR a0.evalR a1.evalR s.evalR i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [affineBudgetPower,HighTemplates.affineBudgetPower,Fraction.evalR]

theorem eval_affineCapHighPower (B L c a0 a1 H P S u rho : Fraction) (i : Fin 4) (j : Fin 1) :
    (affineCapHighPower B L c a0 a1 H P S u rho i j).evalR=
      HighTemplates.affineCapHighPower B.evalR L.evalR c.evalR a0.evalR a1.evalR
        H.evalR P.evalR S.evalR u.evalR rho.evalR i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [affineCapHighPower,HighTemplates.affineCapHighPower,Fraction.evalR]

theorem eval_affineBudgetHighPower (B L c a0 a1 H P S u rho : Fraction) (i : Fin 4) (j : Fin 1) :
    (affineBudgetHighPower B L c a0 a1 H P S u rho i j).evalR=
      HighTemplates.affineBudgetHighPower B.evalR L.evalR c.evalR a0.evalR a1.evalR
        H.evalR P.evalR S.evalR u.evalR rho.evalR i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [affineBudgetHighPower,HighTemplates.affineBudgetHighPower,Fraction.evalR]


theorem eval_hCoeff (A D : Fraction) (j : Fin 3) :
    (hCoeff A D j).evalR=CurveHighTemplates.hCoeff A.evalR D.evalR j := by
  fin_cases j <;> norm_num [hCoeff,CurveHighTemplates.hCoeff,Fraction.evalR]
theorem eval_pCoeff (B L s D : Fraction) (j : Fin 3) :
    (pCoeff B L s D j).evalR=CurveHighTemplates.pCoeff B.evalR L.evalR s.evalR D.evalR j := by
  fin_cases j <;> norm_num [pCoeff,CurveHighTemplates.pCoeff,Fraction.evalR]
theorem eval_sCoeff (s A D : Fraction) (j : Fin 3) :
    (sCoeff s A D j).evalR=CurveHighTemplates.sCoeff s.evalR A.evalR D.evalR j := by
  fin_cases j <;> norm_num [sCoeff,CurveHighTemplates.sCoeff,Fraction.evalR]
theorem eval_uCoeff (A : Fraction) (j : Fin 3) :
    (uCoeff A j).evalR=CurveHighTemplates.uCoeff A.evalR j := by
  fin_cases j <;> norm_num [uCoeff,CurveHighTemplates.uCoeff,Fraction.evalR]
theorem eval_rCoeff (rho D : Fraction) (j : Fin 3) :
    (rCoeff rho D j).evalR=CurveHighTemplates.rCoeff rho.evalR D.evalR j := by
  fin_cases j <;> norm_num [rCoeff,CurveHighTemplates.rCoeff,Fraction.evalR]

theorem eval_capPower (B0 L0 c a0 a1 B L s A D rho : Fraction) (i : Fin 4) (j : Fin 3) :
    (capPower B0 L0 c a0 a1 B L s A D rho i j).evalR=
      CurveHighTemplates.capPower B0.evalR L0.evalR c.evalR a0.evalR a1.evalR
        B.evalR L.evalR s.evalR A.evalR D.evalR rho.evalR i j := by
  simp only [capPower,CurveHighTemplates.capPower,eval_affineCapHighPower,
    eval_hCoeff,eval_pCoeff,eval_sCoeff,eval_uCoeff,eval_rCoeff]

theorem eval_budgetPower (B0 L0 c a0 a1 B L s A D rho : Fraction) (i : Fin 4) (j : Fin 3) :
    (budgetPower B0 L0 c a0 a1 B L s A D rho i j).evalR=
      CurveHighTemplates.budgetPower B0.evalR L0.evalR c.evalR a0.evalR a1.evalR
        B.evalR L.evalR s.evalR A.evalR D.evalR rho.evalR i j := by
  simp only [budgetPower,CurveHighTemplates.budgetPower,eval_affineBudgetHighPower,
    eval_hCoeff,eval_pCoeff,eval_sCoeff,eval_uCoeff,eval_rCoeff]

theorem eval_selectedPower (B0 L0 c a0 a1 B L s A D rho : Fraction) (i : Fin 4) (j : Fin 3) :
    (selectedPower B0 L0 c a0 a1 B L s A D rho i j).evalR=
      CurveHighTemplates.selectedPower B0.evalR L0.evalR c.evalR a0.evalR a1.evalR
        B.evalR L.evalR s.evalR A.evalR D.evalR rho.evalR i j := by
  unfold selectedPower CurveHighTemplates.selectedPower
  split_ifs
  · simp only [FractionHighTemplates.eval_selectedPower,eval_hCoeff,eval_pCoeff,
      eval_sCoeff,eval_uCoeff,eval_rCoeff]
  · exact Fraction.eval_zero (K:=ℝ)

theorem eval_tailPower (B0 L0 c a0 a1 B L s A D rho : Fraction) (i : Fin 4) (j : Fin 3) :
    (tailPower B0 L0 c a0 a1 B L s A D rho i j).evalR=
      CurveHighTemplates.tailPower B0.evalR L0.evalR c.evalR a0.evalR a1.evalR
        B.evalR L.evalR s.evalR A.evalR D.evalR rho.evalR i j := by
  unfold tailPower CurveHighTemplates.tailPower
  split_ifs
  · simp only [FractionHighTemplates.eval_tailPower,eval_hCoeff,eval_pCoeff,
      eval_sCoeff,eval_uCoeff,eval_rCoeff]
  · exact Fraction.eval_zero (K:=ℝ)

theorem eval_mapped (a : Fin 4→Fin 3→Fraction) (k e0 ev hi : Fraction) (i : Fin 4) (j : Fin 6) :
    (mapped a k e0 ev hi i j).evalR=
      CurveBernstein.mapped (fun m n=>(a m n).evalR) k.evalR e0.evalR ev.evalR hi.evalR i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [mapped,CurveBernstein.mapped,Fraction.evalR]

theorem eval_widthShift (a : Fin 4→Fin 6→Fraction) (lo hi : Fraction) (i : Fin 4) (j : Fin 6) :
    (widthShift a lo hi i j).evalR=
      CurveBernstein.widthShift (fun m n=>(a m n).evalR) lo.evalR hi.evalR i j := by
  fin_cases j <;>
    norm_num [widthShift,CurveBernstein.widthShift,Fin.sum_univ_succ,Nat.choose,Fraction.evalR] <;> ring

@[simp] theorem eval_highReserve : highReserve.evalR=CurvedSourceStep.highReserve := by
  norm_num [highReserve,CurvedSourceStep.highReserve,Fraction.evalR]

theorem eval_cellPower (p : Params) (cell : Cell) (i : Fin 4) (j : Fin 4) (k : Fin 3) :
    (cellPower p cell i j k).evalR=CurvedSourceStep.cellPower p.toReal cell.toReal i j k := by
  fin_cases i <;> simp only [cellPower,CurvedSourceStep.cellPower]
  all_goals first
    | rw [eval_capPower]
    | rw [eval_budgetPower]
    | rw [eval_tailPower]
    | rw [eval_selectedPower]
  all_goals simp only [eval_crossing,eval_highReserve,Params.toReal,Cell.toReal]
  all_goals norm_num [Fraction.evalR]


/-- Transport the compact integer sign checks to the literal real cell
certificate. Strict geometry remains explicit and cheap to check. -/
theorem Signs.toHighCellCertificate {p : Params} {cell : Cell} {combined : Bool}
    (h : Signs p cell combined)
    (hdensity : cell.lo.evalR<cell.hi.evalR)
    (hpos : 0<cell.lo.evalR) (hupper : cell.hi.evalR ≤ 3/4)
    (halo : 0<cell.a0.evalR+cell.a1.evalR*cell.lo.evalR)
    (hahi : 0<cell.a0.evalR+cell.a1.evalR*cell.hi.evalR)
    (halole : cell.a0.evalR+cell.a1.evalR*cell.lo.evalR ≤ cell.lo.evalR)
    (hahile : cell.a0.evalR+cell.a1.evalR*cell.hi.evalR ≤ cell.hi.evalR)
    (hwidth : cell.vl.evalR<cell.vh.evalR) :
    CurvedSourceStep.HighCellCertificate p.toReal cell.toReal combined where
  density_width := hdensity
  density_pos := hpos
  density_upper := hupper
  alpha_lo_pos := halo
  alpha_hi_pos := hahi
  alpha_lo_le := halole
  alpha_hi_le := hahile
  amplitude_cap := by
    intro i j
    rw [FastBernsteinBox.coefficients54_eq]
    have hc := Fraction.evalR_nonneg_of_num _ (h.1 i j)
    rw [FractionHighTemplates.eval_fast54] at hc
    simp only [eval_affineCapPower,eval_crossing,evalR_div,Params.toReal,Cell.toReal] at hc ⊢
    norm_num [Fraction.evalR] at hc ⊢
    exact hc
  amplitude_budget := by
    intro i j
    rw [FastBernsteinBox.coefficients54_eq]
    have hc := Fraction.evalR_nonneg_of_num _ (h.2.1 i j)
    rw [FractionHighTemplates.eval_fast54] at hc
    simp only [eval_affineBudgetPower,eval_crossing,evalR_div,Params.toReal,Cell.toReal] at hc ⊢
    norm_num [Fraction.evalR] at hc ⊢
    exact hc
  high := by
    intro i hi
    apply CurveBernstein.BoxCertificate.leaf (by norm_num) hwidth
    intro j k
    rw [FastBernsteinBox.coefficients35_eq]
    have hc := Fraction.evalR_nonneg_of_num _ (h.2.2 i hi j k)
    rw [FractionHighTemplates.eval_fast35] at hc
    simp only [eval_widthShift,eval_mapped,eval_cellPower,Params.toReal,Cell.toReal] at hc ⊢
    norm_num [Fraction.evalR] at hc ⊢
    exact hc

end
end Qrh.JointDetector.RepeatedMarks.FractionCurveData

#print axioms Qrh.JointDetector.RepeatedMarks.FractionCurveData.Signs.toHighCellCertificate
