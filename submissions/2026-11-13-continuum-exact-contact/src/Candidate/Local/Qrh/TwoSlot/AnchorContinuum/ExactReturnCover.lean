/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The complete limiting four-edge scalar cover: 37 strict interval-polynomial
checks and 20 cells supplied by the exact critical-rectangle factorization.
Count-envelope transport and positive analytic costs are separate obligations. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ExactReturnData
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.CriticalRectangle
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ReturnCount

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
noncomputable section
open Set IntervalPolynomial IntervalPolynomial.P2
open Qrh.TwoSlot.AnchorZeroLoss.Affine.Return

theorem ev_markedJ (d p : ℝ) : ev markedJ d p = ExactWindow.JI d p := by
  simp only [markedJ,markedK,V,ev_add,ev_sub,ev_smul,ev_mul,ev_C,ev_X,ev_Y]
  dsimp [R,Coeff.rat,Coeff.add,Coeff.mul,g1C]
  norm_num
  unfold ExactWindow.JI ExactWindow.kI exactLine
  ring

theorem ev_markedN (d p : ℝ) : ev markedN d p = ExactWindow.NI d p := by
  simp only [markedN,markedU,V,ev_add,ev_sub,ev_smul,ev_mul,ev_C,ev_X,ev_Y,ev_markedJ]
  dsimp [R,Coeff.rat,Coeff.add,Coeff.sub,Coeff.neg,Coeff.mul,g0C,g1C]
  norm_num
  unfold ExactWindow.NI ExactWindow.UI exactLine
  ring

theorem ev_critical_base (d p : ℝ) : ev (Ebase 3) d p = baseCost stationaryCutoff d p := by
  simp only [Ebase,ev_add,ev_sub,ev_smul,ev_mul,ev_C,ev_X,ev_Y]
  norm_num [edgeD,edgeC,hC,ellC,yC,R,Coeff.rat,Coeff.add,Coeff.sub,Coeff.neg,Coeff.mul,Coeff.div]
  unfold baseCost
  ring

theorem critical_polynomial (d p : ℝ) :
    ev (marginP 3 .improved) d p = margin stationaryCutoff d p := by
  simp only [marginP,J,N,ev_sub,ev_mul,ev_C,ev_smul,ev_markedJ,ev_markedN,ev_critical_base]
  norm_num [thetaC,edgeD,hC,R,Coeff.rat,Coeff.mul]
  unfold margin
  ring

theorem cell_admitted (i : Fin 57) : (RationalReturn.ReturnQ.cells i).admitted := by
  have hh := RationalReturn.ReturnQ.cells_checked i
  simp only [RationalReturn.ReturnQ.Cell.ok,Bool.and_eq_true,decide_eq_true_eq] at hh
  exact hh.1

theorem cell_nonnegative (i : Fin 57) {d p : ℝ}
    (hd : 0 ≤ d) (hp : 0 ≤ p)
    (hd0 : ((RationalReturn.ReturnQ.cells i).dlo:ℝ) ≤ d)
    (hd1 : d ≤ ((RationalReturn.ReturnQ.cells i).dhi:ℝ))
    (hp0 : ((RationalReturn.ReturnQ.cells i).plo:ℝ) ≤ p)
    (hp1 : p ≤ ((RationalReturn.ReturnQ.cells i).phi:ℝ)) :
    0 ≤ ev (marginP (RationalReturn.ReturnQ.cells i).edge
      (codeOf (RationalReturn.ReturnQ.cells i).code)) d p := by
  by_cases hi : isCritical i
  · obtain ⟨he,hc⟩ := hi
    have he3 : (RationalReturn.ReturnQ.cells i).edge = (3:Fin 4) := Fin.ext he
    have had := cell_admitted i
    simp only [RationalReturn.ReturnQ.Cell.admitted,hc] at had
    obtain ⟨hd',hp'⟩ := RationalReturn.ReturnQ.cell_intervals _
      had.1 had.2.1 had.2.2.1 had.2.2.2 hd0 hd1 hp0 hp1
    rw [he3,hc,codeOf,critical_polynomial]
    exact critical_rectangle_nonnegative (by simpa using hd') (by simpa using hp')
  · exact (strict_cell_positive i hi hd hp hd0 hd1 hp0 hp1).le

/-- The saved exact cover pays a correctly admitted scalar branch at every
density/amplitude point on each of the four limiting conductor edges. -/
theorem complete_edge_cover (e : Fin 4) {d p : ℝ}
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    ∃ i : Fin 57, (RationalReturn.ReturnQ.cells i).edge = e ∧
      (RationalReturn.ReturnQ.cells i).admitted ∧
      0 ≤ ev (marginP e (codeOf (RationalReturn.ReturnQ.cells i).code)) d p := by
  obtain ⟨i,he,hd0,hd1,hp0,hp1⟩ := RationalReturn.ReturnQ.cells_cover e hd hp
  refine ⟨i,he,cell_admitted i,?_⟩
  rw [←he]
  exact cell_nonnegative i hd.1 hp.1 hd0 hd1 hp0 hp1

end
end Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.complete_edge_cover
