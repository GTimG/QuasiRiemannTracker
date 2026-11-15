/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The genuine admitted exact count envelope pays every limiting conductor edge.
This is a return inequality, not yet the positive-cost analytic endpoint. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ExactCountTransport

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
noncomputable section
open Set IntervalPolynomial IntervalPolynomial.P2

def price (D cap d p : ℝ) : ℝ :=
  1/2+13*stationaryCutoff/75-(stationaryCutoff-2*ell)/2-ell/2-9*D/100+
    d/2+d*p*(ell-cap/2)
def row (D cap d p : ℝ) : ℝ := price D cap d p+(3/4)*D*envelope d p

theorem ev_price (e : Fin 4) (d p : ℝ) :
    ev (Ebase e) d p = price (edgeD e).value (edgeC e).value d p := by
  simp only [Ebase,ev_add,ev_C,ev_smul,ev_mul,ev_X,ev_Y]
  dsimp [R,Coeff.rat,Coeff.add,Coeff.sub,Coeff.neg,Coeff.mul,hC,ellC,yC]
  norm_num
  unfold price
  ring

theorem ev_margin (e : Fin 4) (b : Code) (d p : ℝ) :
    ev (marginP e b) d p = ev (J b) d p*(theta-price (edgeD e).value (edgeC e).value d p)-
      (3/4)*(edgeD e).value*ev (N b) d p := by
  simp only [marginP,ev_sub,ev_mul,ev_C,ev_smul,ev_price]
  dsimp [thetaC,R,Coeff.rat,Coeff.mul]
  norm_num

theorem edgeD_nonnegative (e : Fin 4) : 0 ≤ (edgeD e).value := by
  fin_cases e <;> norm_num [edgeD,R,Coeff.rat,hC,stationaryCutoff_pos.le]

theorem edge_bound (e : Fin 4) {d p : ℝ}
    (hd : d ∈ Icc (0:ℝ) (3/4)) (hp : p ∈ Icc (0:ℝ) (1/2)) :
    row (edgeD e).value (edgeC e).value d p ≤ theta := by
  obtain ⟨i,he,hd0,hd1,hp0,hp1⟩ := RationalReturn.ReturnQ.cells_cover e hd hp
  have hM := cell_nonnegative i hd.1 hp.1 hd0 hd1 hp0 hp1
  rw [he,ev_margin] at hM
  have hJ := denominator_pos (codeOf (RationalReturn.ReturnQ.cells i).code) hd hp
  have hR := envelope_le_cell i hd hp hd0 hd1 hp0 hp1
  have hRN := mul_le_mul_of_nonneg_left ((le_div_iff₀ hJ).mp hR)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 3/4) (edgeD_nonnegative e))
  have hmul : ev (J (codeOf (RationalReturn.ReturnQ.cells i).code)) d p*
      row (edgeD e).value (edgeC e).value d p ≤
      ev (J (codeOf (RationalReturn.ReturnQ.cells i).code)) d p*theta := by
    unfold row
    nlinarith only [hM,hRN]
  exact (mul_le_mul_iff_right₀ hJ).mp hmul

end
end Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn.edge_bound
