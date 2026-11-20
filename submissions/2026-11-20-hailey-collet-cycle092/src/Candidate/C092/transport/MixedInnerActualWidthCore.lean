/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The true native saturation faces constrain the ACTUAL supporting lengths.
Neither the paired crossing nor the scalar witness minimizer replaces m. -/
import Candidate.C092.transport.MixedOffsetCountBranchData
import Candidate.C092.transport.RawTicketAdmission
set_option autoImplicit false
namespace QRH.Cycle092.MixedInnerActualWidth
noncomputable section
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed
open QRH.Cycle092.MixedCenteredFaces

/-- Strict insufficiency of the genuine centered count controls both actual
inverse and ordinary lengths on the same supporting original-row class. -/
theorem insufficient_saturation {delta k r m t0 H q0 : ℝ}
    (hd : 0< delta) (hk : 0< k)
    (h : delta*center k r m (t0/3) H<4*q0/3) :
    r<2*t0/3+4*q0/(3*delta*k) ∧
    m< t0/3+2*q0/(3*delta*k) := by
  have hI : k*(r-2*(t0/3))≤ center k r m (t0/3) H:=le_max_left _ _
  have hO : 2*k*(m-t0/3)≤ center k r m (t0/3) H:=by
    have hz:=le_max_right (0:ℝ) (m-t0/3)
    exact (mul_le_mul_of_nonneg_left hz (by positivity : 0≤2*k)).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hi:=mul_le_mul_of_nonneg_left hI hd.le
  have ho:=mul_le_mul_of_nonneg_left hO hd.le
  constructor
  · have hx : (r-2*t0/3)*(3*delta*k)<4*q0 := by nlinarith only [hi,h]
    have :=(lt_div_iff₀ (by positivity : 0<3*delta*k)).mpr hx
    linarith only [this]
  · have hy : (m-t0/3)*(3*delta*k)<2*q0 := by nlinarith only [ho,h]
    have :=(lt_div_iff₀ (by positivity : 0<3*delta*k)).mpr hy
    linarith only [this]

/-- The supported product lower bound turns the inverse upper bound into a
lower bound for the SAME ordinary dyad length. -/
theorem insufficient_actual_range {delta k r m t0 H q0 xi ann : ℝ}
    (hd : 0< delta) (hk : 0< k)
    (h : delta*center k r m (t0/3) H<4*q0/3)
    (hsupport : t0-xi-ann≤ r+m) :
    t0/3-xi-4*q0/(3*delta*k)-ann< m ∧
    m< t0/3+2*q0/(3*delta*k) := by
  have hh:=insufficient_saturation hd hk h
  constructor <;> linarith only [hh.1,hh.2,hsupport]

/-- Directed rational bounds used by the finite certificate below. The
refined top budget remains separate from the original old-debit fees. -/
def lowerM (box : QRH.Coverage.Box) : ℚ :=
  (1+box.uLo*(1-box.vHi*(1+6*(5805913/100000000)-4*(3799809/50000000)))/
    (5/2-box.uLo*(1+2*box.vHi*(1+2*(3799809/50000000)))))/3
def upperM (box : QRH.Coverage.Box) : ℚ :=
  (1+box.uHi*(1-box.vLo*(1+6*(5805911/100000000)-4*(379981/5000000)))/
    (5/2-box.uHi*(1+2*box.vLo*(1+2*(379981/5000000)))))/3
def lowerK (box : QRH.Coverage.Box) : ℚ :=1-box.vHi*(1+2*(379981/5000000))
def lambdaX (r : Row) : ℚ:=4*rowBudget r.B/(3*r.box.uLo*lowerK r.box)
def lambdaY (r : Row) : ℚ:=2*rowBudget r.B/(3*r.box.uLo*lowerK r.box)
def widthCheck (r : Row) : Bool:=decide (
  (4643/12500:ℚ)≤ lowerM r.box-rowGamma r.box r.B-lambdaX r-3/10^(13:ℕ) ∧
  upperM r.box+lambdaY r+1/10^(13:ℕ)≤(947/2500:ℚ))

end
end QRH.Cycle092.MixedInnerActualWidth
#print axioms QRH.Cycle092.MixedInnerActualWidth.insufficient_saturation
#print axioms QRH.Cycle092.MixedInnerActualWidth.insufficient_actual_range
