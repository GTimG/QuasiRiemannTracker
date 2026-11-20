/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact exponent accounting from the original reciprocal/packet/contour factors
to the literal Q physical price. No source or count bound is assumed here. -/
import Candidate.C092.transport.SelectedNonfloorFullW

noncomputable section
set_option autoImplicit false
open QRH.Record1252270103Return
namespace QRH.Cycle092.SelectedNonfloor
variable [Geometry.Parameters]

/-- The conductor-unit row price with the ACTUAL row-cardinality exponent R.
No paired-count formula is substituted before the count has been proved. -/
def rowPrice (delta p R D source : ℝ) : ℝ :=
  1/2+13*Geometry.h/75-Geometry.y/2-Geometry.ell/2-9*D/100+delta/2+
    delta*p*(Geometry.ell-D*Physical.Selection.zeroCapacity Geometry.y source D/2)+3*D*R/4

/-- Original contour power, genuine reciprocal scalar, full P15 front, and
source fourth/count/amplitude power. Height and inverse-normalizer losses can
be added afterwards; none is silently charged to a central scalar margin. -/
def rawExponent (a p R D source e t eps momentLoss massLoss : ℝ) : ℝ :=
  4*Geometry.x/25+a+16*e-33/50-Geometry.y/2-4*Geometry.ell/25+
    D*((2*a-1)*p*(Geometry.ell/D-Physical.Selection.zeroCapacity Geometry.y source D/2)+
      (3*R+1+momentLoss)/4+massLoss-17/50+2*eps)+17*t/25

/-- Exact price identity, including every displayed small loss. The term
`-17D/50` comes from the TRUE physical reciprocal scalar. -/
theorem raw_exponent_eq_price (a p R D source e t eps momentLoss massLoss : ℝ)
    (hD : D ≠ 0) :
    rawExponent a p R D source e t eps momentLoss massLoss =
      Geometry.signalShift+rowPrice (2*a-1) p R D source+
        16*e+2*eps*D+D*(momentLoss/4+massLoss)+17*t/25 := by
  have hx : Geometry.x = 1-Geometry.y-Geometry.ell := by linarith [Geometry.x_add_y]
  unfold rawExponent rowPrice Geometry.signalShift Geometry.h
  rw [hx]
  field_simp
  <;> ring

/-- Q's native geometry gives precisely the physical Q1 formula, after a
GENUINE count theorem has supplied its particular paired count. -/
theorem row_price_at_Q (h : ℝ) (hl : Cycle090.hLower ≤ h) (hu : h ≤ Cycle090.hUpper)
    (delta p g0 g1 D : ℝ) (hD : 0 < D) :
    @rowPrice (ActualGeometry.parameters h hl hu) delta p (Cycle090.pairedCount delta p g0 g1) D Cycle090.sourceCost =
      Physical.price h delta p g0 g1 D := by
  have hc := Physical.Selection.scaled_zero_capacity (y:=Cycle090.yLength h)
    (s:=Cycle090.sourceCost) hD
  change D*Physical.Selection.zeroCapacity (Cycle090.yLength h) Cycle090.sourceCost D =
    Cycle090.cappedCapacity Cycle090.physicalCap (Cycle090.yLength h) Cycle090.sourceCost D at hc
  unfold rowPrice Physical.price
  rw [ActualGeometry.parameters_h]
  change 1/2+13*h/75-(Cycle090.yLength h)/2-Cycle090.ell/2-9*D/100+delta/2+
    delta*p*(Cycle090.ell-D*Physical.Selection.zeroCapacity (Cycle090.yLength h) Cycle090.sourceCost D/2)+
      3*D*Cycle090.pairedCount delta p g0 g1/4 = _
  rw [hc]
  change 1/2+13*h/75-(h-2*Physical.ell)/2-Physical.ell/2-9*D/100+delta/2+
    delta*p*(Physical.ell-Cycle090.cappedCapacity Cycle090.physicalCap (h-2*Physical.ell) Cycle090.sourceCost D/2)+
      3*D*Cycle090.pairedCount delta p g0 g1/4 = _
  rfl

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.raw_exponent_eq_price
#print axioms QRH.Cycle092.SelectedNonfloor.row_price_at_Q
