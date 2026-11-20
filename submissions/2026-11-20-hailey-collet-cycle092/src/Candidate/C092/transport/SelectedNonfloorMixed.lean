/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The established exact mixed-price envelope applied to the original analytic
exponent. The actual source/count gain remains an explicit packet obligation. -/
import Candidate.C092.transport.SelectedNonfloorHeight
import Candidate.C092.transport.ActualMixedPriceAll

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open QRH.Record1252270103Return
open QRH.Cycle090 QRH.Cycle092.TopData QRH.Cycle092.Mixed QRH.Coverage
open QRH.ContactCertificate QRH.PhysicalCertificate
namespace QRH.Cycle092.SelectedNonfloor

/-- Every actual mixed leaf pays the authentic analytic exponent, provided
the original full packet attains its stipulated live source/count gain.
The gain is SUBTRACTED EXPLICITLY; this does not postulate that it has already
been constructed on any physical row family. -/
theorem mixed_raw_exponent_below_target {r : Row} (hr : r ∈ rows)
    {h x D xi z : ℝ} {point : Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : r.box.Contains point)
    (hx : QRH.RationalInterval.Contains alphaInterval x)
    (hD : (1/100:ℝ) ≤ D) (hDh : D ≤ h+rowPad)
    (hxi0 : 0 ≤ xi) (hxi1 : xi ≤ (rowGamma r.box r.B:ℝ))
    (hz0 : widthLo ≤ z) (hz1 : z ≤ widthHi)
    (a e t eps momentLoss massLoss : ℝ) (ha : 2*a-1 = point.1) :
    letI : Geometry.Parameters := ActualGeometry.parameters h hh hh'
    rawExponent a point.2 (pairedCount point.1 point.2 (g0 (wValue x)) (g1 (wValue x)))
        D sourceCost e t eps momentLoss massLoss-
      D*point.1*ActualMixedPrice.gain r point.2 x xi z+
      Cycle090.paddingDebit+1/100000000000000 <
    Geometry.signalShift+theta-inwardDebit-1/1000000000000+
      (16*e+2*eps*D+D*(momentLoss/4+massLoss)+17*t/25) := by
  letI : Geometry.Parameters := ActualGeometry.parameters h hh hh'
  have hDp : 0 < D := (by norm_num : (0:ℝ)<1/100).trans_le hD
  have hs := ActualMixedPrice.all_rows_uniform_physical_reserve hr hh hh' hp hx hD hDh hxi0 hxi1 hz0 hz1
  have he : Physical.price h point.1 point.2 (g0 (wValue x)) (g1 (wValue x)) D-theta+inwardDebit ≤
      ActualMixedPrice.excess h point.1 point.2 x D := by
    exact le_max_right _ _
  rw [raw_exponent_eq_price _ _ _ _ _ _ _ _ _ _ hDp.ne', ha,
    row_price_at_Q h hh hh' point.1 point.2 (g0 (wValue x)) (g1 (wValue x)) D hDp]
  dsimp only [ActualMixedPrice.saving] at hs
  linarith

end QRH.Cycle092.SelectedNonfloor
#print axioms QRH.Cycle092.SelectedNonfloor.mixed_raw_exponent_below_target
