/- SPDX-License-Identifier: Apache-2.0
Cycle092 source adaptation: local import paths and anonymous local instance names
may be relocated for submission. Inherited attribution is retained in this source,
Candidate.Provenance and metadata.json. This notice assigns no new authorship. -/
import Candidate.C092.Intake.QRH.SourceCertificate.Core

/-!
# Recovered source raw geometry and radial gates

The expressions below are the actual 21 formulas in `CHECK_SYMMETRIC.py`,
recomputed from the source parameters. The reported JSON gate values are not
used as premises. These are finite arithmetic facts, not an analytic source or
physical-endpoint admission theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace QRH.SourceCertificate

/-- Actual source derivative away from the seam, using the right derivative at the seam. -/
def gainDerivative (y : ℚ) : ℚ :=
  if y < seam then -(87/500)-2*(67/10)*(seam-y)
  else -2*(2309/500)*(Y-y)-3*(101/2)*(Y-y)^2-31/100000
/-- Width maximum used by the source raw and radial checks. -/
def maxWidth : ℚ := 1/2-369/1000+gain (369/1000)
/-- Volume bound used by the source raw and radial checks. -/
def maxVolume : ℚ := (1+(1+23/20)*Y)/2+gain Y
/-- Source absolute derivative bound proposed by the original finite checker. -/
def derivativeBound : ℚ := max (-gainDerivative (369/1000)) (-gainDerivative seam)
/-- Rational fifth-root enclosure at the tangent-to-curve interface. -/
def seamRootUpper : ℚ := 445771590373/2000000000000

/-- The radical enclosure used by the tangent-to-curve gate is valid. -/
theorem seamRootUpper_guard : RootGuard (3/4) seamRootUpper := by decide +kernel

/-- All literal source raw geometry and radial gate formulas, with their original names. -/
def rawAndRadiusGates : List (String × ℚ) := [
  ("start", -max (gain Y) (gain (Y/H))),
  ("start_convex", 2*(2309/500)+6*(101/2)*(Y-Y/H)),
  ("seam_low_crossing", gainDerivative (H*seam)-gainDerivative (seam/H)),
  ("derivative", 1/4-derivativeBound),
  ("native_margin", 3/20-(1/2-369/1000)),
  ("radius_max_long", 1/2-(23/20)*Y/(49/50)),
  ("reorder_ratio", (23/20)-Y/(369/1000)),
  ("capacities_slope_upper", 61/100-(1/2+gain (369/1000)+Y*derivativeBound)),
  ("low_abs_slope", 5/6-responseUpper*(61/100)),
  ("sub_abs_slope", 5/6-(3/4)/2-responseUpper*(61/100)),
  ("short_reference", H-4*(23/200+maxWidth)),
  ("long_reference", 73/100-((1+23/20)*Y-23/200)),
  ("signed", 5/6+23/200-maxVolume-3*u),
  ("first_zero", 1-maxVolume),
  ("second_zero_slots", 1-5*u),
  ("second_zero_norm", 1-maxVolume-4*u),
  ("sn9_fixed", (5001/10000)*(49/50-maxVolume)),
  ("native_98", u-rho+(5/6)*(H-49/50)-(3/4)*max 0 (1/100+gain (369/1000)-u)),
  ("unmarked_875", u-rho+(5/6)*(H-7/8)-(3/4)*(maxWidth-u)),
  ("small_08", u-rho+(5/6)*(H-2/25)-(3/4)*(1+23/20)*Y-(maxWidth-u)),
  ("tangent_to_curve", quota (3/4) seamRootUpper-
    ((1-(3/4))/2+5805911/100000000-(379981/5000000)*(3/4)))
]

/-- Kernel computation validates all 21 actual rational gate expressions. -/
theorem rawAndRadiusGates_checked :
    rawAndRadiusGates.length = 21 ∧ rawAndRadiusGates.all (fun p => decide (0 < p.2)) = true := by
  decide +kernel

/-- Every named gate has a strictly positive exact rational reserve. -/
theorem rawAndRadiusGates_positive (name : String) (value : ℚ)
    (h : (name, value) ∈ rawAndRadiusGates) : 0 < value := by
  exact of_decide_eq_true ((List.all_eq_true.mp rawAndRadiusGates_checked.2) (name,value) h)

/-- The source width maximum agrees exactly with the replayed report. -/
theorem maxWidth_value : maxWidth = 266370430517/2000000000000 := by decide +kernel
/-- The source volume bound agrees exactly with the replayed report. -/
theorem maxVolume_value : maxVolume = 9179599/10000000 := by decide +kernel

end QRH.SourceCertificate
