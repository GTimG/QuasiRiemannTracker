/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.FractionCurveData
namespace Qrh.JointDetector.CurvedSourceFractions
open RepeatedMarks.FractionArithmetic RepeatedMarks.FractionCurveData
set_option autoImplicit false
def phi : Fraction := 999999999/1000000000
def slope (n : ℕ) : Fraction := Fraction.ofInt (2566860586289-(n:ℤ)*50000000)/1000000000000
def cap (n : ℕ) : Fraction := if n≤17036 then 1/10 else 1/10+Fraction.ofInt ((n-17036:ℕ):ℤ)/10000
def point (n : ℕ) (B0 B : Fraction) : Params :=
  ⟨B0,slope n,cap n,B,slope (n+1),cap (n+1),
    (if n+1≤17036 then 7/20 else 3/20),(if n+1≤17036 then 40 else 0)⟩
def clippedRay (p : Params) : Fraction := amplitudeFloor/matchedCut p phi 0
def oneBank (p : Params) (ray : Fraction) : Fin 1 → Cell := ![rayCell p phi ray]
def twoBank (p : Params) (ray : Fraction) : Fin 2 → Cell := ![constantCell p phi ray,lateRayCell p phi ray]
def threeBank (p : Params) (ray : Fraction) : Fin 3 → Cell := ![constantCell p phi ray,lateRayCell p phi ray,earlyRayCell p phi ray]
end Qrh.JointDetector.CurvedSourceFractions
