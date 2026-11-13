/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
The limiting edge-margin polynomials with interval-enclosed exact parameters.
Uses the existing admitted native polynomials and Sil's exact marked count. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.IntervalPolynomial
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ParameterPrecision
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.ExactCountScheme

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
noncomputable section
open IntervalPolynomial IntervalPolynomial.P2
open QRH.ArviReturnTuning
open QRH.PositiveGap.ReturnTuning (toQ)

def R (q : ℚ) : Coeff := Coeff.rat q
def thetaC : Coeff := ⟨Precision.thetaBox,theta,Precision.theta_sound⟩
def hC : Coeff := ⟨⟨815324503/1000000000,163064901/200000000⟩,stationaryCutoff,by
  simpa [RationalInterval.Box.Contains] using
    And.intro Precision.cutoff_bounds.1.le Precision.cutoff_bounds.2.le⟩
def ellC : Coeff := ⟨Precision.ellBox,ell,Precision.ell_sound⟩
def g0C : Coeff := ⟨Precision.g0Box,tangentIntercept,Precision.g0_sound⟩
def g1C : Coeff := ⟨Precision.g1Box,-tangentSlope,Precision.g1_sound⟩
def yC : Coeff := hC.sub ((R 2).mul ellC)
def kappaC : Coeff := ((R 2).mul thetaC).sub (R 1)
def k3 : Coeff := (R 3).mul kappaC
def k6 : Coeff := (R 6).mul kappaC
theorem k3_pos : 0 < k3.box.lo := by
  norm_num [k3,kappaC,thetaC,R,Coeff.rat,Coeff.mul,Coeff.sub,Coeff.add,Coeff.neg,
    RationalInterval.point,RationalInterval.mul,RationalInterval.add,RationalInterval.neg,Precision.thetaBox]
theorem k6_pos : 0 < k6.box.lo := by
  norm_num [k6,kappaC,thetaC,R,Coeff.rat,Coeff.mul,Coeff.sub,Coeff.add,Coeff.neg,
    RationalInterval.point,RationalInterval.mul,RationalInterval.add,RationalInterval.neg,Precision.thetaBox]

def edgeD : Fin 4 → Coeff := ![R (1/200),R (19/25),R (19/25),hC]
def edgeC : Fin 4 → Coeff :=
  ![(R (1/200)).div k6 k6_pos,
    (((R 2).mul yC).sub (R (19/25))).div k6 k6_pos,
    R ((3/40)*(19/25)),
    (hC.sub ((R 4).mul ellC)).div (R 2) (by norm_num [R,Coeff.rat,RationalInterval.point])]

inductive Code | old | native | nativeLow | improved deriving DecidableEq, Repr

def V : P2 := sub (C (R (5/6))) X
def oldD : P2 := sub (sub (C (R 3)) Y) (smul ((R 2).div k3 k3_pos) Y)
def oldC : P2 := mul (smul (R 2) (sub (C (R 1)) Y))
  (sub (C (R 1)) (smul ((R 1).div k3 k3_pos) Y))
def oldJ : P2 := add (mul V oldD) (mul X oldC)
def oldN : P2 := add (mul (sub (C (R 1)) X) oldJ) (smul (R (1/2)) (mul (mul X oldC) V))
def markedK : P2 := sub (C (R 1)) (smul ((R 1).add ((R 2).mul g1C)) Y)
def markedU : P2 := sub (C (R 1)) (smul (((R 1).add ((R 6).mul g0C)).sub ((R 4).mul g1C)) Y)
def markedJ : P2 := add (smul (R 3) V) (smul (R 2) (mul X markedK))
def markedN : P2 := add (mul (sub (C (R 1)) X) markedJ) (mul (mul V X) markedU)
def J : Code → P2
  | .old => oldJ
  | .native | .nativeLow => lift (toQ .C).Jq
  | .improved => markedJ
def N : Code → P2
  | .old => oldN
  | .native | .nativeLow => lift (toQ .C).Nq
  | .improved => markedN

def Ebase (e : Fin 4) : P2 :=
  add (C (((((R (1/2)).add ((R (13/75)).mul hC)).sub ((R (1/2)).mul yC)).sub
    ((R (1/2)).mul ellC)).sub ((R (9/100)).mul (edgeD e))))
    (add (smul (R (1/2)) X) (smul (ellC.sub ((R (1/2)).mul (edgeC e))) (mul X Y)))
def marginP (e : Fin 4) (b : Code) : P2 :=
  sub (mul (J b) (sub (C thetaC) (Ebase e))) (smul ((R (3/4)).mul (edgeD e)) (N b))

end
end Qrh.TwoSlot.AnchorContinuum.Contact.ExactReturn
