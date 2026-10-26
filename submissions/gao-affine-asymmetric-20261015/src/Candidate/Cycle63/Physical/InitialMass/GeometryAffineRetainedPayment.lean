/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainScalarPayment

set_option autoImplicit false
set_option maxHeartbeats 40000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- Close the scalar part of the actual main contraction after putting both
selected branches under one profile and height control. The exceptional
payment is already averaged; the ordinary payment uses the prime factor once. -/
theorem geometry_affine_main_contracted_payment
    (Z n amp δ low high target coefficient cap Cb Ksel CL CH Ce Co control
      main exceptional ratio : ℝ)
    (hZ : 1<Z) (hn : Z^(amp-δ)≤n)
    (hc : 0≤coefficient) (hcap : coefficient≤cap)
    (hCb : 0≤Cb) (hKsel : 0≤Ksel) (hCL : 0≤CL) (hCH : 0≤CH)
    (hCo : 0≤Co) (hcontrol : 0≤control)
    (hcontract : (56/n)*coefficient*main≤exceptional+Co*((56/n)*coefficient*ratio))
    (hexceptional : exceptional≤Ce*control*Z^target)
    (hratio : ratio≤Cb*(Ksel*Z^δ*((CL*control)*Z^low+(CH*control)*Z^high))*Z^δ)
    (hlow : low+3*δ-amp≤target) (hhigh : high+3*δ-amp≤target) :
    (56/n)*coefficient*main≤
      (Ce+Co*(56*cap*Cb*Ksel*(CL+CH)))*control*Z^target := by
  have hp := geometry_affine_main_selected_ratio_payment
    Z n amp δ low high target coefficient cap Cb Ksel (CL*control) (CH*control) ratio
    hZ hn hc hcap hCb hKsel (mul_nonneg hCL hcontrol) (mul_nonneg hCH hcontrol)
    hratio hlow hhigh
  apply hcontract.trans
  have hs := add_le_add hexceptional (mul_le_mul_of_nonneg_left hp hCo)
  convert hs using 1 <;> ring

/-- The error family already contains its single prime average in the joint
weight. Its contraction and finite ratio image therefore need no further
prime factor. The first error weight remains inside that family. -/
theorem geometry_affine_error_contracted_payment
    (Z εratio exponent target Cb C Ce Co control paidError exceptional ratio : ℝ)
    (hZ : 1<Z) (hCb : 0≤Cb) (hC : 0≤C) (hCo : 0≤Co) (hcontrol : 0≤control)
    (hcontract : paidError≤exceptional+Co*ratio)
    (hexceptional : exceptional≤Ce*control*Z^target)
    (hratio : ratio≤Cb*(C*control*Z^exponent)*Z^εratio)
    (hexponent : exponent+εratio≤target) :
    paidError≤(Ce+Co*Cb*C)*control*Z^target := by
  have hz := Real.rpow_le_rpow_of_exponent_le hZ.le hexponent
  have hp := mul_le_mul_of_nonneg_left hz
    (mul_nonneg (mul_nonneg hCb hC) hcontrol)
  have heq : Cb*(C*control*Z^exponent)*Z^εratio=
      (Cb*C*control)*Z^(exponent+εratio) := by
    rw [Real.rpow_add (zero_lt_one.trans hZ)]
    ring
  rw [heq] at hratio
  have hs := add_le_add hexceptional
    (mul_le_mul_of_nonneg_left (hratio.trans hp) hCo)
  apply hcontract.trans
  convert hs using 1 <;> ring

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_main_contracted_payment
#print axioms OAI.SevenEighths.Cycle63InitialMass.geometry_affine_error_contracted_payment
