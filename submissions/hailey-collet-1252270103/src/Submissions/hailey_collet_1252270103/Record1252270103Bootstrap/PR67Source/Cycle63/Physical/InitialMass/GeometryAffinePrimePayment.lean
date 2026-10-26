import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryFinalLowLoss
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section

/-- The actual prime-cardinality lower bound cancels the amplifier exponent
once. All source, profile, and height factors can remain in the constant. -/
theorem geometry_affine_prime_power_payment
    (Z n amp loss target coefficient C : ℝ)
    (hZ : 0<Z) (hn : Z^(amp-loss)≤n)
    (hc : 0≤ coefficient) (hC : 0≤C) :
    (56/n)*coefficient*(C*Z^target)≤
      (56*coefficient*C)*Z^(target+loss-amp) := by
  have hp : 0<Z^(amp-loss) := Real.rpow_pos_of_pos hZ _
  have hnum : 0≤(56*coefficient*C)*Z^target := by positivity
  calc
    (56/n)*coefficient*(C*Z^target) = ((56*coefficient*C)*Z^target)/n := by ring
    _ ≤ ((56*coefficient*C)*Z^target)/Z^(amp-loss) :=
      div_le_div_of_nonneg_left hnum hp hn
    _ = (56*coefficient*C)*(Z^target/Z^(amp-loss)) := by ring
    _ = (56*coefficient*C)*Z^(target+loss-amp) := by
      rw [←Real.rpow_sub hZ]
      congr 2
      ring

/-- A retained ordinary bound is paid using its single prime average and
the existing amplifier-coefficient cap. The exponent premise includes the
selection, ratio, and prime losses before comparison with the final saving. -/
theorem geometry_affine_prime_payment_of_bound
    (Z n amp loss target exponent coefficient cap C value : ℝ)
    (hZ : 1<Z) (hn : Z^(amp-loss)≤n)
    (hc : 0≤ coefficient) (hcap : coefficient≤ cap) (hC : 0≤C)
    (hvalue : value≤C*Z^target) (hexponent : target+loss-amp≤exponent) :
    (56/n)*coefficient*value≤(56*cap*C)*Z^exponent := by
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hn0 : 0<n := (Real.rpow_pos_of_pos hZ0 _).trans_le hn
  have hv := mul_le_mul_of_nonneg_left hvalue
    (mul_nonneg (div_nonneg (by norm_num : (0:ℝ)≤56) hn0.le) hc)
  have hp := geometry_affine_prime_power_payment Z n amp loss target coefficient C hZ0 hn hc hC
  have hcoef : 56*coefficient*C≤56*cap*C := by gcongr
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le hexponent
  have hcap0 : 0≤ cap := hc.trans hcap
  exact (hv.trans hp).trans (mul_le_mul hcoef hpow
    (Real.rpow_nonneg hZ0.le _) (by positivity))

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
