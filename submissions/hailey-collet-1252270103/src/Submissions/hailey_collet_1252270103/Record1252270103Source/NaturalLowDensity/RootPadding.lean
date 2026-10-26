/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Range extension of outputs/record-c012518109-20261019/formalization/Record12518109Gain/RootPadding.lean. Original formulas and source attribution retained. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.NaturalLowDensity.MaxRescale

set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.NaturalLowDensity
open Record12518109Gain
noncomputable section

/-- Padding the actual natural conductor loses at most rho times the
padding width; the full gain at the unpadded core width is retained. -/
theorem padded_core_exponent {ν S q δ L b : ℝ}
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hδ : 0≤δ) :
    rho ν*(q+δ)+ν*S-gain ν S (q+δ)+(q+δ)*L+2*b*S≤
      rho ν*q+ν*S-gain ν S q+rho ν*δ+(q+δ)*L+2*b*S := by
  have hh:=gain_mono (S:=S) hν0 hν1 le_rfl (show q≤q+δ by linarith)
  nlinarith

theorem padded_core_power {ν S q δ L b Z : ℝ}
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hδ : 0≤δ) (hZ : 1≤Z) :
    Z^(rho ν*(q+δ)+ν*S-gain ν S (q+δ)+(q+δ)*L+2*b*S)≤
      Z^(rho ν*q+ν*S-gain ν S q+rho ν*δ+(q+δ)*L+2*b*S) :=
  Real.rpow_le_rpow_of_exponent_le hZ (padded_core_exponent hν0 hν1 hδ)

end
end QRH.Record1252270103Source.NaturalLowDensity
