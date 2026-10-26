import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.MaxRescale

namespace Record12518109Gain
noncomputable section

/-- Padding the actual natural conductor loses at most rho times the
padding width; the full gain at the unpadded core width is retained. -/
theorem padded_core_exponent {ν S q δ L b : ℝ}
    (hν0 : 31/50≤ν) (hν1 : ν≤3/4) (hδ : 0≤δ) :
    rho ν*(q+δ)+ν*S-gain ν S (q+δ)+(q+δ)*L+2*b*S≤
      rho ν*q+ν*S-gain ν S q+rho ν*δ+(q+δ)*L+2*b*S := by
  have hh:=gain_mono (S:=S) hν0 hν1 le_rfl (show q≤q+δ by linarith)
  nlinarith

theorem padded_core_power {ν S q δ L b Z : ℝ}
    (hν0 : 31/50≤ν) (hν1 : ν≤3/4) (hδ : 0≤δ) (hZ : 1≤Z) :
    Z^(rho ν*(q+δ)+ν*S-gain ν S (q+δ)+(q+δ)*L+2*b*S)≤
      Z^(rho ν*q+ν*S-gain ν S q+rho ν*δ+(q+δ)*L+2*b*S) :=
  Real.rpow_le_rpow_of_exponent_le hZ (padded_core_exponent hν0 hν1 hδ)

end
end Record12518109Gain
