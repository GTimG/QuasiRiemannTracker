/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.RawCaps
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.Geometry

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section

/-- The original first-common geometry makes the affine retained cap positive. -/
theorem raw_affine_cap_positive (B lam F t b c delta f : ℝ)
    (hB : B ≤ 1) (hlam : 0 < lam) (hdelta : 0 ≤ delta)
    (hdc : delta ≤ c) (hf : f ≤ b) (hguard : 0 < B*F-t-b) :
    0 < (B*(F-delta)-(t-c+f))/lam := by
  apply div_pos _ hlam
  have hc : 0 ≤ c-B*delta := by nlinarith
  nlinarith

/-- The exact RAW ambient scale has a positive lower exponent before live rows. -/
theorem raw_radius_lower (F T delta d : ℝ)
    (hdelta : 2*delta ≤ d) (hd : d ≤ T) : F-T/2 ≤ F-delta := by linarith

/-- The first quotient cap and its common-width correction are identical. -/
theorem raw_cap_identity (B lam F t c delta f : ℝ) :
    (B*(F-delta)-(t-c+f))/lam =
      (B*F-t)/lam+(c-B*delta-f)/lam := by ring

/-- Erasure by the retained minimum preserves the zero-erasure floor and both
cap branches. The identity is valid even when one proposed deletion is negative. -/
theorem raw_erasure_cost (slots affine upper : ℝ) :
    max 0 (slots-min affine upper) = max 0 (max (slots-affine) (slots-upper)) := by
  rcases le_total affine upper with h | h
  · rw [min_eq_left h, max_eq_left (by linarith : slots-upper ≤ slots-affine)]
  · rw [min_eq_right h, max_eq_right (by linarith : slots-affine ≤ slots-upper)]

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.raw_affine_cap_positive
#print axioms QRH.Record1252270103Low.raw_radius_lower
#print axioms QRH.Record1252270103Low.raw_cap_identity
#print axioms QRH.Record1252270103Low.raw_erasure_cost
