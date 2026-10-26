import Candidate.Target830.Marked.ParametersBridge

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.TargetHigh830

/-- The ordinary density increment helps; the literal large-root truncation
cost must still be paid as a positive raw fee. -/
theorem raw_gain_defect (G D root rho ordinaryLoss tailLoss : ℝ)
    (hD : 0≤D) (hroot : 0≤root) (hordinary : 0≤ordinaryLoss) (htail : 0≤tailLoss) :
    min G (D*root*(6*rho-1))-D*root*tailLoss ≤
      min G (D*root*(6*(rho+ordinaryLoss)-1-tailLoss)) := by
  have hn := mul_nonneg (mul_nonneg hD hroot) htail
  have ho := mul_nonneg (mul_nonneg hD hroot) hordinary
  apply le_min
  · linarith [min_le_left G (D*root*(6*rho-1))]
  · nlinarith [min_le_right G (D*root*(6*rho-1))]

/-- Complete exponent comparison after the actual detector/root/height
and normalization costs have been included in the single raw allowance. -/
theorem raw_exponent_payment (G D root rho ordinaryLoss tailLoss main extra fee : ℝ)
    (hD : 0≤D) (hroot : 0≤root) (hordinary : 0≤ordinaryLoss) (htail : 0≤tailLoss)
    (hfee : extra+D*root*tailLoss≤fee) :
    main+extra-min G (D*root*(6*(rho+ordinaryLoss)-1-tailLoss)) ≤
      main-min G (D*root*(6*rho-1))+fee := by
  have hg := raw_gain_defect G D root rho ordinaryLoss tailLoss hD hroot hordinary htail
  linarith

end OAI.SevenEighths.TargetHigh830
#print axioms OAI.SevenEighths.TargetHigh830.raw_gain_defect
#print axioms OAI.SevenEighths.TargetHigh830.raw_exponent_payment
