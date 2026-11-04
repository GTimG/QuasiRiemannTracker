import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.ExtendedRowCountGeometry

/- A numerical envelope and its exact connection to the rational certificate.
   An analytic row-count theorem must still supply these exponent bounds. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.RowCountExtension
noncomputable section

def commonDenominator (c d y : ℝ) : ℝ :=
  (5/6-d)*(5/2-c+(1+2*c)*y)+d*(1-c/2+2*y+2*c*y^2)
def adaptiveSplit (c d y : ℝ) : ℝ :=
  1+d*(1-c/2+2*y+2*c*y^2)/(2*commonDenominator c d y)
def rowEnvelope (c d y : ℝ) : ℝ :=
  1-d+(5/6-d)*d*(1-c/2+2*y+2*c*y^2)/(2*commonDenominator c d y)

theorem adaptive_split_range (c d y : ℝ)
    (hc : 4/9 ≤ c) (hcu : c ≤ 6/13) (hd : 0 ≤ d) (hdu : d ≤ 5/6)
    (hy : 0 ≤ y) (hyu : y ≤ 1/2) :
    1 ≤ adaptiveSplit c d y ∧ adaptiveSplit c d y ≤ 3/2 := by
  have hJ : 0 < commonDenominator c d y :=
    lt_of_lt_of_le (by norm_num) (generalized_J_lower c d y hc hcu hd hdu hy hyu)
  have hP : 0 ≤ 1-c/2+2*y+2*c*y^2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ c) (sq_nonneg y)]
  have hD : 0 ≤ 5/2-c+(1+2*c)*y := by
    have hh := denominator_lower hc hcu (by linarith : 0 ≤ 1/2-y) (by linarith : 1/2-y ≤ 1/2)
    rw [(source_coordinate_identities c y).1] at hh
    linarith
  have hh := mul_nonneg (by linarith : 0 ≤ 5/6-d) hD
  unfold adaptiveSplit
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hd hP) (by positivity))
  · have hf : d*(1-c/2+2*y+2*c*y^2)/(2*commonDenominator c d y) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      unfold commonDenominator
      nlinarith
    linarith

theorem short_at_adaptive_split (c d y : ℝ)
    (hD : 5/2-c+(1+2*c)*y ≠ 0) (hJ : commonDenominator c d y ≠ 0) :
    shortExponent c d (1/2-y) (adaptiveSplit c d y) = rowEnvelope c d y := by
  unfold shortExponent adaptiveSplit rowEnvelope
  rw [(source_coordinate_identities c y).1, (source_coordinate_identities c y).2]
  have generic (D P J d : ℝ) (hDn : D ≠ 0) (hJn : J ≠ 0)
      (he : J = (5/6-d)*D+d*P) :
      1-d+d*P/D*(3/2-(1+d*P/(2*J))) = 1-d+(5/6-d)*d*P/(2*J) := by
    field_simp
    rw [he]
    ring
  exact generic _ _ _ d hD hJ rfl

theorem long_at_adaptive_split (c d y : ℝ) :
    1-d+(5/6-d)*(adaptiveSplit c d y-1) = rowEnvelope c d y := by
  unfold adaptiveSplit rowEnvelope
  ring

theorem rational_envelope_identity (d y : ℝ) : rowEnvelope cRat d y = countR d y := by
  rfl

theorem rational_short_matches_certificate (d y : ℝ)
    (hd : 0 ≤ d) (hdu : d ≤ 5/6) (hy : 0 ≤ y) (hyu : y ≤ 1/2) :
    shortExponent cRat d (1/2-y) (adaptiveSplit cRat d y) = countR d y := by
  have hc : (4/9 : ℝ) ≤ cRat := by norm_num [cRat, kappaRat]
  have hcu : cRat ≤ (6/13 : ℝ) := by norm_num [cRat, kappaRat]
  have hD := denominator_lower hc hcu (by linarith : 0 ≤ 1/2-y) (by linarith : 1/2-y ≤ 1/2)
  rw [(source_coordinate_identities cRat y).1] at hD
  have hJ := generalized_J_lower cRat d y hc hcu hd hdu hy hyu
  rw [← rational_envelope_identity]
  exact short_at_adaptive_split cRat d y (by linarith) (by unfold commonDenominator; linarith)

/- This permits the small length error in the analytic detector. The upper
   bound Delta <= 1 avoids assuming the old Delta <= 1/8 cutoff. -/
theorem capacity_loss_with_length_error (q m κ₀ κ Δ γ : ℝ)
    (hqu : q ≤ 1/2) (hm : 1/3-γ ≤ m) (hmu : m ≤ 1/2)
    (hk₀ : 13/18 ≤ κ₀) (hk : κ = κ₀+2*Δ)
    (hΔ : 0 ≤ Δ) (hΔu : Δ ≤ 1) (hγ : 0 ≤ γ) :
    q*(1-2*m)/3*(1/κ₀-1/κ) ≤ Δ/4+2*γ := by
  have hk0p : 0 < κ₀ := by linarith
  have hkfloor : 13/18 ≤ κ := by linarith
  have hkp : 0 < κ := by linarith
  have hden : (4/3 : ℝ) ≤ 3*κ₀*κ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hk₀) (sub_nonneg.mpr hkfloor)]
  have hn := mul_le_mul hqu (show 1-2*m ≤ 1/3+2*γ by linarith)
    (by linarith : 0 ≤ 1-2*m) (by norm_num : (0:ℝ) ≤ 1/2)
  have hnum := mul_le_mul_of_nonneg_right hn (show 0 ≤ 2*Δ by positivity)
  have hg := mul_le_mul_of_nonneg_left hΔu hγ
  have hbase := mul_le_mul_of_nonneg_right hden (show 0 ≤ Δ/4+2*γ by positivity)
  have he : q*(1-2*m)/3*(1/κ₀-1/κ) =
      2*q*(1-2*m)*Δ/(3*κ₀*κ) := by
    field_simp
    nlinarith
  rw [he]
  apply (div_le_iff₀ (by positivity : 0 < 3*κ₀*κ)).mpr
  nlinarith

#print axioms rational_short_matches_certificate
#print axioms capacity_loss_with_length_error
end
end BelowSevenEighthsTight.RowCountExtension
