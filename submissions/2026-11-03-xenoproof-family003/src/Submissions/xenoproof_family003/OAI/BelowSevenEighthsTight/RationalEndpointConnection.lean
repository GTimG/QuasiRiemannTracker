import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RationalRowCountConnection

/- Numerical transport from a row exponent to the retained physical exponent.
   The analytic statement producing that exponent is still a separate obligation. -/
set_option autoImplicit false
namespace BelowSevenEighthsTight.RowCountExtension
noncomputable section

def physicalExponent (δ q R β H : ℝ) : ℝ :=
  (1+δ)/2-β-(1+δ)/2*lyRat-ellRat/2+q*ellRat+H*(R+δ/2-1/6)

theorem rational_count_bounds (d y : ℝ)
    (hd : 0 ≤ d) (hdu : d ≤ 5/6) (hy : 0 ≤ y) (hyu : y ≤ 1/2) :
    1-d ≤ countR d y ∧ countR d y ≤ 1 := by
  have hJ := J_pos d y hd hdu hy
  have hP : 0 ≤ P y := by
    unfold P
    have hc : 0 < cRat ∧ cRat < 1 := by norm_num [cRat, kappaRat]
    nlinarith [mul_nonneg hc.1.le (sq_nonneg y)]
  have hysq : y^2 ≤ y/2 := by nlinarith
  have hDP : P y ≤ D y := by
    norm_num [P, D, cRat, kappaRat]
    nlinarith
  have hhdp := mul_le_mul_of_nonneg_left hDP (by linarith : 0 ≤ 5/6-d)
  have hdp := mul_nonneg hd hP
  have hcompare : (5/6-d)*P y ≤ 2*J d y := by
    unfold J
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hcompare hd
  have hterm : (5/6-d)*d*P y/(2*J d y) ≤ d := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  unfold countR
  constructor
  · exact le_add_of_nonneg_right (div_nonneg
      (mul_nonneg (mul_nonneg (by linarith) hd) hP) (by positivity))
  · linarith

theorem physical_exponent_transport_identity (d y q R β H : ℝ) :
    physicalExponent d q R β H = endpointE d y-(β-sigmaRat)+
      ellRat*(q-d*(1/2-y))+H*(R-countR d y)+
      (H-hRat)*(countR d y+d/2-1/6) := by
  unfold physicalExponent endpointE countR c0Rat hRat lyRat sigmaRat ellRat bRat
  ring

theorem rational_low_endpoint_with_errors (d y q R β H ζ loss : ℝ)
    (hd : 0 ≤ d) (hdu : d ≤ 5/6) (hy : 0 ≤ y) (hyu : y ≤ 1/2)
    (hβ : sigmaRat ≤ β) (hH : 0 ≤ H) (hHu : H ≤ 1)
    (hζ : 0 ≤ ζ) (hheight : H ≤ hRat+ζ)
    (hq : q ≤ d*(1/2-y)) (hR : R ≤ countR d y+(β-sigmaRat)/4+loss) :
    physicalExponent d q R β H ≤
      -1/1000000000000000-3*(β-sigmaRat)/4+H*loss+2*ζ := by
  have hE := rational_endpoint_bound d y hd hdu hy hyu
  have hb := rational_count_bounds d y hd hdu hy hyu
  have hK : 0 ≤ countR d y+d/2-1/6 := by linarith
  have hKu : countR d y+d/2-1/6 ≤ 2 := by linarith
  have hslot := mul_le_mul_of_nonneg_left hq
    (show 0 ≤ ellRat by norm_num [ellRat])
  have hrow := mul_le_mul_of_nonneg_left hR hH
  have hh := mul_le_mul_of_nonneg_right (show H-hRat ≤ ζ by linarith) hK
  have hh' := mul_le_mul_of_nonneg_left hKu hζ
  have hcap := mul_le_mul_of_nonneg_right hHu (show 0 ≤ β-sigmaRat by linarith)
  rw [physical_exponent_transport_identity d y q R β H]
  nlinarith

theorem rational_high_endpoint_with_errors (d q R β H ζ loss : ℝ)
    (hd : 5/6 ≤ d) (hdu : d ≤ 1) (hH : 0 ≤ H)
    (hζ : 0 ≤ ζ) (hheight : H ≤ hRat+ζ)
    (hq : q ≤ d/2) (hR : R ≤ 1-d+loss) :
    physicalExponent d q R β H ≤ -1/20-(β-sigmaRat)+H*loss+2*ζ := by
  have hK : 0 ≤ 5/6-d/2 := by linarith
  have hKu : 5/6-d/2 ≤ 2 := by linarith
  have hslot := mul_le_mul_of_nonneg_left hq
    (show 0 ≤ ellRat by norm_num [ellRat])
  have hrow := mul_le_mul_of_nonneg_left hR hH
  have hh := mul_le_mul_of_nonneg_right hheight hK
  have hh' := mul_le_mul_of_nonneg_left hKu hζ
  have hbase : c0Rat-bRat*d/2 ≤ -1/20 := by
    have hh := mul_le_mul_of_nonneg_left hd
      (show 0 ≤ bRat/2 by norm_num [bRat])
    norm_num [c0Rat, bRat, ellRat] at hh ⊢
    linarith
  have hid : (1+d)/2-sigmaRat-(1+d)/2*lyRat-ellRat/2+
      d/2*ellRat+hRat*(5/6-d/2) = c0Rat-bRat*d/2 := by
    unfold sigmaRat lyRat hRat c0Rat ellRat bRat
    ring
  unfold physicalExponent
  nlinarith

theorem rational_low_strict_margin (d y q R β H loss : ℝ)
    (hd : 0 ≤ d) (hdu : d ≤ 5/6) (hy : 0 ≤ y) (hyu : y ≤ 1/2)
    (hβ : sigmaRat ≤ β) (hH : 0 ≤ H)
    (hheight : H ≤ hRat+1/8000000000000000)
    (hloss : 0 ≤ loss) (hlossu : loss ≤ 1/8000000000000000)
    (hq : q ≤ d*(1/2-y)) (hR : R ≤ countR d y+(β-sigmaRat)/4+loss) :
    physicalExponent d q R β H ≤ -5/8000000000000000-3*(β-sigmaRat)/4 := by
  have hHu : H ≤ 1 := hheight.trans (by norm_num [hRat, ellRat, bRat])
  have hh := rational_low_endpoint_with_errors d y q R β H (1/8000000000000000) loss
    hd hdu hy hyu hβ hH hHu (by norm_num) hheight hq hR
  have hl := mul_le_mul hHu hlossu hloss (by norm_num : (0:ℝ) ≤ 1)
  linarith

#print axioms rational_low_endpoint_with_errors
#print axioms rational_high_endpoint_with_errors
#print axioms rational_low_strict_margin
end
end BelowSevenEighthsTight.RowCountExtension
