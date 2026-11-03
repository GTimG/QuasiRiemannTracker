import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.CubicCertificate
import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.GeometryObstruction

/- This connects the limiting polynomial to the retained physical exponent.
   It proves an exponent inequality, not an analytic moment or probe theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 0
namespace BelowSevenEighthsTight
noncomputable section
def sigmaOptimal (r : ℝ) : ℝ := (103/146 : ℝ) + (153/292 : ℝ)*r + (-33/146 : ℝ)*r^2
def kappaOptimal (r : ℝ) : ℝ := (30/73 : ℝ) + (153/146 : ℝ)*r + (-33/73 : ℝ)*r^2
def ellOptimal (r : ℝ) : ℝ := (185/219 : ℝ) + (-153/73 : ℝ)*r + (66/73 : ℝ)*r^2
def bOptimal (r : ℝ) : ℝ := (-64066814/17945079 : ℝ) + (70596975/5981693 : ℝ)*r + (-35358510/5981693 : ℝ)*r^2
def cOptimal (r : ℝ) : ℝ := (543/335 : ℝ) + (-249/67 : ℝ)*r + (594/335 : ℝ)*r^2
def hOptimal (r : ℝ) : ℝ := (1+3*ellOptimal r+bOptimal r)/2
def lyOptimal (r : ℝ) : ℝ := (1-ellOptimal r+bOptimal r)/2
def c0Optimal (r : ℝ) : ℝ := -1/4+5*ellOptimal r/4+bOptimal r/6
def DOptimal (r y : ℝ) : ℝ := 5/2-cOptimal r+(1+2*cOptimal r)*y
def POptimal (r y : ℝ) : ℝ := 1-cOptimal r/2+2*y+2*cOptimal r*y^2
def JOptimal (r d y : ℝ) : ℝ := (5/6-d)*DOptimal r y+d*POptimal r y
def ROptimal (r d y : ℝ) : ℝ := 1-d+(5/6-d)*d*POptimal r y/(2*JOptimal r d y)
def EOptimal (r d y : ℝ) : ℝ :=
  c0Optimal r-(bOptimal r/2+ellOptimal r*y)*d+
    hOptimal r*(5/6-d)*d*POptimal r y/(2*JOptimal r d y)

private theorem parameter_nonneg (A B C r : ℝ)
    (hr : rootLower ≤ r) (hru : r ≤ rootUpper)
    (h0 : 0 ≤ A+B*rootLower+C*rootLower^2)
    (h1 : 0 ≤ A+B*(rootLower+rootUpper)/2+C*rootLower*rootUpper)
    (h2 : 0 ≤ A+B*rootUpper+C*rootUpper^2) : 0 ≤ A+B*r+C*r^2 := by
  have hl := sub_nonneg.mpr hr
  have hu := sub_nonneg.mpr hru
  have he : (rootUpper-rootLower)^2*(A+B*r+C*r^2) =
      (A+B*rootLower+C*rootLower^2)*(rootUpper-r)^2 +
      2*(A+B*(rootLower+rootUpper)/2+C*rootLower*rootUpper)*
        (r-rootLower)*(rootUpper-r) +
      (A+B*rootUpper+C*rootUpper^2)*(r-rootLower)^2 := by ring
  have hmul : 0 ≤ (rootUpper-rootLower)^2*(A+B*r+C*r^2) := by
    rw [he]
    positivity
  exact nonneg_of_mul_nonneg_right hmul (sq_pos_of_pos (sub_pos.mpr root_interval_signs.1))

private theorem c_nonneg (r : ℝ) (hl : rootLower ≤ r) (hu : r ≤ rootUpper) : 0 ≤ cOptimal r := by
  convert parameter_nonneg (543/335 : ℝ) (-249/67 : ℝ) (594/335 : ℝ) r hl hu
    (by norm_num [rootLower, rootUpper]) (by norm_num [rootLower, rootUpper])
    (by norm_num [rootLower, rootUpper]) using 1 <;> unfold cOptimal <;> ring

private theorem c_le_one (r : ℝ) (hl : rootLower ≤ r) (hu : r ≤ rootUpper) : 0 ≤ 1-cOptimal r := by
  convert parameter_nonneg (-208/335 : ℝ) (249/67 : ℝ) (-594/335 : ℝ) r hl hu
    (by norm_num [rootLower, rootUpper]) (by norm_num [rootLower, rootUpper])
    (by norm_num [rootLower, rootUpper]) using 1 <;> unfold cOptimal <;> ring

theorem sigma_parameter (r : ℝ) (hr : deltaPolynomial r = 0) :
    sigmaOptimal r*(9+18*r) = 7 + 18*r := by
  unfold sigmaOptimal
  unfold deltaPolynomial at hr
  linear_combination ((-1/292 : ℝ))*hr

theorem ell_parameter (r : ℝ) (hr : deltaPolynomial r = 0) :
    ellOptimal r*(9+18*r) = 5 + -6*r := by
  unfold ellOptimal
  unfold deltaPolynomial at hr
  linear_combination ((1/73 : ℝ))*hr

theorem reciprocal_capacity_parameter (r : ℝ) (hr : deltaPolynomial r = 0) :
    cOptimal r*(3*kappaOptimal r) = 1 := by
  unfold cOptimal kappaOptimal
  unfold deltaPolynomial at hr
  linear_combination ((257/48910 : ℝ) + (-99/48910 : ℝ)*r)*hr

theorem limiting_numerator_identity (r d y : ℝ) (hr : deltaPolynomial r = 0) :
    optimalPolynomial r d y =
      JOptimal r d y*(-2*c0Optimal r+(bOptimal r+2*ellOptimal r*y)*d)-
      hOptimal r*(5/6-d)*d*POptimal r y := by
  unfold optimalPolynomial JOptimal DOptimal POptimal c0Optimal hOptimal
    bOptimal ellOptimal cOptimal
  unfold deltaPolynomial at hr
  linear_combination ((74626205/43283530548 : ℝ) + (-74626205/21641765274 : ℝ)*y + (197605277/14427843516 : ℝ)*d + (-126761771/3606960879 : ℝ)*d*y + (55918265/3606960879 : ℝ)*d*y^2 + (-91902343/12023202930 : ℝ)*d^2 + (262315187/6011601465 : ℝ)*d^2*y + (-382943362/6011601465 : ℝ)*d^2*y^2 + (1028/73365 : ℝ)*d^2*y^3 + (-1734095/4809281172 : ℝ)*r + (1734095/2404640586 : ℝ)*r*y + (-9844835/1603093724 : ℝ)*r*d + (6447617/400773431 : ℝ)*r*d*y + (-3050399/400773431 : ℝ)*r*d*y^2 + (12895707/4007734310 : ℝ)*r*d^2 + (-38062563/2003867155 : ℝ)*r*d^2*y + (55741818/2003867155 : ℝ)*r*d^2*y^2 + (-132/24455 : ℝ)*r*d^2*y^3)*hr

theorem capacity_self_consistency (r : ℝ) :
    kappaOptimal r = 2*sigmaOptimal r-1 := by
  unfold kappaOptimal sigmaOptimal
  ring

theorem JOptimal_pos (r d y : ℝ) (hl : rootLower ≤ r) (hu : r ≤ rootUpper)
    (hd : 0 ≤ d) (hdu : d ≤ 5/6) (hy : 0 ≤ y) : 0 < JOptimal r d y := by
  have hc0 := c_nonneg r hl hu
  have hc1 := c_le_one r hl hu
  have hD : 1/2 ≤ DOptimal r y := by
    dsimp [DOptimal]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1+2*cOptimal r) hy]
  have hP : 1/2 ≤ POptimal r y := by
    dsimp [POptimal]
    nlinarith [mul_nonneg hc0 (sq_nonneg y)]
  have h1 := mul_nonneg (sub_nonneg.mpr hdu) (sub_nonneg.mpr hD)
  have h2 := mul_nonneg hd (sub_nonneg.mpr hP)
  dsimp [JOptimal]
  nlinarith

theorem critical_count_identity (r : ℝ) (hl : rootLower ≤ r) (hu : r ≤ rootUpper)
    (hr : deltaPolynomial r = 0) : ROptimal r r 0 = 2/3 := by
  have hrl := root_interval_signs.2.1
  have hru := root_interval_signs.2.2.1
  have hj := JOptimal_pos r r 0 hl hu (by linarith) (by linarith) (by norm_num)
  have hp : 2*JOptimal r r 0*(1-r-2/3)+(5/6-r)*r*POptimal r 0 = 0 := by
    unfold JOptimal DOptimal POptimal cOptimal
    unfold deltaPolynomial at hr
    linear_combination ((31/12060 : ℝ) + (-1/1340 : ℝ)*r)*hr
  have he : (5/6-r)*r*POptimal r 0/(2*JOptimal r r 0) = 2/3-(1-r) := by
    apply (div_eq_iff (ne_of_gt (by positivity : 0 < 2*JOptimal r r 0))).mpr
    nlinarith
  unfold ROptimal
  rw [he]
  ring


theorem limiting_endpoint_bound (d y : ℝ)
    (hd : 0 ≤ d) (hdu : d ≤ 5/6) (hy : 0 ≤ y) (hyu : y ≤ 1/2) :
    EOptimal deltaRoot d y ≤ 0 := by
  have hj := JOptimal_pos deltaRoot d y deltaRoot_spec.1.1 deltaRoot_spec.1.2 hd hdu hy
  have hn := limiting_polynomial_nonneg deltaRoot d y
    deltaRoot_spec.1.1 deltaRoot_spec.1.2 deltaRoot_spec.2 hd hdu hy hyu
  have he : optimalPolynomial deltaRoot d y =
      -2*JOptimal deltaRoot d y*EOptimal deltaRoot d y := by
    rw [limiting_numerator_identity deltaRoot d y deltaRoot_spec.2]
    unfold EOptimal
    field_simp
    <;> ring
  rw [he] at hn
  nlinarith

theorem limiting_physical_endpoint_identity (r d y : ℝ) :
    ((1+d)/2-sigmaOptimal r+hOptimal r*((17/50 : ℝ)-1/6)
      -(1+d)/2*lyOptimal r-ellOptimal r/2+d*(1/2-y)*ellOptimal r
      +hOptimal r*(ROptimal r d y+d/2-17/50)) = EOptimal r d y := by
  unfold EOptimal ROptimal c0Optimal hOptimal lyOptimal sigmaOptimal ellOptimal bOptimal
  ring

theorem sigmaOptimal_root : sigmaOptimal deltaRoot = sigmaRoot := by
  have he := sigma_parameter deltaRoot deltaRoot_spec.2
  have hl := deltaRoot_spec.1.1
  have hp := root_interval_signs.2.1
  have hd : 9+18*deltaRoot ≠ 0 := ne_of_gt (by linarith)
  unfold sigmaRoot
  apply (eq_div_iff hd).mpr
  simpa using he

theorem limiting_low_planes :
    lowPlaneOne (1-ellOptimal deltaRoot) (ellOptimal deltaRoot) = sigmaRoot ∧
    lowPlaneThree (1-ellOptimal deltaRoot) (ellOptimal deltaRoot) = sigmaRoot := by
  rw [← sigmaOptimal_root]
  constructor <;> simp only [lowPlaneOne, lowPlaneThree, ellOptimal, sigmaOptimal] <;> ring

theorem limiting_high_plane :
    highContactPlane deltaRoot (1-ellOptimal deltaRoot) (ellOptimal deltaRoot) = sigmaRoot := by
  rw [← sigmaOptimal_root]
  have hr := deltaRoot_spec.2
  unfold highContactPlane ellOptimal sigmaOptimal
  unfold deltaPolynomial at hr
  linear_combination ((1/876 : ℝ))*hr

theorem limiting_planes_attain_boundary :
    max (lowPlaneOne (1-ellOptimal deltaRoot) (ellOptimal deltaRoot))
      (max (lowPlaneThree (1-ellOptimal deltaRoot) (ellOptimal deltaRoot))
        (highContactPlane deltaRoot (1-ellOptimal deltaRoot) (ellOptimal deltaRoot))) = sigmaRoot := by
  rw [limiting_low_planes.1, limiting_low_planes.2, limiting_high_plane, max_self, max_self]

theorem limiting_free_geometry_obstruction (M ell : ℝ) :
    sigmaRoot ≤ max (lowPlaneOne M ell)
      (max (lowPlaneThree M ell) (highContactPlane deltaRoot M ell)) := by
  have hl := deltaRoot_spec.1.1
  have hp := root_interval_signs.2.1
  exact free_geometry_obstruction deltaRoot M ell (by linarith)

theorem limiting_bound_below_rational : sigmaRoot < sigmaRat ∧ sigmaRat < 7/8 := by
  have hu := sigmaRoot_enclosure.2
  constructor
  · norm_num [sigmaRat] at *
    linarith
  · norm_num [sigmaRat]

#print axioms limiting_endpoint_bound
#print axioms limiting_physical_endpoint_identity
#print axioms limiting_free_geometry_obstruction
end
end BelowSevenEighthsTight
