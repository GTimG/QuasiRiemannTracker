import Submissions.xenoproof_family003.OAI.BelowSevenEighthsTight.RationalCertificate

set_option autoImplicit false
namespace BelowSevenEighthsTight
noncomputable section

def lowPlaneOne (M ell : ℝ) : ℝ := 5/6-ell/6+M/12
def lowPlaneThree (M ell : ℝ) : ℝ := 1/3+ell/3+7*M/12
def highContactPlane (d M ell : ℝ) : ℝ := 1+d-(1+d)*M/2+d*ell
def contactBoundary (d : ℝ) : ℝ := (7+18*d)/(9+18*d)

theorem dual_identity (d M ell : ℝ) :
    (4+18*d)*lowPlaneOne M ell+2*lowPlaneThree M ell+
      3*highContactPlane d M ell = 7+18*d := by
  unfold lowPlaneOne lowPlaneThree highContactPlane
  ring

/- This is a theorem about the three stated exponent bounds. No lower bound
   on an actual L-function or operator norm is asserted. -/
theorem free_geometry_obstruction (d M ell : ℝ) (hd : 0 ≤ d) :
    contactBoundary d ≤
      max (lowPlaneOne M ell) (max (lowPlaneThree M ell) (highContactPlane d M ell)) := by
  let U := max (lowPlaneOne M ell) (max (lowPlaneThree M ell) (highContactPlane d M ell))
  have h1 : lowPlaneOne M ell ≤ U := le_max_left _ _
  have h3 : lowPlaneThree M ell ≤ U := (le_max_left _ _).trans (le_max_right _ _)
  have hh : highContactPlane d M ell ≤ U := (le_max_right _ _).trans (le_max_right _ _)
  have hw : 0 ≤ 4+18*d := by linarith
  have h := mul_le_mul_of_nonneg_left h1 hw
  have hi := dual_identity d M ell
  change (7+18*d)/(9+18*d) ≤ U
  apply (div_le_iff₀ (by linarith : 0 < 9+18*d)).mpr
  nlinarith

theorem contactBoundary_strictMono (d t : ℝ) (hd : 0 ≤ d) (ht : d < t) :
    contactBoundary d < contactBoundary t := by
  unfold contactBoundary
  apply (div_lt_div_iff₀ (by linarith : 0 < 9+18*d)
    (by linarith : 0 < 9+18*t)).mpr
  nlinarith

#print axioms free_geometry_obstruction
end
end BelowSevenEighthsTight
