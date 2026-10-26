/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.CapGeometry

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section

/-- A nonnegative perturbation pays the zero, affine and upper-cap branches
simultaneously; no branch is discarded. -/
theorem three_branch_perturb (x y u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    max 0 (max (x+u) (y+v)) ≤ max 0 (max x y)+max u v := by
  apply max_le
  · exact add_nonneg (le_max_left _ _) (hu.trans (le_max_left _ _))
  · apply max_le
    · exact add_le_add ((le_max_left x y).trans (le_max_right 0 _)) (le_max_left u v)
    · exact add_le_add ((le_max_right x y).trans (le_max_right 0 _)) (le_max_right u v)

/-- C28 G13 with the actual clipping/annular loss, radial rounding and whole-slot
mesh. At zero loss it recovers the original three-branch inequality exactly. -/
theorem raw_low_three_branches_with_loss
    (a g q B lam h F t b c delta f B12 D loss rho mesh : ℝ)
    (hq : 0 ≤ q) (hB0 : 0 ≤ B) (hB : B ≤ 1) (hlam : 1 < lam)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (hdc : delta ≤ c)
    (hB12 : 0 ≤ B12) (hdB : delta ≤ B12) (hD : 0 ≤ D) (hf : 0 ≤ f)
    (hh : 0 ≤ h) (hqh : q*h ≤ 1)
    (hgap : g = a-q*(b+(t-B*F)/lam))
    (hcap : (B*F-t)/lam ≤ h*F) (hloss : 0 ≤ loss) (hrho : 0 ≤ rho) :
    -a-B12-D + q*(max 0 (max
      (b-f-(B*(F-delta-rho)-(t-c+f+loss))/lam)
      (b-f-h*(F-delta-rho)))+mesh) ≤
      -min a g+q*(max ((B*rho+loss)/lam) (h*rho)+mesh) := by
  have hlam0 : 0 < lam := by linarith only [hlam]
  have ha := raw_low_three_branches a g q B lam h F t b c delta f B12 D
    hq hB hlam hc hdelta hdc hB12 hdB hD hf hh hqh hgap hcap
  have hp := three_branch_perturb
    (b-f-(B*(F-delta)-(t-c+f))/lam) (b-f-h*(F-delta))
    ((B*rho+loss)/lam) (h*rho)
    (div_nonneg (add_nonneg (mul_nonneg hB0 hrho) hloss) hlam0.le) (mul_nonneg hh hrho)
  have e₁ : b-f-(B*(F-delta-rho)-(t-c+f+loss))/lam =
      (b-f-(B*(F-delta)-(t-c+f))/lam)+(B*rho+loss)/lam := by ring
  have e₂ : b-f-h*(F-delta-rho) = (b-f-h*(F-delta))+h*rho := by ring
  rw [e₁,e₂]
  have hm := mul_le_mul_of_nonneg_left hp hq
  linarith only [ha,hm]

/-- Any actual whole-slot removal bounded by the supported common cap has the
same G13 payment, including all finite support and rounding costs. -/
theorem actual_erasure_three_branch_payment
    (a g q B lam h F t b c delta f B12 D loss rho mesh erased : ℝ)
    (hq : 0 ≤ q) (hB0 : 0 ≤ B) (hB : B ≤ 1) (hlam : 1 < lam)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (hdc : delta ≤ c)
    (hB12 : 0 ≤ B12) (hdB : delta ≤ B12) (hD : 0 ≤ D) (hf : 0 ≤ f)
    (hh : 0 ≤ h) (hqh : q*h ≤ 1)
    (hgap : g = a-q*(b+(t-B*F)/lam))
    (hcap : (B*F-t)/lam ≤ h*F) (hloss : 0 ≤ loss) (hrho : 0 ≤ rho)
    (herased : erased ≤ max 0 (max
      (b-f-(B*(F-delta-rho)-(t-c+f+loss))/lam)
      (b-f-h*(F-delta-rho)))+mesh) :
    -a-B12-D+q*erased ≤ -min a g+q*(max ((B*rho+loss)/lam) (h*rho)+mesh) := by
  have he := mul_le_mul_of_nonneg_left herased hq
  have hp := raw_low_three_branches_with_loss a g q B lam h F t b c delta f B12 D loss rho mesh
    hq hB0 hB hlam hc hdelta hdc hB12 hdB hD hf hh hqh hgap hcap hloss hrho
  linarith only [he,hp]

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.raw_low_three_branches_with_loss
#print axioms QRH.Record1252270103Low.actual_erasure_three_branch_payment
