/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.BernsteinBox
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.HighCertificate
namespace Qrh.JointDetector.RepeatedMarks.HighTemplates
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 60000
open scoped BigOperators
open BernsteinBox

def rayCapD (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (5/2:ℝ) + (-5/12:ℝ)*z*a1 + (-1:ℝ)*nu + (-1/2:ℝ)*nu*z*a1

def rayCapK (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (5/3:ℝ)*nu + (5/6:ℝ)*nu*z*c*a1 + (-5/12:ℝ)*nu*z^2*c*a1^2 + (-1:ℝ)*nu^2*z*a1 + (-1:ℝ)*nu^2*z*c*a1 + (1/2:ℝ)*nu^2*z^2*c*a1^2

def rayCapDz (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (-5/12:ℝ)*a1 + (-1/2:ℝ)*nu*a1

def rayCapKz (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (5/6:ℝ)*nu*c*a1 + (-5/6:ℝ)*nu*z*c*a1^2 + (-1:ℝ)*nu^2*a1 + (-1:ℝ)*nu^2*c*a1 + (1:ℝ)*nu^2*z*c*a1^2

def rayCapAmp (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (-25/36:ℝ)*a1 + (25/4:ℝ)*a1*s + (-25/12:ℝ)*c*a1 + (-25/12:ℝ)*z*a1^2*s + (25/12:ℝ)*z*c*a1^2 + (25/144:ℝ)*z^2*a1^3*s + (-25/144:ℝ)*z^2*c*a1^3 + (5/3:ℝ)*nu*a1 + (-5:ℝ)*nu*a1*s + (10/3:ℝ)*nu*c*a1 + (-5/3:ℝ)*nu*z*a1^2*s + (-10/3:ℝ)*nu*z*c*a1^2 + (5/12:ℝ)*nu*z^2*a1^3*s + (-1:ℝ)*nu^2*a1 + (1:ℝ)*nu^2*a1*s + (-1:ℝ)*nu^2*c*a1 + (1:ℝ)*nu^2*z*a1^2*s + (1:ℝ)*nu^2*z*c*a1^2 + (1/4:ℝ)*nu^2*z^2*a1^3*s + (1/4:ℝ)*nu^2*z^2*c*a1^3

def rayCapPower (B L c a0 a1 s : ℝ) (i : Fin 3) (j : Fin 5) : ℝ :=
  match i.val,j.val with

  | 0,0 => (-25/36:ℝ)*a1 + (25/4:ℝ)*a1*s + (-25/12:ℝ)*c*a1

  | 0,1 => (-25/12:ℝ)*a1^2*s + (25/12:ℝ)*c*a1^2

  | 0,2 => (25/144:ℝ)*a1^3*s + (-25/144:ℝ)*c*a1^3

  | 1,0 => (5/3:ℝ)*a1 + (-5:ℝ)*a1*s + (10/3:ℝ)*c*a1

  | 1,1 => (-5/3:ℝ)*a1^2*s + (-10/3:ℝ)*c*a1^2

  | 1,2 => (5/12:ℝ)*a1^3*s

  | 2,0 => (-1:ℝ)*a1 + (1:ℝ)*a1*s + (-1:ℝ)*c*a1

  | 2,1 => (1:ℝ)*a1^2*s + (1:ℝ)*c*a1^2

  | 2,2 => (1/4:ℝ)*a1^3*s + (1/4:ℝ)*c*a1^3

  | _,_ => 0

theorem rayCap_power (B L c a0 a1 s : ℝ) (nu z : ℝ) :
    powerEval (rayCapPower B L c a0 a1 s) nu z = rayCapAmp B L c a0 a1 s nu z := by
  norm_num [powerEval,rayCapPower,rayCapAmp,Fin.sum_univ_succ]
  ring

theorem rayCap_amplitude_identity (B L c a0 a1 s : ℝ) (nu z : ℝ) :
    nu*rayCapAmp B L c a0 a1 s nu z =
      rayCapK B L c a0 a1 s nu z*rayCapDz B L c a0 a1 s nu z-
      rayCapKz B L c a0 a1 s nu z*rayCapD B L c a0 a1 s nu z+
      (a1*nu)*s*(rayCapD B L c a0 a1 s nu z)^2 := by
  unfold rayCapAmp rayCapK rayCapD rayCapDz rayCapKz
  ring

theorem rayCap_nonneg (B L c a0 a1 s : ℝ) (lo hi nu z : ℝ) (hlo : lo < hi)
    (hnu : nu ∈ Set.Icc lo hi) (hz : z ∈ Set.Icc (0:ℝ) 1)
    (hc : ∀ i j, 0 ≤ coefficients (rayCapPower B L c a0 a1 s) lo hi i j) :
    0 ≤ rayCapAmp B L c a0 a1 s nu z := by
  let x := (nu-lo)/(hi-lo)
  have hx : x ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hnu.1]) (by linarith)
    · exact (div_le_one (by linarith : 0 < hi-lo)).2 (by linarith [hnu.2])
  have he : lo+(hi-lo)*x=nu := by dsimp [x]; field_simp [(sub_pos.mpr hlo).ne']; ring
  have hp := bernEval_nonneg hc hx hz
  rw [← reconstruct24,he,rayCap_power] at hp
  exact hp

def rayBudgetD (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (5/2:ℝ) + (-5/12:ℝ)*z*a1 + (-5/3:ℝ)*z*(1/L)*a1 + (-1:ℝ)*nu + (-1/2:ℝ)*nu*z*a1 + (1:ℝ)*nu*z^2*(1/L)*a1^2

def rayBudgetK (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (5/3:ℝ)*nu + (-5/3:ℝ)*nu*z*(1/L)*a1 + (5/6:ℝ)*nu*z*B*(1/L)*a1 + (-5/12:ℝ)*nu*z^2*B*(1/L)*a1^2 + (-1:ℝ)*nu^2*z*a1 + (-1:ℝ)*nu^2*z*B*(1/L)*a1 + (1:ℝ)*nu^2*z^2*(1/L)*a1^2 + (1/2:ℝ)*nu^2*z^2*B*(1/L)*a1^2

def rayBudgetDz (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (-5/12:ℝ)*a1 + (-5/3:ℝ)*(1/L)*a1 + (-1/2:ℝ)*nu*a1 + (2:ℝ)*nu*z*(1/L)*a1^2

def rayBudgetKz (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (-5/3:ℝ)*nu*(1/L)*a1 + (5/6:ℝ)*nu*B*(1/L)*a1 + (-5/6:ℝ)*nu*z*B*(1/L)*a1^2 + (-1:ℝ)*nu^2*a1 + (-1:ℝ)*nu^2*B*(1/L)*a1 + (2:ℝ)*nu^2*z*(1/L)*a1^2 + (1:ℝ)*nu^2*z*B*(1/L)*a1^2

def rayBudgetAmp (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (-25/36:ℝ)*a1 + (25/4:ℝ)*a1*s + (25/18:ℝ)*(1/L)*a1 + (-25/12:ℝ)*B*(1/L)*a1 + (-25/12:ℝ)*z*a1^2*s + (-25/3:ℝ)*z*(1/L)*a1^2*s + (25/12:ℝ)*z*B*(1/L)*a1^2 + (25/144:ℝ)*z^2*a1^3*s + (25/18:ℝ)*z^2*(1/L)*a1^3*s + (25/9:ℝ)*z^2*(1/L)^2*a1^3*s + (-25/144:ℝ)*z^2*B*(1/L)*a1^3 + (-25/36:ℝ)*z^2*B*(1/L)^2*a1^3 + (5/3:ℝ)*nu*a1 + (-5:ℝ)*nu*a1*s + (-5/3:ℝ)*nu*(1/L)*a1 + (10/3:ℝ)*nu*B*(1/L)*a1 + (-5/3:ℝ)*nu*z*a1^2*s + (-5/3:ℝ)*nu*z*(1/L)*a1^2 + (10/3:ℝ)*nu*z*(1/L)*a1^2*s + (-10/3:ℝ)*nu*z*B*(1/L)*a1^2 + (5/12:ℝ)*nu*z^2*a1^3*s + (5/12:ℝ)*nu*z^2*(1/L)*a1^3 + (20/3:ℝ)*nu*z^2*(1/L)*a1^3*s + (5/3:ℝ)*nu*z^2*B*(1/L)^2*a1^3 + (-5/6:ℝ)*nu*z^3*(1/L)*a1^4*s + (-10/3:ℝ)*nu*z^3*(1/L)^2*a1^4*s + (-1:ℝ)*nu^2*a1 + (1:ℝ)*nu^2*a1*s + (-1:ℝ)*nu^2*B*(1/L)*a1 + (1:ℝ)*nu^2*z*a1^2*s + (2:ℝ)*nu^2*z*(1/L)*a1^2 + (1:ℝ)*nu^2*z*B*(1/L)*a1^2 + (1/4:ℝ)*nu^2*z^2*a1^3*s + (-1/2:ℝ)*nu^2*z^2*(1/L)*a1^3 + (-2:ℝ)*nu^2*z^2*(1/L)*a1^3*s + (1/4:ℝ)*nu^2*z^2*B*(1/L)*a1^3 + (-1:ℝ)*nu^2*z^2*B*(1/L)^2*a1^3 + (-1:ℝ)*nu^2*z^3*(1/L)*a1^4*s + (1:ℝ)*nu^2*z^4*(1/L)^2*a1^5*s

def rayBudgetPower (B L c a0 a1 s : ℝ) (i : Fin 3) (j : Fin 5) : ℝ :=
  match i.val,j.val with

  | 0,0 => (-25/36:ℝ)*a1 + (25/4:ℝ)*a1*s + (25/18:ℝ)*(1/L)*a1 + (-25/12:ℝ)*B*(1/L)*a1

  | 0,1 => (-25/12:ℝ)*a1^2*s + (-25/3:ℝ)*(1/L)*a1^2*s + (25/12:ℝ)*B*(1/L)*a1^2

  | 0,2 => (25/144:ℝ)*a1^3*s + (25/18:ℝ)*(1/L)*a1^3*s + (25/9:ℝ)*(1/L)^2*a1^3*s + (-25/144:ℝ)*B*(1/L)*a1^3 + (-25/36:ℝ)*B*(1/L)^2*a1^3

  | 1,0 => (5/3:ℝ)*a1 + (-5:ℝ)*a1*s + (-5/3:ℝ)*(1/L)*a1 + (10/3:ℝ)*B*(1/L)*a1

  | 1,1 => (-5/3:ℝ)*a1^2*s + (-5/3:ℝ)*(1/L)*a1^2 + (10/3:ℝ)*(1/L)*a1^2*s + (-10/3:ℝ)*B*(1/L)*a1^2

  | 1,2 => (5/12:ℝ)*a1^3*s + (5/12:ℝ)*(1/L)*a1^3 + (20/3:ℝ)*(1/L)*a1^3*s + (5/3:ℝ)*B*(1/L)^2*a1^3

  | 1,3 => (-5/6:ℝ)*(1/L)*a1^4*s + (-10/3:ℝ)*(1/L)^2*a1^4*s

  | 2,0 => (-1:ℝ)*a1 + (1:ℝ)*a1*s + (-1:ℝ)*B*(1/L)*a1

  | 2,1 => (1:ℝ)*a1^2*s + (2:ℝ)*(1/L)*a1^2 + (1:ℝ)*B*(1/L)*a1^2

  | 2,2 => (1/4:ℝ)*a1^3*s + (-1/2:ℝ)*(1/L)*a1^3 + (-2:ℝ)*(1/L)*a1^3*s + (1/4:ℝ)*B*(1/L)*a1^3 + (-1:ℝ)*B*(1/L)^2*a1^3

  | 2,3 => (-1:ℝ)*(1/L)*a1^4*s

  | 2,4 => (1:ℝ)*(1/L)^2*a1^5*s

  | _,_ => 0

theorem rayBudget_power (B L c a0 a1 s : ℝ) (nu z : ℝ) :
    powerEval (rayBudgetPower B L c a0 a1 s) nu z = rayBudgetAmp B L c a0 a1 s nu z := by
  norm_num [powerEval,rayBudgetPower,rayBudgetAmp,Fin.sum_univ_succ]
  ring

theorem rayBudget_amplitude_identity (B L c a0 a1 s : ℝ) (nu z : ℝ) :
    nu*rayBudgetAmp B L c a0 a1 s nu z =
      rayBudgetK B L c a0 a1 s nu z*rayBudgetDz B L c a0 a1 s nu z-
      rayBudgetKz B L c a0 a1 s nu z*rayBudgetD B L c a0 a1 s nu z+
      (a1*nu)*s*(rayBudgetD B L c a0 a1 s nu z)^2 := by
  unfold rayBudgetAmp rayBudgetK rayBudgetD rayBudgetDz rayBudgetKz
  ring

theorem rayBudget_nonneg (B L c a0 a1 s : ℝ) (lo hi nu z : ℝ) (hlo : lo < hi)
    (hnu : nu ∈ Set.Icc lo hi) (hz : z ∈ Set.Icc (0:ℝ) 1)
    (hc : ∀ i j, 0 ≤ coefficients (rayBudgetPower B L c a0 a1 s) lo hi i j) :
    0 ≤ rayBudgetAmp B L c a0 a1 s nu z := by
  let x := (nu-lo)/(hi-lo)
  have hx : x ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hnu.1]) (by linarith)
    · exact (div_le_one (by linarith : 0 < hi-lo)).2 (by linarith [hnu.2])
  have he : lo+(hi-lo)*x=nu := by dsimp [x]; field_simp [(sub_pos.mpr hlo).ne']; ring
  have hp := bernEval_nonneg hc hx hz
  rw [← reconstruct24,he,rayBudget_power] at hp
  exact hp

def affineCapD (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (-5/12:ℝ)*z*a0 + (5/2:ℝ)*nu + (-5/12:ℝ)*nu*z*a1 + (-1/2:ℝ)*nu*z*a0 + (-1:ℝ)*nu^2 + (-1/2:ℝ)*nu^2*z*a1

def affineCapK (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (-5/12:ℝ)*z^2*c*a0^2 + (5/6:ℝ)*nu*z*c*a0 + (-5/6:ℝ)*nu*z^2*c*a0*a1 + (1/2:ℝ)*nu*z^2*c*a0^2 + (5/3:ℝ)*nu^2 + (-1:ℝ)*nu^2*z*a0 + (5/6:ℝ)*nu^2*z*c*a1 + (-1:ℝ)*nu^2*z*c*a0 + (-5/12:ℝ)*nu^2*z^2*c*a1^2 + (1:ℝ)*nu^2*z^2*c*a0*a1 + (-1:ℝ)*nu^3*z*a1 + (-1:ℝ)*nu^3*z*c*a1 + (1/2:ℝ)*nu^3*z^2*c*a1^2

def affineCapDz (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (-5/12:ℝ)*a0 + (-5/12:ℝ)*nu*a1 + (-1/2:ℝ)*nu*a0 + (-1/2:ℝ)*nu^2*a1

def affineCapKz (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (-5/6:ℝ)*z*c*a0^2 + (5/6:ℝ)*nu*c*a0 + (-5/3:ℝ)*nu*z*c*a0*a1 + (1:ℝ)*nu*z*c*a0^2 + (-1:ℝ)*nu^2*a0 + (5/6:ℝ)*nu^2*c*a1 + (-1:ℝ)*nu^2*c*a0 + (-5/6:ℝ)*nu^2*z*c*a1^2 + (2:ℝ)*nu^2*z*c*a0*a1 + (-1:ℝ)*nu^3*a1 + (-1:ℝ)*nu^3*c*a1 + (1:ℝ)*nu^3*z*c*a1^2

def affineCapAmp (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (25/144:ℝ)*z^2*a0^3*s + (-25/144:ℝ)*z^2*c*a0^3 + (-25/12:ℝ)*nu*z*a0^2*s + (25/12:ℝ)*nu*z*c*a0^2 + (25/48:ℝ)*nu*z^2*a0^2*a1*s + (5/12:ℝ)*nu*z^2*a0^3*s + (-25/48:ℝ)*nu*z^2*c*a0^2*a1 + (-25/36:ℝ)*nu^2*a0 + (25/4:ℝ)*nu^2*a0*s + (-25/12:ℝ)*nu^2*c*a0 + (-25/6:ℝ)*nu^2*z*a0*a1*s + (-5/3:ℝ)*nu^2*z*a0^2*s + (25/6:ℝ)*nu^2*z*c*a0*a1 + (-10/3:ℝ)*nu^2*z*c*a0^2 + (25/48:ℝ)*nu^2*z^2*a0*a1^2*s + (5/4:ℝ)*nu^2*z^2*a0^2*a1*s + (1/4:ℝ)*nu^2*z^2*a0^3*s + (-25/48:ℝ)*nu^2*z^2*c*a0*a1^2 + (1/4:ℝ)*nu^2*z^2*c*a0^3 + (-25/36:ℝ)*nu^3*a1 + (25/4:ℝ)*nu^3*a1*s + (5/3:ℝ)*nu^3*a0 + (-5:ℝ)*nu^3*a0*s + (-25/12:ℝ)*nu^3*c*a1 + (10/3:ℝ)*nu^3*c*a0 + (-25/12:ℝ)*nu^3*z*a1^2*s + (-10/3:ℝ)*nu^3*z*a0*a1*s + (1:ℝ)*nu^3*z*a0^2*s + (25/12:ℝ)*nu^3*z*c*a1^2 + (-20/3:ℝ)*nu^3*z*c*a0*a1 + (1:ℝ)*nu^3*z*c*a0^2 + (25/144:ℝ)*nu^3*z^2*a1^3*s + (5/4:ℝ)*nu^3*z^2*a0*a1^2*s + (3/4:ℝ)*nu^3*z^2*a0^2*a1*s + (-25/144:ℝ)*nu^3*z^2*c*a1^3 + (3/4:ℝ)*nu^3*z^2*c*a0^2*a1 + (5/3:ℝ)*nu^4*a1 + (-5:ℝ)*nu^4*a1*s + (-1:ℝ)*nu^4*a0 + (1:ℝ)*nu^4*a0*s + (10/3:ℝ)*nu^4*c*a1 + (-1:ℝ)*nu^4*c*a0 + (-5/3:ℝ)*nu^4*z*a1^2*s + (2:ℝ)*nu^4*z*a0*a1*s + (-10/3:ℝ)*nu^4*z*c*a1^2 + (2:ℝ)*nu^4*z*c*a0*a1 + (5/12:ℝ)*nu^4*z^2*a1^3*s + (3/4:ℝ)*nu^4*z^2*a0*a1^2*s + (3/4:ℝ)*nu^4*z^2*c*a0*a1^2 + (-1:ℝ)*nu^5*a1 + (1:ℝ)*nu^5*a1*s + (-1:ℝ)*nu^5*c*a1 + (1:ℝ)*nu^5*z*a1^2*s + (1:ℝ)*nu^5*z*c*a1^2 + (1/4:ℝ)*nu^5*z^2*a1^3*s + (1/4:ℝ)*nu^5*z^2*c*a1^3

def affineCapPower (B L c a0 a1 s : ℝ) (i : Fin 6) (j : Fin 5) : ℝ :=
  match i.val,j.val with

  | 0,2 => (25/144:ℝ)*a0^3*s + (-25/144:ℝ)*c*a0^3

  | 1,1 => (-25/12:ℝ)*a0^2*s + (25/12:ℝ)*c*a0^2

  | 1,2 => (25/48:ℝ)*a0^2*a1*s + (5/12:ℝ)*a0^3*s + (-25/48:ℝ)*c*a0^2*a1

  | 2,0 => (-25/36:ℝ)*a0 + (25/4:ℝ)*a0*s + (-25/12:ℝ)*c*a0

  | 2,1 => (-25/6:ℝ)*a0*a1*s + (-5/3:ℝ)*a0^2*s + (25/6:ℝ)*c*a0*a1 + (-10/3:ℝ)*c*a0^2

  | 2,2 => (25/48:ℝ)*a0*a1^2*s + (5/4:ℝ)*a0^2*a1*s + (1/4:ℝ)*a0^3*s + (-25/48:ℝ)*c*a0*a1^2 + (1/4:ℝ)*c*a0^3

  | 3,0 => (-25/36:ℝ)*a1 + (25/4:ℝ)*a1*s + (5/3:ℝ)*a0 + (-5:ℝ)*a0*s + (-25/12:ℝ)*c*a1 + (10/3:ℝ)*c*a0

  | 3,1 => (-25/12:ℝ)*a1^2*s + (-10/3:ℝ)*a0*a1*s + (1:ℝ)*a0^2*s + (25/12:ℝ)*c*a1^2 + (-20/3:ℝ)*c*a0*a1 + (1:ℝ)*c*a0^2

  | 3,2 => (25/144:ℝ)*a1^3*s + (5/4:ℝ)*a0*a1^2*s + (3/4:ℝ)*a0^2*a1*s + (-25/144:ℝ)*c*a1^3 + (3/4:ℝ)*c*a0^2*a1

  | 4,0 => (5/3:ℝ)*a1 + (-5:ℝ)*a1*s + (-1:ℝ)*a0 + (1:ℝ)*a0*s + (10/3:ℝ)*c*a1 + (-1:ℝ)*c*a0

  | 4,1 => (-5/3:ℝ)*a1^2*s + (2:ℝ)*a0*a1*s + (-10/3:ℝ)*c*a1^2 + (2:ℝ)*c*a0*a1

  | 4,2 => (5/12:ℝ)*a1^3*s + (3/4:ℝ)*a0*a1^2*s + (3/4:ℝ)*c*a0*a1^2

  | 5,0 => (-1:ℝ)*a1 + (1:ℝ)*a1*s + (-1:ℝ)*c*a1

  | 5,1 => (1:ℝ)*a1^2*s + (1:ℝ)*c*a1^2

  | 5,2 => (1/4:ℝ)*a1^3*s + (1/4:ℝ)*c*a1^3

  | _,_ => 0

theorem affineCap_power (B L c a0 a1 s : ℝ) (nu z : ℝ) :
    powerEval (affineCapPower B L c a0 a1 s) nu z = affineCapAmp B L c a0 a1 s nu z := by
  norm_num [powerEval,affineCapPower,affineCapAmp,Fin.sum_univ_succ]
  ring

theorem affineCap_amplitude_identity (B L c a0 a1 s : ℝ) (nu z : ℝ) :
    affineCapAmp B L c a0 a1 s nu z =
      affineCapK B L c a0 a1 s nu z*affineCapDz B L c a0 a1 s nu z-
      affineCapKz B L c a0 a1 s nu z*affineCapD B L c a0 a1 s nu z+
      (a0+a1*nu)*s*(affineCapD B L c a0 a1 s nu z)^2 := by
  unfold affineCapAmp affineCapK affineCapD affineCapDz affineCapKz
  ring

theorem affineCap_nonneg (B L c a0 a1 s : ℝ) (lo hi nu z : ℝ) (hlo : lo < hi)
    (hnu : nu ∈ Set.Icc lo hi) (hz : z ∈ Set.Icc (0:ℝ) 1)
    (hc : ∀ i j, 0 ≤ coefficients (affineCapPower B L c a0 a1 s) lo hi i j) :
    0 ≤ affineCapAmp B L c a0 a1 s nu z := by
  let x := (nu-lo)/(hi-lo)
  have hx : x ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hnu.1]) (by linarith)
    · exact (div_le_one (by linarith : 0 < hi-lo)).2 (by linarith [hnu.2])
  have he : lo+(hi-lo)*x=nu := by dsimp [x]; field_simp [(sub_pos.mpr hlo).ne']; ring
  have hp := bernEval_nonneg hc hx hz
  rw [← reconstruct54,he,affineCap_power] at hp
  exact hp

def affineBudgetD (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (-5/12:ℝ)*z*a0 + (-5/3:ℝ)*z*(1/L)*a0 + (1:ℝ)*z^2*(1/L)*a0^2 + (5/2:ℝ)*nu + (-5/12:ℝ)*nu*z*a1 + (-1/2:ℝ)*nu*z*a0 + (-5/3:ℝ)*nu*z*(1/L)*a1 + (2:ℝ)*nu*z^2*(1/L)*a0*a1 + (-1:ℝ)*nu^2 + (-1/2:ℝ)*nu^2*z*a1 + (1:ℝ)*nu^2*z^2*(1/L)*a1^2

def affineBudgetK (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (-5/12:ℝ)*z^2*B*(1/L)*a0^2 + (-5/3:ℝ)*nu*z*(1/L)*a0 + (5/6:ℝ)*nu*z*B*(1/L)*a0 + (1:ℝ)*nu*z^2*(1/L)*a0^2 + (-5/6:ℝ)*nu*z^2*B*(1/L)*a0*a1 + (1/2:ℝ)*nu*z^2*B*(1/L)*a0^2 + (5/3:ℝ)*nu^2 + (-1:ℝ)*nu^2*z*a0 + (-5/3:ℝ)*nu^2*z*(1/L)*a1 + (5/6:ℝ)*nu^2*z*B*(1/L)*a1 + (-1:ℝ)*nu^2*z*B*(1/L)*a0 + (2:ℝ)*nu^2*z^2*(1/L)*a0*a1 + (-5/12:ℝ)*nu^2*z^2*B*(1/L)*a1^2 + (1:ℝ)*nu^2*z^2*B*(1/L)*a0*a1 + (-1:ℝ)*nu^3*z*a1 + (-1:ℝ)*nu^3*z*B*(1/L)*a1 + (1:ℝ)*nu^3*z^2*(1/L)*a1^2 + (1/2:ℝ)*nu^3*z^2*B*(1/L)*a1^2

def affineBudgetDz (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (-5/12:ℝ)*a0 + (-5/3:ℝ)*(1/L)*a0 + (2:ℝ)*z*(1/L)*a0^2 + (-5/12:ℝ)*nu*a1 + (-1/2:ℝ)*nu*a0 + (-5/3:ℝ)*nu*(1/L)*a1 + (4:ℝ)*nu*z*(1/L)*a0*a1 + (-1/2:ℝ)*nu^2*a1 + (2:ℝ)*nu^2*z*(1/L)*a1^2

def affineBudgetKz (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (-5/6:ℝ)*z*B*(1/L)*a0^2 + (-5/3:ℝ)*nu*(1/L)*a0 + (5/6:ℝ)*nu*B*(1/L)*a0 + (2:ℝ)*nu*z*(1/L)*a0^2 + (-5/3:ℝ)*nu*z*B*(1/L)*a0*a1 + (1:ℝ)*nu*z*B*(1/L)*a0^2 + (-1:ℝ)*nu^2*a0 + (-5/3:ℝ)*nu^2*(1/L)*a1 + (5/6:ℝ)*nu^2*B*(1/L)*a1 + (-1:ℝ)*nu^2*B*(1/L)*a0 + (4:ℝ)*nu^2*z*(1/L)*a0*a1 + (-5/6:ℝ)*nu^2*z*B*(1/L)*a1^2 + (2:ℝ)*nu^2*z*B*(1/L)*a0*a1 + (-1:ℝ)*nu^3*a1 + (-1:ℝ)*nu^3*B*(1/L)*a1 + (2:ℝ)*nu^3*z*(1/L)*a1^2 + (1:ℝ)*nu^3*z*B*(1/L)*a1^2

def affineBudgetAmp (B L c a0 a1 s : ℝ) (nu z : ℝ) : ℝ := (25/144:ℝ)*z^2*a0^3*s + (25/18:ℝ)*z^2*(1/L)*a0^3*s + (25/9:ℝ)*z^2*(1/L)^2*a0^3*s + (-25/144:ℝ)*z^2*B*(1/L)*a0^3 + (-25/36:ℝ)*z^2*B*(1/L)^2*a0^3 + (-5/6:ℝ)*z^3*(1/L)*a0^4*s + (-10/3:ℝ)*z^3*(1/L)^2*a0^4*s + (1:ℝ)*z^4*(1/L)^2*a0^5*s + (-25/12:ℝ)*nu*z*a0^2*s + (-25/3:ℝ)*nu*z*(1/L)*a0^2*s + (25/12:ℝ)*nu*z*B*(1/L)*a0^2 + (25/48:ℝ)*nu*z^2*a0^2*a1*s + (5/12:ℝ)*nu*z^2*a0^3*s + (25/6:ℝ)*nu*z^2*(1/L)*a0^2*a1*s + (5/12:ℝ)*nu*z^2*(1/L)*a0^3 + (20/3:ℝ)*nu*z^2*(1/L)*a0^3*s + (25/3:ℝ)*nu*z^2*(1/L)^2*a0^2*a1*s + (-25/48:ℝ)*nu*z^2*B*(1/L)*a0^2*a1 + (-25/12:ℝ)*nu*z^2*B*(1/L)^2*a0^2*a1 + (5/3:ℝ)*nu*z^2*B*(1/L)^2*a0^3 + (-10/3:ℝ)*nu*z^3*(1/L)*a0^3*a1*s + (-1:ℝ)*nu*z^3*(1/L)*a0^4*s + (-40/3:ℝ)*nu*z^3*(1/L)^2*a0^3*a1*s + (5:ℝ)*nu*z^4*(1/L)^2*a0^4*a1*s + (-25/36:ℝ)*nu^2*a0 + (25/4:ℝ)*nu^2*a0*s + (25/18:ℝ)*nu^2*(1/L)*a0 + (-25/12:ℝ)*nu^2*B*(1/L)*a0 + (-25/6:ℝ)*nu^2*z*a0*a1*s + (-5/3:ℝ)*nu^2*z*a0^2*s + (-50/3:ℝ)*nu^2*z*(1/L)*a0*a1*s + (-5/3:ℝ)*nu^2*z*(1/L)*a0^2 + (10/3:ℝ)*nu^2*z*(1/L)*a0^2*s + (25/6:ℝ)*nu^2*z*B*(1/L)*a0*a1 + (-10/3:ℝ)*nu^2*z*B*(1/L)*a0^2 + (25/48:ℝ)*nu^2*z^2*a0*a1^2*s + (5/4:ℝ)*nu^2*z^2*a0^2*a1*s + (1/4:ℝ)*nu^2*z^2*a0^3*s + (25/6:ℝ)*nu^2*z^2*(1/L)*a0*a1^2*s + (5/4:ℝ)*nu^2*z^2*(1/L)*a0^2*a1 + (20:ℝ)*nu^2*z^2*(1/L)*a0^2*a1*s + (-1/2:ℝ)*nu^2*z^2*(1/L)*a0^3 + (-2:ℝ)*nu^2*z^2*(1/L)*a0^3*s + (25/3:ℝ)*nu^2*z^2*(1/L)^2*a0*a1^2*s + (-25/48:ℝ)*nu^2*z^2*B*(1/L)*a0*a1^2 + (1/4:ℝ)*nu^2*z^2*B*(1/L)*a0^3 + (-25/12:ℝ)*nu^2*z^2*B*(1/L)^2*a0*a1^2 + (5:ℝ)*nu^2*z^2*B*(1/L)^2*a0^2*a1 + (-1:ℝ)*nu^2*z^2*B*(1/L)^2*a0^3 + (-5:ℝ)*nu^2*z^3*(1/L)*a0^2*a1^2*s + (-4:ℝ)*nu^2*z^3*(1/L)*a0^3*a1*s + (-20:ℝ)*nu^2*z^3*(1/L)^2*a0^2*a1^2*s + (10:ℝ)*nu^2*z^4*(1/L)^2*a0^3*a1^2*s + (-25/36:ℝ)*nu^3*a1 + (25/4:ℝ)*nu^3*a1*s + (5/3:ℝ)*nu^3*a0 + (-5:ℝ)*nu^3*a0*s + (25/18:ℝ)*nu^3*(1/L)*a1 + (-5/3:ℝ)*nu^3*(1/L)*a0 + (-25/12:ℝ)*nu^3*B*(1/L)*a1 + (10/3:ℝ)*nu^3*B*(1/L)*a0 + (-25/12:ℝ)*nu^3*z*a1^2*s + (-10/3:ℝ)*nu^3*z*a0*a1*s + (1:ℝ)*nu^3*z*a0^2*s + (-25/3:ℝ)*nu^3*z*(1/L)*a1^2*s + (-10/3:ℝ)*nu^3*z*(1/L)*a0*a1 + (20/3:ℝ)*nu^3*z*(1/L)*a0*a1*s + (2:ℝ)*nu^3*z*(1/L)*a0^2 + (25/12:ℝ)*nu^3*z*B*(1/L)*a1^2 + (-20/3:ℝ)*nu^3*z*B*(1/L)*a0*a1 + (1:ℝ)*nu^3*z*B*(1/L)*a0^2 + (25/144:ℝ)*nu^3*z^2*a1^3*s + (5/4:ℝ)*nu^3*z^2*a0*a1^2*s + (3/4:ℝ)*nu^3*z^2*a0^2*a1*s + (25/18:ℝ)*nu^3*z^2*(1/L)*a1^3*s + (5/4:ℝ)*nu^3*z^2*(1/L)*a0*a1^2 + (20:ℝ)*nu^3*z^2*(1/L)*a0*a1^2*s + (-3/2:ℝ)*nu^3*z^2*(1/L)*a0^2*a1 + (-6:ℝ)*nu^3*z^2*(1/L)*a0^2*a1*s + (25/9:ℝ)*nu^3*z^2*(1/L)^2*a1^3*s + (-25/144:ℝ)*nu^3*z^2*B*(1/L)*a1^3 + (3/4:ℝ)*nu^3*z^2*B*(1/L)*a0^2*a1 + (-25/36:ℝ)*nu^3*z^2*B*(1/L)^2*a1^3 + (5:ℝ)*nu^3*z^2*B*(1/L)^2*a0*a1^2 + (-3:ℝ)*nu^3*z^2*B*(1/L)^2*a0^2*a1 + (-10/3:ℝ)*nu^3*z^3*(1/L)*a0*a1^3*s + (-6:ℝ)*nu^3*z^3*(1/L)*a0^2*a1^2*s + (-40/3:ℝ)*nu^3*z^3*(1/L)^2*a0*a1^3*s + (10:ℝ)*nu^3*z^4*(1/L)^2*a0^2*a1^3*s + (5/3:ℝ)*nu^4*a1 + (-5:ℝ)*nu^4*a1*s + (-1:ℝ)*nu^4*a0 + (1:ℝ)*nu^4*a0*s + (-5/3:ℝ)*nu^4*(1/L)*a1 + (10/3:ℝ)*nu^4*B*(1/L)*a1 + (-1:ℝ)*nu^4*B*(1/L)*a0 + (-5/3:ℝ)*nu^4*z*a1^2*s + (2:ℝ)*nu^4*z*a0*a1*s + (-5/3:ℝ)*nu^4*z*(1/L)*a1^2 + (10/3:ℝ)*nu^4*z*(1/L)*a1^2*s + (4:ℝ)*nu^4*z*(1/L)*a0*a1 + (-10/3:ℝ)*nu^4*z*B*(1/L)*a1^2 + (2:ℝ)*nu^4*z*B*(1/L)*a0*a1 + (5/12:ℝ)*nu^4*z^2*a1^3*s + (3/4:ℝ)*nu^4*z^2*a0*a1^2*s + (5/12:ℝ)*nu^4*z^2*(1/L)*a1^3 + (20/3:ℝ)*nu^4*z^2*(1/L)*a1^3*s + (-3/2:ℝ)*nu^4*z^2*(1/L)*a0*a1^2 + (-6:ℝ)*nu^4*z^2*(1/L)*a0*a1^2*s + (3/4:ℝ)*nu^4*z^2*B*(1/L)*a0*a1^2 + (5/3:ℝ)*nu^4*z^2*B*(1/L)^2*a1^3 + (-3:ℝ)*nu^4*z^2*B*(1/L)^2*a0*a1^2 + (-5/6:ℝ)*nu^4*z^3*(1/L)*a1^4*s + (-4:ℝ)*nu^4*z^3*(1/L)*a0*a1^3*s + (-10/3:ℝ)*nu^4*z^3*(1/L)^2*a1^4*s + (5:ℝ)*nu^4*z^4*(1/L)^2*a0*a1^4*s + (-1:ℝ)*nu^5*a1 + (1:ℝ)*nu^5*a1*s + (-1:ℝ)*nu^5*B*(1/L)*a1 + (1:ℝ)*nu^5*z*a1^2*s + (2:ℝ)*nu^5*z*(1/L)*a1^2 + (1:ℝ)*nu^5*z*B*(1/L)*a1^2 + (1/4:ℝ)*nu^5*z^2*a1^3*s + (-1/2:ℝ)*nu^5*z^2*(1/L)*a1^3 + (-2:ℝ)*nu^5*z^2*(1/L)*a1^3*s + (1/4:ℝ)*nu^5*z^2*B*(1/L)*a1^3 + (-1:ℝ)*nu^5*z^2*B*(1/L)^2*a1^3 + (-1:ℝ)*nu^5*z^3*(1/L)*a1^4*s + (1:ℝ)*nu^5*z^4*(1/L)^2*a1^5*s

def affineBudgetPower (B L c a0 a1 s : ℝ) (i : Fin 6) (j : Fin 5) : ℝ :=
  match i.val,j.val with

  | 0,2 => (25/144:ℝ)*a0^3*s + (25/18:ℝ)*(1/L)*a0^3*s + (25/9:ℝ)*(1/L)^2*a0^3*s + (-25/144:ℝ)*B*(1/L)*a0^3 + (-25/36:ℝ)*B*(1/L)^2*a0^3

  | 0,3 => (-5/6:ℝ)*(1/L)*a0^4*s + (-10/3:ℝ)*(1/L)^2*a0^4*s

  | 0,4 => (1:ℝ)*(1/L)^2*a0^5*s

  | 1,1 => (-25/12:ℝ)*a0^2*s + (-25/3:ℝ)*(1/L)*a0^2*s + (25/12:ℝ)*B*(1/L)*a0^2

  | 1,2 => (25/48:ℝ)*a0^2*a1*s + (5/12:ℝ)*a0^3*s + (25/6:ℝ)*(1/L)*a0^2*a1*s + (5/12:ℝ)*(1/L)*a0^3 + (20/3:ℝ)*(1/L)*a0^3*s + (25/3:ℝ)*(1/L)^2*a0^2*a1*s + (-25/48:ℝ)*B*(1/L)*a0^2*a1 + (-25/12:ℝ)*B*(1/L)^2*a0^2*a1 + (5/3:ℝ)*B*(1/L)^2*a0^3

  | 1,3 => (-10/3:ℝ)*(1/L)*a0^3*a1*s + (-1:ℝ)*(1/L)*a0^4*s + (-40/3:ℝ)*(1/L)^2*a0^3*a1*s

  | 1,4 => (5:ℝ)*(1/L)^2*a0^4*a1*s

  | 2,0 => (-25/36:ℝ)*a0 + (25/4:ℝ)*a0*s + (25/18:ℝ)*(1/L)*a0 + (-25/12:ℝ)*B*(1/L)*a0

  | 2,1 => (-25/6:ℝ)*a0*a1*s + (-5/3:ℝ)*a0^2*s + (-50/3:ℝ)*(1/L)*a0*a1*s + (-5/3:ℝ)*(1/L)*a0^2 + (10/3:ℝ)*(1/L)*a0^2*s + (25/6:ℝ)*B*(1/L)*a0*a1 + (-10/3:ℝ)*B*(1/L)*a0^2

  | 2,2 => (25/48:ℝ)*a0*a1^2*s + (5/4:ℝ)*a0^2*a1*s + (1/4:ℝ)*a0^3*s + (25/6:ℝ)*(1/L)*a0*a1^2*s + (5/4:ℝ)*(1/L)*a0^2*a1 + (20:ℝ)*(1/L)*a0^2*a1*s + (-1/2:ℝ)*(1/L)*a0^3 + (-2:ℝ)*(1/L)*a0^3*s + (25/3:ℝ)*(1/L)^2*a0*a1^2*s + (-25/48:ℝ)*B*(1/L)*a0*a1^2 + (1/4:ℝ)*B*(1/L)*a0^3 + (-25/12:ℝ)*B*(1/L)^2*a0*a1^2 + (5:ℝ)*B*(1/L)^2*a0^2*a1 + (-1:ℝ)*B*(1/L)^2*a0^3

  | 2,3 => (-5:ℝ)*(1/L)*a0^2*a1^2*s + (-4:ℝ)*(1/L)*a0^3*a1*s + (-20:ℝ)*(1/L)^2*a0^2*a1^2*s

  | 2,4 => (10:ℝ)*(1/L)^2*a0^3*a1^2*s

  | 3,0 => (-25/36:ℝ)*a1 + (25/4:ℝ)*a1*s + (5/3:ℝ)*a0 + (-5:ℝ)*a0*s + (25/18:ℝ)*(1/L)*a1 + (-5/3:ℝ)*(1/L)*a0 + (-25/12:ℝ)*B*(1/L)*a1 + (10/3:ℝ)*B*(1/L)*a0

  | 3,1 => (-25/12:ℝ)*a1^2*s + (-10/3:ℝ)*a0*a1*s + (1:ℝ)*a0^2*s + (-25/3:ℝ)*(1/L)*a1^2*s + (-10/3:ℝ)*(1/L)*a0*a1 + (20/3:ℝ)*(1/L)*a0*a1*s + (2:ℝ)*(1/L)*a0^2 + (25/12:ℝ)*B*(1/L)*a1^2 + (-20/3:ℝ)*B*(1/L)*a0*a1 + (1:ℝ)*B*(1/L)*a0^2

  | 3,2 => (25/144:ℝ)*a1^3*s + (5/4:ℝ)*a0*a1^2*s + (3/4:ℝ)*a0^2*a1*s + (25/18:ℝ)*(1/L)*a1^3*s + (5/4:ℝ)*(1/L)*a0*a1^2 + (20:ℝ)*(1/L)*a0*a1^2*s + (-3/2:ℝ)*(1/L)*a0^2*a1 + (-6:ℝ)*(1/L)*a0^2*a1*s + (25/9:ℝ)*(1/L)^2*a1^3*s + (-25/144:ℝ)*B*(1/L)*a1^3 + (3/4:ℝ)*B*(1/L)*a0^2*a1 + (-25/36:ℝ)*B*(1/L)^2*a1^3 + (5:ℝ)*B*(1/L)^2*a0*a1^2 + (-3:ℝ)*B*(1/L)^2*a0^2*a1

  | 3,3 => (-10/3:ℝ)*(1/L)*a0*a1^3*s + (-6:ℝ)*(1/L)*a0^2*a1^2*s + (-40/3:ℝ)*(1/L)^2*a0*a1^3*s

  | 3,4 => (10:ℝ)*(1/L)^2*a0^2*a1^3*s

  | 4,0 => (5/3:ℝ)*a1 + (-5:ℝ)*a1*s + (-1:ℝ)*a0 + (1:ℝ)*a0*s + (-5/3:ℝ)*(1/L)*a1 + (10/3:ℝ)*B*(1/L)*a1 + (-1:ℝ)*B*(1/L)*a0

  | 4,1 => (-5/3:ℝ)*a1^2*s + (2:ℝ)*a0*a1*s + (-5/3:ℝ)*(1/L)*a1^2 + (10/3:ℝ)*(1/L)*a1^2*s + (4:ℝ)*(1/L)*a0*a1 + (-10/3:ℝ)*B*(1/L)*a1^2 + (2:ℝ)*B*(1/L)*a0*a1

  | 4,2 => (5/12:ℝ)*a1^3*s + (3/4:ℝ)*a0*a1^2*s + (5/12:ℝ)*(1/L)*a1^3 + (20/3:ℝ)*(1/L)*a1^3*s + (-3/2:ℝ)*(1/L)*a0*a1^2 + (-6:ℝ)*(1/L)*a0*a1^2*s + (3/4:ℝ)*B*(1/L)*a0*a1^2 + (5/3:ℝ)*B*(1/L)^2*a1^3 + (-3:ℝ)*B*(1/L)^2*a0*a1^2

  | 4,3 => (-5/6:ℝ)*(1/L)*a1^4*s + (-4:ℝ)*(1/L)*a0*a1^3*s + (-10/3:ℝ)*(1/L)^2*a1^4*s

  | 4,4 => (5:ℝ)*(1/L)^2*a0*a1^4*s

  | 5,0 => (-1:ℝ)*a1 + (1:ℝ)*a1*s + (-1:ℝ)*B*(1/L)*a1

  | 5,1 => (1:ℝ)*a1^2*s + (2:ℝ)*(1/L)*a1^2 + (1:ℝ)*B*(1/L)*a1^2

  | 5,2 => (1/4:ℝ)*a1^3*s + (-1/2:ℝ)*(1/L)*a1^3 + (-2:ℝ)*(1/L)*a1^3*s + (1/4:ℝ)*B*(1/L)*a1^3 + (-1:ℝ)*B*(1/L)^2*a1^3

  | 5,3 => (-1:ℝ)*(1/L)*a1^4*s

  | 5,4 => (1:ℝ)*(1/L)^2*a1^5*s

  | _,_ => 0

theorem affineBudget_power (B L c a0 a1 s : ℝ) (nu z : ℝ) :
    powerEval (affineBudgetPower B L c a0 a1 s) nu z = affineBudgetAmp B L c a0 a1 s nu z := by
  norm_num [powerEval,affineBudgetPower,affineBudgetAmp,Fin.sum_univ_succ]
  ring

theorem affineBudget_amplitude_identity (B L c a0 a1 s : ℝ) (nu z : ℝ) :
    affineBudgetAmp B L c a0 a1 s nu z =
      affineBudgetK B L c a0 a1 s nu z*affineBudgetDz B L c a0 a1 s nu z-
      affineBudgetKz B L c a0 a1 s nu z*affineBudgetD B L c a0 a1 s nu z+
      (a0+a1*nu)*s*(affineBudgetD B L c a0 a1 s nu z)^2 := by
  unfold affineBudgetAmp affineBudgetK affineBudgetD affineBudgetDz affineBudgetKz
  ring

theorem affineBudget_nonneg (B L c a0 a1 s : ℝ) (lo hi nu z : ℝ) (hlo : lo < hi)
    (hnu : nu ∈ Set.Icc lo hi) (hz : z ∈ Set.Icc (0:ℝ) 1)
    (hc : ∀ i j, 0 ≤ coefficients (affineBudgetPower B L c a0 a1 s) lo hi i j) :
    0 ≤ affineBudgetAmp B L c a0 a1 s nu z := by
  let x := (nu-lo)/(hi-lo)
  have hx : x ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hnu.1]) (by linarith)
    · exact (div_le_one (by linarith : 0 < hi-lo)).2 (by linarith [hnu.2])
  have he : lo+(hi-lo)*x=nu := by dsimp [x]; field_simp [(sub_pos.mpr hlo).ne']; ring
  have hp := bernEval_nonneg hc hx hz
  rw [← reconstruct54,he,affineBudget_power] at hp
  exact hp

def rayCapHigh (B L c a0 a1 H P S u rho : ℝ) (nu : ℝ) : ℝ := (-5/2:ℝ)*rho + (5/2:ℝ)*u + (5/12:ℝ)*a1*rho + (-5/12:ℝ)*a1*u + (1:ℝ)*nu*rho + (-1:ℝ)*nu*u + (-5/2:ℝ)*nu*P + (5/3:ℝ)*nu*H + (1/2:ℝ)*nu*a1*rho + (-1/2:ℝ)*nu*a1*u + (-5/2:ℝ)*nu*a1*S + (5/12:ℝ)*nu*a1*P + (5/12:ℝ)*nu*a1^2*S + (5/6:ℝ)*nu*c*a1*H + (-5/12:ℝ)*nu*c*a1^2*H + (1:ℝ)*nu^2*P + (1:ℝ)*nu^2*a1*S + (1/2:ℝ)*nu^2*a1*P + (-1:ℝ)*nu^2*a1*H + (1/2:ℝ)*nu^2*a1^2*S + (-1:ℝ)*nu^2*c*a1*H + (1/2:ℝ)*nu^2*c*a1^2*H

def rayCapHighPower (B L c a0 a1 H P S u rho : ℝ) (i : Fin 3) (_j : Fin 1) : ℝ :=
  match i.val with

  | 0 => (-5/2:ℝ)*rho + (5/2:ℝ)*u + (5/12:ℝ)*a1*rho + (-5/12:ℝ)*a1*u

  | 1 => (1:ℝ)*rho + (-1:ℝ)*u + (-5/2:ℝ)*P + (5/3:ℝ)*H + (1/2:ℝ)*a1*rho + (-1/2:ℝ)*a1*u + (-5/2:ℝ)*a1*S + (5/12:ℝ)*a1*P + (5/12:ℝ)*a1^2*S + (5/6:ℝ)*c*a1*H + (-5/12:ℝ)*c*a1^2*H

  | 2 => (1:ℝ)*P + (1:ℝ)*a1*S + (1/2:ℝ)*a1*P + (-1:ℝ)*a1*H + (1/2:ℝ)*a1^2*S + (-1:ℝ)*c*a1*H + (1/2:ℝ)*c*a1^2*H

  | _ => 0

theorem rayCap_high_power (B L c a0 a1 H P S u rho : ℝ) (nu : ℝ) :
    powerEval (rayCapHighPower B L c a0 a1 H P S u rho) nu 0 = rayCapHigh B L c a0 a1 H P S u rho nu := by
  norm_num [powerEval,rayCapHighPower,rayCapHigh,Fin.sum_univ_succ]
  ring

theorem rayCap_high_identity (B L c a0 a1 H P S u rho : ℝ) (nu : ℝ) :
    rayCapHigh B L c a0 a1 H P S u rho nu = H*rayCapK B L c a0 a1 0 nu 1-
      nu*P*rayCapD B L c a0 a1 0 nu 1-
      (a1*nu)*S*rayCapD B L c a0 a1 0 nu 1+
      u*rayCapD B L c a0 a1 0 nu 1-rho*rayCapD B L c a0 a1 0 nu 1 := by
  unfold rayCapHigh rayCapK rayCapD
  ring

theorem rayCap_high_nonneg (B L c a0 a1 H P S u rho : ℝ) (lo hi nu : ℝ) (hlo : lo < hi)
    (hnu : nu ∈ Set.Icc lo hi)
    (hc : ∀ i j, 0 ≤ coefficients (rayCapHighPower B L c a0 a1 H P S u rho) lo hi i j) :
    0 ≤ rayCapHigh B L c a0 a1 H P S u rho nu := by
  let x := (nu-lo)/(hi-lo)
  have hx : x ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hnu.1]) (by linarith)
    · exact (div_le_one (by linarith : 0 < hi-lo)).2 (by linarith [hnu.2])
  have he : lo+(hi-lo)*x=nu := by dsimp [x]; field_simp [(sub_pos.mpr hlo).ne']; ring
  have hp := bernEval_nonneg hc hx (show (0:ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl,by norm_num⟩)
  rw [← reconstruct20,he,rayCap_high_power] at hp
  exact hp

def rayBudgetHigh (B L c a0 a1 H P S u rho : ℝ) (nu : ℝ) : ℝ := (-5/2:ℝ)*rho + (5/2:ℝ)*u + (5/12:ℝ)*a1*rho + (-5/12:ℝ)*a1*u + (5/3:ℝ)*(1/L)*a1*rho + (-5/3:ℝ)*(1/L)*a1*u + (1:ℝ)*nu*rho + (-1:ℝ)*nu*u + (-5/2:ℝ)*nu*P + (5/3:ℝ)*nu*H + (1/2:ℝ)*nu*a1*rho + (-1/2:ℝ)*nu*a1*u + (-5/2:ℝ)*nu*a1*S + (5/12:ℝ)*nu*a1*P + (5/12:ℝ)*nu*a1^2*S + (5/3:ℝ)*nu*(1/L)*a1*P + (-5/3:ℝ)*nu*(1/L)*a1*H + (-1:ℝ)*nu*(1/L)*a1^2*rho + (1:ℝ)*nu*(1/L)*a1^2*u + (5/3:ℝ)*nu*(1/L)*a1^2*S + (5/6:ℝ)*nu*B*(1/L)*a1*H + (-5/12:ℝ)*nu*B*(1/L)*a1^2*H + (1:ℝ)*nu^2*P + (1:ℝ)*nu^2*a1*S + (1/2:ℝ)*nu^2*a1*P + (-1:ℝ)*nu^2*a1*H + (1/2:ℝ)*nu^2*a1^2*S + (-1:ℝ)*nu^2*(1/L)*a1^2*P + (1:ℝ)*nu^2*(1/L)*a1^2*H + (-1:ℝ)*nu^2*(1/L)*a1^3*S + (-1:ℝ)*nu^2*B*(1/L)*a1*H + (1/2:ℝ)*nu^2*B*(1/L)*a1^2*H

def rayBudgetHighPower (B L c a0 a1 H P S u rho : ℝ) (i : Fin 3) (_j : Fin 1) : ℝ :=
  match i.val with

  | 0 => (-5/2:ℝ)*rho + (5/2:ℝ)*u + (5/12:ℝ)*a1*rho + (-5/12:ℝ)*a1*u + (5/3:ℝ)*(1/L)*a1*rho + (-5/3:ℝ)*(1/L)*a1*u

  | 1 => (1:ℝ)*rho + (-1:ℝ)*u + (-5/2:ℝ)*P + (5/3:ℝ)*H + (1/2:ℝ)*a1*rho + (-1/2:ℝ)*a1*u + (-5/2:ℝ)*a1*S + (5/12:ℝ)*a1*P + (5/12:ℝ)*a1^2*S + (5/3:ℝ)*(1/L)*a1*P + (-5/3:ℝ)*(1/L)*a1*H + (-1:ℝ)*(1/L)*a1^2*rho + (1:ℝ)*(1/L)*a1^2*u + (5/3:ℝ)*(1/L)*a1^2*S + (5/6:ℝ)*B*(1/L)*a1*H + (-5/12:ℝ)*B*(1/L)*a1^2*H

  | 2 => (1:ℝ)*P + (1:ℝ)*a1*S + (1/2:ℝ)*a1*P + (-1:ℝ)*a1*H + (1/2:ℝ)*a1^2*S + (-1:ℝ)*(1/L)*a1^2*P + (1:ℝ)*(1/L)*a1^2*H + (-1:ℝ)*(1/L)*a1^3*S + (-1:ℝ)*B*(1/L)*a1*H + (1/2:ℝ)*B*(1/L)*a1^2*H

  | _ => 0

theorem rayBudget_high_power (B L c a0 a1 H P S u rho : ℝ) (nu : ℝ) :
    powerEval (rayBudgetHighPower B L c a0 a1 H P S u rho) nu 0 = rayBudgetHigh B L c a0 a1 H P S u rho nu := by
  norm_num [powerEval,rayBudgetHighPower,rayBudgetHigh,Fin.sum_univ_succ]
  ring

theorem rayBudget_high_identity (B L c a0 a1 H P S u rho : ℝ) (nu : ℝ) :
    rayBudgetHigh B L c a0 a1 H P S u rho nu = H*rayBudgetK B L c a0 a1 0 nu 1-
      nu*P*rayBudgetD B L c a0 a1 0 nu 1-
      (a1*nu)*S*rayBudgetD B L c a0 a1 0 nu 1+
      u*rayBudgetD B L c a0 a1 0 nu 1-rho*rayBudgetD B L c a0 a1 0 nu 1 := by
  unfold rayBudgetHigh rayBudgetK rayBudgetD
  ring

theorem rayBudget_high_nonneg (B L c a0 a1 H P S u rho : ℝ) (lo hi nu : ℝ) (hlo : lo < hi)
    (hnu : nu ∈ Set.Icc lo hi)
    (hc : ∀ i j, 0 ≤ coefficients (rayBudgetHighPower B L c a0 a1 H P S u rho) lo hi i j) :
    0 ≤ rayBudgetHigh B L c a0 a1 H P S u rho nu := by
  let x := (nu-lo)/(hi-lo)
  have hx : x ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hnu.1]) (by linarith)
    · exact (div_le_one (by linarith : 0 < hi-lo)).2 (by linarith [hnu.2])
  have he : lo+(hi-lo)*x=nu := by dsimp [x]; field_simp [(sub_pos.mpr hlo).ne']; ring
  have hp := bernEval_nonneg hc hx (show (0:ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl,by norm_num⟩)
  rw [← reconstruct20,he,rayBudget_high_power] at hp
  exact hp

def affineCapHigh (B L c a0 a1 H P S u rho : ℝ) (nu : ℝ) : ℝ := (5/12:ℝ)*a0*rho + (-5/12:ℝ)*a0*u + (5/12:ℝ)*a0^2*S + (-5/12:ℝ)*c*a0^2*H + (-5/2:ℝ)*nu*rho + (5/2:ℝ)*nu*u + (5/12:ℝ)*nu*a1*rho + (-5/12:ℝ)*nu*a1*u + (1/2:ℝ)*nu*a0*rho + (-1/2:ℝ)*nu*a0*u + (-5/2:ℝ)*nu*a0*S + (5/12:ℝ)*nu*a0*P + (5/6:ℝ)*nu*a0*a1*S + (1/2:ℝ)*nu*a0^2*S + (5/6:ℝ)*nu*c*a0*H + (-5/6:ℝ)*nu*c*a0*a1*H + (1/2:ℝ)*nu*c*a0^2*H + (1:ℝ)*nu^2*rho + (-1:ℝ)*nu^2*u + (-5/2:ℝ)*nu^2*P + (5/3:ℝ)*nu^2*H + (1/2:ℝ)*nu^2*a1*rho + (-1/2:ℝ)*nu^2*a1*u + (-5/2:ℝ)*nu^2*a1*S + (5/12:ℝ)*nu^2*a1*P + (5/12:ℝ)*nu^2*a1^2*S + (1:ℝ)*nu^2*a0*S + (1/2:ℝ)*nu^2*a0*P + (-1:ℝ)*nu^2*a0*H + (1:ℝ)*nu^2*a0*a1*S + (5/6:ℝ)*nu^2*c*a1*H + (-5/12:ℝ)*nu^2*c*a1^2*H + (-1:ℝ)*nu^2*c*a0*H + (1:ℝ)*nu^2*c*a0*a1*H + (1:ℝ)*nu^3*P + (1:ℝ)*nu^3*a1*S + (1/2:ℝ)*nu^3*a1*P + (-1:ℝ)*nu^3*a1*H + (1/2:ℝ)*nu^3*a1^2*S + (-1:ℝ)*nu^3*c*a1*H + (1/2:ℝ)*nu^3*c*a1^2*H

def affineCapHighPower (B L c a0 a1 H P S u rho : ℝ) (i : Fin 4) (_j : Fin 1) : ℝ :=
  match i.val with

  | 0 => (5/12:ℝ)*a0*rho + (-5/12:ℝ)*a0*u + (5/12:ℝ)*a0^2*S + (-5/12:ℝ)*c*a0^2*H

  | 1 => (-5/2:ℝ)*rho + (5/2:ℝ)*u + (5/12:ℝ)*a1*rho + (-5/12:ℝ)*a1*u + (1/2:ℝ)*a0*rho + (-1/2:ℝ)*a0*u + (-5/2:ℝ)*a0*S + (5/12:ℝ)*a0*P + (5/6:ℝ)*a0*a1*S + (1/2:ℝ)*a0^2*S + (5/6:ℝ)*c*a0*H + (-5/6:ℝ)*c*a0*a1*H + (1/2:ℝ)*c*a0^2*H

  | 2 => (1:ℝ)*rho + (-1:ℝ)*u + (-5/2:ℝ)*P + (5/3:ℝ)*H + (1/2:ℝ)*a1*rho + (-1/2:ℝ)*a1*u + (-5/2:ℝ)*a1*S + (5/12:ℝ)*a1*P + (5/12:ℝ)*a1^2*S + (1:ℝ)*a0*S + (1/2:ℝ)*a0*P + (-1:ℝ)*a0*H + (1:ℝ)*a0*a1*S + (5/6:ℝ)*c*a1*H + (-5/12:ℝ)*c*a1^2*H + (-1:ℝ)*c*a0*H + (1:ℝ)*c*a0*a1*H

  | 3 => (1:ℝ)*P + (1:ℝ)*a1*S + (1/2:ℝ)*a1*P + (-1:ℝ)*a1*H + (1/2:ℝ)*a1^2*S + (-1:ℝ)*c*a1*H + (1/2:ℝ)*c*a1^2*H

  | _ => 0

theorem affineCap_high_power (B L c a0 a1 H P S u rho : ℝ) (nu : ℝ) :
    powerEval (affineCapHighPower B L c a0 a1 H P S u rho) nu 0 = affineCapHigh B L c a0 a1 H P S u rho nu := by
  norm_num [powerEval,affineCapHighPower,affineCapHigh,Fin.sum_univ_succ]
  ring

theorem affineCap_high_identity (B L c a0 a1 H P S u rho : ℝ) (nu : ℝ) :
    affineCapHigh B L c a0 a1 H P S u rho nu = H*affineCapK B L c a0 a1 0 nu 1-
      nu*P*affineCapD B L c a0 a1 0 nu 1-
      (a0+a1*nu)*S*affineCapD B L c a0 a1 0 nu 1+
      u*affineCapD B L c a0 a1 0 nu 1-rho*affineCapD B L c a0 a1 0 nu 1 := by
  unfold affineCapHigh affineCapK affineCapD
  ring

theorem affineCap_high_nonneg (B L c a0 a1 H P S u rho : ℝ) (lo hi nu : ℝ) (hlo : lo < hi)
    (hnu : nu ∈ Set.Icc lo hi)
    (hc : ∀ i j, 0 ≤ coefficients (affineCapHighPower B L c a0 a1 H P S u rho) lo hi i j) :
    0 ≤ affineCapHigh B L c a0 a1 H P S u rho nu := by
  let x := (nu-lo)/(hi-lo)
  have hx : x ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hnu.1]) (by linarith)
    · exact (div_le_one (by linarith : 0 < hi-lo)).2 (by linarith [hnu.2])
  have he : lo+(hi-lo)*x=nu := by dsimp [x]; field_simp [(sub_pos.mpr hlo).ne']; ring
  have hp := bernEval_nonneg hc hx (show (0:ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl,by norm_num⟩)
  rw [← reconstruct30,he,affineCap_high_power] at hp
  exact hp

def affineBudgetHigh (B L c a0 a1 H P S u rho : ℝ) (nu : ℝ) : ℝ := (5/12:ℝ)*a0*rho + (-5/12:ℝ)*a0*u + (5/12:ℝ)*a0^2*S + (5/3:ℝ)*(1/L)*a0*rho + (-5/3:ℝ)*(1/L)*a0*u + (-1:ℝ)*(1/L)*a0^2*rho + (1:ℝ)*(1/L)*a0^2*u + (5/3:ℝ)*(1/L)*a0^2*S + (-1:ℝ)*(1/L)*a0^3*S + (-5/12:ℝ)*B*(1/L)*a0^2*H + (-5/2:ℝ)*nu*rho + (5/2:ℝ)*nu*u + (5/12:ℝ)*nu*a1*rho + (-5/12:ℝ)*nu*a1*u + (1/2:ℝ)*nu*a0*rho + (-1/2:ℝ)*nu*a0*u + (-5/2:ℝ)*nu*a0*S + (5/12:ℝ)*nu*a0*P + (5/6:ℝ)*nu*a0*a1*S + (1/2:ℝ)*nu*a0^2*S + (5/3:ℝ)*nu*(1/L)*a1*rho + (-5/3:ℝ)*nu*(1/L)*a1*u + (5/3:ℝ)*nu*(1/L)*a0*P + (-5/3:ℝ)*nu*(1/L)*a0*H + (-2:ℝ)*nu*(1/L)*a0*a1*rho + (2:ℝ)*nu*(1/L)*a0*a1*u + (10/3:ℝ)*nu*(1/L)*a0*a1*S + (-1:ℝ)*nu*(1/L)*a0^2*P + (1:ℝ)*nu*(1/L)*a0^2*H + (-3:ℝ)*nu*(1/L)*a0^2*a1*S + (5/6:ℝ)*nu*B*(1/L)*a0*H + (-5/6:ℝ)*nu*B*(1/L)*a0*a1*H + (1/2:ℝ)*nu*B*(1/L)*a0^2*H + (1:ℝ)*nu^2*rho + (-1:ℝ)*nu^2*u + (-5/2:ℝ)*nu^2*P + (5/3:ℝ)*nu^2*H + (1/2:ℝ)*nu^2*a1*rho + (-1/2:ℝ)*nu^2*a1*u + (-5/2:ℝ)*nu^2*a1*S + (5/12:ℝ)*nu^2*a1*P + (5/12:ℝ)*nu^2*a1^2*S + (1:ℝ)*nu^2*a0*S + (1/2:ℝ)*nu^2*a0*P + (-1:ℝ)*nu^2*a0*H + (1:ℝ)*nu^2*a0*a1*S + (5/3:ℝ)*nu^2*(1/L)*a1*P + (-5/3:ℝ)*nu^2*(1/L)*a1*H + (-1:ℝ)*nu^2*(1/L)*a1^2*rho + (1:ℝ)*nu^2*(1/L)*a1^2*u + (5/3:ℝ)*nu^2*(1/L)*a1^2*S + (-2:ℝ)*nu^2*(1/L)*a0*a1*P + (2:ℝ)*nu^2*(1/L)*a0*a1*H + (-3:ℝ)*nu^2*(1/L)*a0*a1^2*S + (5/6:ℝ)*nu^2*B*(1/L)*a1*H + (-5/12:ℝ)*nu^2*B*(1/L)*a1^2*H + (-1:ℝ)*nu^2*B*(1/L)*a0*H + (1:ℝ)*nu^2*B*(1/L)*a0*a1*H + (1:ℝ)*nu^3*P + (1:ℝ)*nu^3*a1*S + (1/2:ℝ)*nu^3*a1*P + (-1:ℝ)*nu^3*a1*H + (1/2:ℝ)*nu^3*a1^2*S + (-1:ℝ)*nu^3*(1/L)*a1^2*P + (1:ℝ)*nu^3*(1/L)*a1^2*H + (-1:ℝ)*nu^3*(1/L)*a1^3*S + (-1:ℝ)*nu^3*B*(1/L)*a1*H + (1/2:ℝ)*nu^3*B*(1/L)*a1^2*H

def affineBudgetHighPower (B L c a0 a1 H P S u rho : ℝ) (i : Fin 4) (_j : Fin 1) : ℝ :=
  match i.val with

  | 0 => (5/12:ℝ)*a0*rho + (-5/12:ℝ)*a0*u + (5/12:ℝ)*a0^2*S + (5/3:ℝ)*(1/L)*a0*rho + (-5/3:ℝ)*(1/L)*a0*u + (-1:ℝ)*(1/L)*a0^2*rho + (1:ℝ)*(1/L)*a0^2*u + (5/3:ℝ)*(1/L)*a0^2*S + (-1:ℝ)*(1/L)*a0^3*S + (-5/12:ℝ)*B*(1/L)*a0^2*H

  | 1 => (-5/2:ℝ)*rho + (5/2:ℝ)*u + (5/12:ℝ)*a1*rho + (-5/12:ℝ)*a1*u + (1/2:ℝ)*a0*rho + (-1/2:ℝ)*a0*u + (-5/2:ℝ)*a0*S + (5/12:ℝ)*a0*P + (5/6:ℝ)*a0*a1*S + (1/2:ℝ)*a0^2*S + (5/3:ℝ)*(1/L)*a1*rho + (-5/3:ℝ)*(1/L)*a1*u + (5/3:ℝ)*(1/L)*a0*P + (-5/3:ℝ)*(1/L)*a0*H + (-2:ℝ)*(1/L)*a0*a1*rho + (2:ℝ)*(1/L)*a0*a1*u + (10/3:ℝ)*(1/L)*a0*a1*S + (-1:ℝ)*(1/L)*a0^2*P + (1:ℝ)*(1/L)*a0^2*H + (-3:ℝ)*(1/L)*a0^2*a1*S + (5/6:ℝ)*B*(1/L)*a0*H + (-5/6:ℝ)*B*(1/L)*a0*a1*H + (1/2:ℝ)*B*(1/L)*a0^2*H

  | 2 => (1:ℝ)*rho + (-1:ℝ)*u + (-5/2:ℝ)*P + (5/3:ℝ)*H + (1/2:ℝ)*a1*rho + (-1/2:ℝ)*a1*u + (-5/2:ℝ)*a1*S + (5/12:ℝ)*a1*P + (5/12:ℝ)*a1^2*S + (1:ℝ)*a0*S + (1/2:ℝ)*a0*P + (-1:ℝ)*a0*H + (1:ℝ)*a0*a1*S + (5/3:ℝ)*(1/L)*a1*P + (-5/3:ℝ)*(1/L)*a1*H + (-1:ℝ)*(1/L)*a1^2*rho + (1:ℝ)*(1/L)*a1^2*u + (5/3:ℝ)*(1/L)*a1^2*S + (-2:ℝ)*(1/L)*a0*a1*P + (2:ℝ)*(1/L)*a0*a1*H + (-3:ℝ)*(1/L)*a0*a1^2*S + (5/6:ℝ)*B*(1/L)*a1*H + (-5/12:ℝ)*B*(1/L)*a1^2*H + (-1:ℝ)*B*(1/L)*a0*H + (1:ℝ)*B*(1/L)*a0*a1*H

  | 3 => (1:ℝ)*P + (1:ℝ)*a1*S + (1/2:ℝ)*a1*P + (-1:ℝ)*a1*H + (1/2:ℝ)*a1^2*S + (-1:ℝ)*(1/L)*a1^2*P + (1:ℝ)*(1/L)*a1^2*H + (-1:ℝ)*(1/L)*a1^3*S + (-1:ℝ)*B*(1/L)*a1*H + (1/2:ℝ)*B*(1/L)*a1^2*H

  | _ => 0

theorem affineBudget_high_power (B L c a0 a1 H P S u rho : ℝ) (nu : ℝ) :
    powerEval (affineBudgetHighPower B L c a0 a1 H P S u rho) nu 0 = affineBudgetHigh B L c a0 a1 H P S u rho nu := by
  norm_num [powerEval,affineBudgetHighPower,affineBudgetHigh,Fin.sum_univ_succ]
  ring

theorem affineBudget_high_identity (B L c a0 a1 H P S u rho : ℝ) (nu : ℝ) :
    affineBudgetHigh B L c a0 a1 H P S u rho nu = H*affineBudgetK B L c a0 a1 0 nu 1-
      nu*P*affineBudgetD B L c a0 a1 0 nu 1-
      (a0+a1*nu)*S*affineBudgetD B L c a0 a1 0 nu 1+
      u*affineBudgetD B L c a0 a1 0 nu 1-rho*affineBudgetD B L c a0 a1 0 nu 1 := by
  unfold affineBudgetHigh affineBudgetK affineBudgetD
  ring

theorem affineBudget_high_nonneg (B L c a0 a1 H P S u rho : ℝ) (lo hi nu : ℝ) (hlo : lo < hi)
    (hnu : nu ∈ Set.Icc lo hi)
    (hc : ∀ i j, 0 ≤ coefficients (affineBudgetHighPower B L c a0 a1 H P S u rho) lo hi i j) :
    0 ≤ affineBudgetHigh B L c a0 a1 H P S u rho nu := by
  let x := (nu-lo)/(hi-lo)
  have hx : x ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith [hnu.1]) (by linarith)
    · exact (div_le_one (by linarith : 0 < hi-lo)).2 (by linarith [hnu.2])
  have he : lo+(hi-lo)*x=nu := by dsimp [x]; field_simp [(sub_pos.mpr hlo).ne']; ring
  have hp := bernEval_nonneg hc hx (show (0:ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl,by norm_num⟩)
  rw [← reconstruct30,he,affineBudget_high_power] at hp
  exact hp

end
end Qrh.JointDetector.RepeatedMarks.HighTemplates
