/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
/- Private .874836 geometry adapted from Hailey Collet and accepted PR60; Apache-2.0. No endpoint theorem. -/
import Candidate.Cycle63.Moment.InitialAffineContract
import Candidate.Uneven.EndpointScalar
import Mathlib.Tactic.NormNum

namespace UnevenEndpointPhysical.Arithmetic
variable [config : OAI.SevenEighths.UnevenEndpoint.Configuration]

noncomputable section

abbrev theta : ℝ := OAI.SevenEighths.UnevenEndpoint.theta
def c : ℝ := 1-theta
abbrev h : ℝ := OAI.SevenEighths.UnevenEndpoint.h
abbrev ell : ℝ := OAI.SevenEighths.UnevenEndpoint.ell
abbrev x : ℝ := OAI.SevenEighths.UnevenEndpoint.x
abbrev y : ℝ := OAI.SevenEighths.UnevenEndpoint.y
def kappaStar : ℝ := 2*theta-1
abbrev dMinus : ℝ := OAI.SevenEighths.UnevenEndpoint.dMinus
abbrev dPlus : ℝ := OAI.SevenEighths.UnevenEndpoint.dPlus
def d0 : ℝ := 1 / 200
def lambda : ℝ := 19793/5000
def B : ℝ := 987047/1000000
def B0 : ℝ := 986347/1000000
def q0 : ℝ := 839/1250
def rho0 : ℝ := 2663/6858
def Ka : ℝ := 4195/2943
def alpha : ℝ := 9371/3924000000
def t0 : ℝ := 103/100000

theorem ell_eq : ell = 11 / 3 - 4 * theta := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,ell, theta]
theorem x_eq : x = 1 + ell - h := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,x, ell, h]

theorem ell_pos : 0 < ell := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,ell]
theorem ell_lt_x : ell < x := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,ell, x]
theorem x_lt_y : x < y := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,x, y]
theorem y_lt_half : y < 1 / 2 := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,y]
theorem sixth_lt_ell : 1 / 6 < ell := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,ell]
theorem ell_lt_fifth : ell < 1 / 5 := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,ell]
theorem x_add_y : x + y = 1 - ell := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,x, y, ell]

end

end UnevenEndpointPhysical.Arithmetic


namespace UnevenEndpointPhysical.Assembly
variable [config : OAI.SevenEighths.UnevenEndpoint.Configuration]
noncomputable section
open UnevenEndpointPhysical.Arithmetic
def signalShift : ℝ := -(5/6-x/3-ell/6)
def signal (s : ℝ) : ℝ := s+signalShift
theorem signalShift_eq : signalShift=-(4+(y-x))/6 := by
  unfold signalShift
  linarith [x_add_y]
theorem signal_at_boundary : signal theta=x/2+(y-x)/12 := by
  unfold signal signalShift
  linarith [ell_eq,x_add_y]
end
end UnevenEndpointPhysical.Assembly


namespace UnevenEndpointPhysical.Assembly
variable [config : OAI.SevenEighths.UnevenEndpoint.Configuration]
noncomputable section
open UnevenEndpointPhysical.Arithmetic
theorem theta_lt_seven_eighths : theta < (7/8:ℝ) := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,theta]
theorem row_endpoint : h=1-x+ell := by linarith [x_eq]
end
end UnevenEndpointPhysical.Assembly

namespace UnevenEndpointPhysical.Transport
variable [config : OAI.SevenEighths.UnevenEndpoint.Configuration]
noncomputable section

abbrev theta : ℝ := Arithmetic.theta
abbrev lx : ℝ := Arithmetic.x
abbrev ly : ℝ := Arithmetic.y
abbrev ell : ℝ := Arithmetic.ell
abbrev h : ℝ := Arithmetic.h
def b : ℝ := ly-lx
abbrev signal := Assembly.signal
def rowExtension : ℝ := OAI.SevenEighths.UnevenEndpoint.upperPadding

theorem ell_interval : (1672 : ℝ)/10000 < ell ∧ ell < 1674/10000 := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,ell, Arithmetic.ell]
theorem h_pos : 0 < h := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,h, Arithmetic.h]
theorem extended_h_lt_one : h+rowExtension < 1 := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,h, Arithmetic.h, rowExtension]

theorem theta_lower : (874 : ℝ)/1000 < theta := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,theta, Arithmetic.theta]
theorem theta_bounds : (874 : ℝ)/1000 < theta ∧ theta < 7/8 :=
  ⟨theta_lower, Assembly.theta_lt_seven_eighths⟩
theorem h_interval : (793 : ℝ)/1000 < h ∧ h < 798/1000 := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,h, Arithmetic.h]
theorem ly_coarse : (458 : ℝ)/1000 < ly ∧ ly < 463/1000 := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,ly, Arithmetic.y]
theorem length_sum : lx+ly = 1-ell := Arithmetic.x_add_y
theorem row_endpoint : h = 1-lx+ell := Assembly.row_endpoint
theorem small_saving : (7/100 : ℝ) < ly/2-h*(17/50-1/6)-1/50 := by
  cases config with
  | mk stage => cases stage <;> norm_num [OAI.SevenEighths.UnevenEndpoint.upperPadding,Sil.Uneven.WarmupRows.theta,Sil.Uneven.WarmupRows.h,Sil.Uneven.RoundedRows.theta,Sil.Uneven.RoundedRows.h,OAI.SevenEighths.UnevenEndpoint.theta,OAI.SevenEighths.UnevenEndpoint.h,OAI.SevenEighths.UnevenEndpoint.ell,OAI.SevenEighths.UnevenEndpoint.x,OAI.SevenEighths.UnevenEndpoint.y,OAI.SevenEighths.UnevenEndpoint.dMinus,OAI.SevenEighths.UnevenEndpoint.dPlus,ly, h, Arithmetic.y, Arithmetic.h]
theorem signalShift_eq : -(4+b)/6 = Assembly.signalShift := by
  exact Assembly.signalShift_eq.symm




end
end UnevenEndpointPhysical.Transport

