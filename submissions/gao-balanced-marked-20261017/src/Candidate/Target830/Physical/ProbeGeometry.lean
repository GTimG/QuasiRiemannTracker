/- Private .874836 geometry adapted from Hailey Collet and accepted PR60; Apache-2.0. No endpoint theorem. -/
import Candidate.Cycle63.Moment.InitialAffineContract
import Candidate.Target830.Physical.Scalar
import Mathlib.Tactic.NormNum

namespace Target830Physical.Arithmetic

noncomputable section

abbrev theta : ℝ := OAI.SevenEighths.Target830.theta
def c : ℝ := 12517/100000
abbrev h : ℝ := OAI.SevenEighths.Target830.h
abbrev ell : ℝ := OAI.SevenEighths.Target830.ell
abbrev x : ℝ := OAI.SevenEighths.Target830.x
abbrev y : ℝ := OAI.SevenEighths.Target830.y
def kappaStar : ℝ := 37483/50000
abbrev dMinus : ℝ := OAI.SevenEighths.Target830.dMinus
abbrev dPlus : ℝ := OAI.SevenEighths.Target830.dPlus
def d0 : ℝ := 1 / 200
def lambda : ℝ := 19793/5000
def B : ℝ := 987047/1000000
def B0 : ℝ := 986347/1000000
def q0 : ℝ := 839/1250
def rho0 : ℝ := 2663/6858
def Ka : ℝ := 4195/2943
def alpha : ℝ := 9371/3924000000
def t0 : ℝ := 103/100000

theorem theta_eq : theta = 1 - c := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,theta, c]
theorem ell_eq : ell = 11 / 3 - 4 * theta := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,ell, theta]
theorem x_eq : x = 1 + ell - h := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,x, ell, h]
theorem y_eq : y = h - 2 * ell := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,y, ell, h]
theorem kappaStar_eq : kappaStar = 2 * theta - 1 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,kappaStar, theta]
theorem dMinus_eq : dMinus = h - 3 / 2000 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,dMinus, h]
theorem dPlus_eq : dPlus = h + 1 / 10000000000 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,dPlus, h]
theorem B_eq : B = B0 + 7 / 10000 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,B, B0]

theorem ell_pos : 0 < ell := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,ell]
theorem ell_lt_x : ell < x := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,ell, x]
theorem x_lt_y : x < y := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,x, y]
theorem y_lt_two_x : y < 2 * x := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,y, x]
theorem y_lt_half : y < 1 / 2 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,y]
theorem half_lt_h : 1 / 2 < h := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,h]
theorem h_lt_two_y : h < 2 * y := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,h, y]
theorem sixth_lt_ell : 1 / 6 < ell := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,ell]
theorem ell_lt_fifth : ell < 1 / 5 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,ell]
theorem four_ell_lt_h : 4 * ell < h := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,ell, h]
theorem x_add_y : x + y = 1 - ell := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,x, y, ell]
theorem d0_pos : 0 < d0 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,d0]
theorem half_lt_dMinus : 1 / 2 < dMinus := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,dMinus]
theorem dMinus_lt_h : dMinus < h := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,dMinus, h]
theorem h_lt_dPlus : h < dPlus := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,h, dPlus]
theorem dPlus_lt_one : dPlus < 1 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,dPlus]
theorem kappaStar_mem : 7 / 10 ≤ kappaStar ∧ kappaStar ≤ 3 / 4 := by
  norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,kappaStar]
theorem alpha_pos : 0 < alpha := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,alpha]
theorem lambda_pos : 0 < lambda := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,lambda]
theorem B_pos : 0 < B := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,B]

end

end Target830Physical.Arithmetic


namespace Target830Physical.Assembly
noncomputable section
open Target830Physical.Arithmetic
def signalShift : ℝ := -(5/6-x/3-ell/6)
def signal (s : ℝ) : ℝ := s+signalShift
theorem signalShift_eq : signalShift=-(4+(y-x))/6 := by
  unfold signalShift
  linarith [x_add_y]
theorem signal_at_boundary : signal theta=x/2+(y-x)/12 := by
  unfold signal signalShift
  linarith [ell_eq,x_add_y]
end
end Target830Physical.Assembly

#print axioms Target830Physical.Assembly.signal_at_boundary

namespace Target830Physical.Assembly
noncomputable section
open Target830Physical.Arithmetic
theorem theta_lt_seven_eighths : theta < (7/8:ℝ) := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,theta]
theorem theta_gt_half : (1/2:ℝ) < theta := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,theta]
theorem row_endpoint : h=1-x+ell := by linarith [x_eq]
end
end Target830Physical.Assembly

namespace Target830Physical.Transport
noncomputable section

abbrev theta : ℝ := Arithmetic.theta
abbrev lx : ℝ := Arithmetic.x
abbrev ly : ℝ := Arithmetic.y
abbrev ell : ℝ := Arithmetic.ell
abbrev h : ℝ := Arithmetic.h
def b : ℝ := ly-lx
abbrev signal := Assembly.signal
def rowExtension : ℝ := 1/10000000000

theorem ell_interval : (1672 : ℝ)/10000 < ell ∧ ell < 1674/10000 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,ell, Arithmetic.ell]
theorem h_pos : 0 < h := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,h, Arithmetic.h]
theorem extended_h_lt_one : h+rowExtension < 1 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,h, Arithmetic.h, rowExtension]

theorem theta_lower : (874 : ℝ)/1000 < theta := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,theta, Arithmetic.theta]
theorem theta_bounds : (874 : ℝ)/1000 < theta ∧ theta < 7/8 :=
  ⟨theta_lower, Assembly.theta_lt_seven_eighths⟩
theorem h_interval : (793 : ℝ)/1000 < h ∧ h < 798/1000 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,h, Arithmetic.h]
theorem ly_coarse : (458 : ℝ)/1000 < ly ∧ ly < 463/1000 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,ly, Arithmetic.y]
theorem length_sum : lx+ly = 1-ell := Arithmetic.x_add_y
theorem row_endpoint : h = 1-lx+ell := Assembly.row_endpoint
theorem small_saving : (7/100 : ℝ) < ly/2-h*(17/50-1/6)-1/50 := by
  norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,ly, h, Arithmetic.y, Arithmetic.h]
theorem signalShift_eq : -(4+b)/6 = Assembly.signalShift := by
  exact Assembly.signalShift_eq.symm

theorem extended_row_cutoff {ζ : ℝ} (hζ : ζ ≤ 1/10000000000) :
    h+ζ ≤ Arithmetic.dPlus := by
  rw [Arithmetic.dPlus_eq]
  linarith

theorem principal_w_reserve :
    ly/20-(1+h)/1000-1/4000 = 31604117/1500000000 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,ly,h,Arithmetic.y,Arithmetic.h]

theorem principal_z_reserve :
    h/600-1/1000-1/4000 = 7837/100000000 := by norm_num [OAI.SevenEighths.Target830.theta,OAI.SevenEighths.Target830.h,OAI.SevenEighths.Target830.ell,OAI.SevenEighths.Target830.x,OAI.SevenEighths.Target830.y,OAI.SevenEighths.Target830.dMinus,OAI.SevenEighths.Target830.dPlus,h,Arithmetic.h]

end
end Target830Physical.Transport

#print axioms Target830Physical.Transport.small_saving
#print axioms Target830Physical.Transport.principal_w_reserve
#print axioms Target830Physical.Transport.principal_z_reserve
