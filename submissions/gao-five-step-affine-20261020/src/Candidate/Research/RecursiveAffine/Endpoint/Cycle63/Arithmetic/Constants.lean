/- Fixed endpoint arithmetic, independent of the preceding row optimizer.
Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ConsumerParameters
import Candidate.Research.RecursiveAffine.RootLedgerBinding
import Candidate.Cycle63.Arithmetic.Window
import Candidate.Cycle63.Certificate.Bracket
set_option autoImplicit false
namespace Cycle153Endpoint.CountAffine
noncomputable def windowBottom : ℝ := 81/200
noncomputable def plainTop : ℝ := 264/625
noncomputable def plainLengthTop : ℝ := 44/100
end Cycle153Endpoint.CountAffine
namespace Cycle153Endpoint.Physical
noncomputable def smallPlainCap : ℝ := (1-Cycle153Endpoint.CountAffine.windowBottom-Cycle153Endpoint.CountAffine.plainTop)/(9/2)
theorem small_slot_complement :
    2*Cycle153Endpoint.CountAffine.plainTop+(9/2:ℝ)*Cycle153.Root.floor≤1 := by
  norm_num [Cycle153Endpoint.CountAffine.plainTop,Cycle153.Root.floor]
end Cycle153Endpoint.Physical


namespace Cycle153Endpoint.Arithmetic
noncomputable section
open Cycle63.Optimization

def theta : ℝ := 8748087/10000000
def h : ℝ := 79716116522/100000000000
def lambda : ℝ := Cycle153.Consumer.lambda
def B : ℝ := Cycle153.Consumer.B
def c : ℝ := 1-theta
def q0 : ℝ := Cycle153.MarkedRootPrice.q
def rho0 : ℝ := density q0
def Ka : ℝ := amplifierRatio Cycle153.MarkedRootPrice.price Cycle153.MarkedRootPrice.intercept q0
def alpha : ℝ := lowReserveWeight
def ell : ℝ := 11/3-4*theta
def x : ℝ := 1+ell-h
def y : ℝ := h-2*ell
def kappaStar : ℝ := 2*theta-1
def dMinus : ℝ := 2*y/(lambda*Cycle153Endpoint.Physical.smallPlainCap+2-B)
def topSaving : ℝ := 1/25000000
def dPlusOffset : ℝ := topSaving/4
def rowSaving : ℝ := 1/50000000
def dPlus : ℝ := h+dPlusOffset
def d0 : ℝ := 1/200
def dampingRate : ℝ := allowanceUnit
def reserveProportion : ℝ := 2*dampingRate
def t0 : ℝ :=
  ((2*y/dMinus-1)*(1/(4*lambda)-1/18)-(1-B)/(4*lambda))/(7/18-reserveProportion)
def lowReserve : ℝ := @Cycle63.AffineLedger.lowReserve Cycle153.Root.rootLedger

theorem lambda_enclosure : lambda∈Set.Icc (374133137186239/100000000000000) (374133137186240/100000000000000) := Cycle153.Consumer.lambda_bounds
theorem B_enclosure : B∈Set.Icc (98202950630894/100000000000000) (98202950630895/100000000000000) := Cycle153.Consumer.B_bounds
alias lambda_bounds := lambda_enclosure
alias B_bounds := B_enclosure
theorem q0_enclosure : q0∈Set.Icc (127604383/200000000:ℝ) (638021915000000001/1000000000000000000:ℝ) := Cycle153.MarkedRootPrice.q_bounds
alias q0_bounds := q0_enclosure
bracket h_enclosure (digits:=12) : h unfolding [h]
alias h_bounds := h_enclosure
bracket topSaving_bounds (digits:=15) : topSaving unfolding [topSaving]
bracket dPlusOffset_bounds (digits:=15) : dPlusOffset unfolding [dPlusOffset,topSaving]
bracket rowSaving_bounds (digits:=15) : rowSaving unfolding [rowSaving]
bracket dMinus_bounds (digits:=9) : dMinus using [lambda_enclosure,B_enclosure,h_enclosure]
  unfolding [dMinus,y,ell,theta,Cycle153Endpoint.Physical.smallPlainCap,Cycle153Endpoint.CountAffine.windowBottom,Cycle153Endpoint.CountAffine.plainTop]
bracket t0_bounds (digits:=12) : t0 using [lambda_enclosure,B_enclosure,h_enclosure]
  unfolding [t0,reserveProportion,dampingRate,allowanceUnit,y,dMinus,ell,theta,Cycle153Endpoint.Physical.smallPlainCap,Cycle153Endpoint.CountAffine.windowBottom,Cycle153Endpoint.CountAffine.plainTop]
theorem topSaving_pos : 0< topSaving := by norm_num [topSaving]
theorem dPlusOffset_pos : 0< dPlusOffset := by norm_num [dPlusOffset,topSaving]
theorem rowSaving_pos : 0< rowSaving := by norm_num [rowSaving]
theorem rowSaving_add : rowSaving+2*dPlusOffset=topSaving := by norm_num [rowSaving,dPlusOffset,topSaving]

theorem ell_eq : ell = 11 / 3 - 4 * theta := rfl
theorem x_eq : x = 1 + ell - h := rfl
theorem y_eq : y = h - 2 * ell := rfl
theorem kappaStar_eq : kappaStar = 2 * theta - 1 := rfl
theorem dPlus_eq : dPlus = h + dPlusOffset := rfl

theorem ell_pos : 0 < ell := by norm_num [ell, theta]
theorem sixth_lt_ell : 1 / 6 < ell := by norm_num [ell, theta]
theorem ell_lt_fifth : ell < 1 / 5 := by norm_num [ell, theta]
theorem ell_lt_x : ell < x := by
  have := h_bounds; unfold x; linarith
theorem x_lt_y : x < y := by
  have := h_bounds; unfold x y; norm_num [ell, theta]; linarith
theorem y_le : y ≤ 19 / 40 := by
  have := h_bounds; unfold y; norm_num [ell, theta]; linarith

theorem y_lt_half : y < 1 / 2 := by
  have := h_bounds; unfold y; norm_num [ell, theta]; linarith
theorem h_lt_two_y : h < 2 * y := by
  have := h_bounds; unfold y; norm_num [ell, theta]; linarith
theorem four_ell_lt_h : 4 * ell < h := by
  have := h_bounds; norm_num [ell, theta]; linarith
theorem x_add_y : x + y = 1 - ell := by unfold x y; ring
theorem d0_pos : 0 < d0 := by norm_num [d0]
theorem dampingRate_pos : 0 < dampingRate := allowanceUnit_pos
theorem half_lt_dMinus : 1 / 2 < dMinus := by linarith [dMinus_bounds.1]
theorem dMinus_lt_h : dMinus < h := by linarith [dMinus_bounds.2, h_bounds.1]
theorem h_lt_dPlus : h < dPlus := by unfold dPlus; linarith [dPlusOffset_pos]
theorem dPlus_lt_one : dPlus < 1 := by
  have := h_bounds; have := dPlusOffset_bounds; unfold dPlus; linarith
theorem kappaStar_mem : 7 / 10 ≤ kappaStar ∧ kappaStar ≤ 3 / 4 := by
  constructor <;> norm_num [kappaStar, theta]


theorem lowReserve_le : lowReserve≤1/50 := @Cycle63.AffineLedger.lowReserve_le Cycle153.Root.rootLedger
theorem lowReserve_pos : 0< lowReserve := @Cycle63.AffineLedger.lowReserve_pos Cycle153.Root.rootLedger
theorem lambda_pos : 0< lambda := by linarith [lambda_bounds.1]
theorem q0_pos : 0< q0 := by linarith [q0_bounds.1]
theorem q0_lt : q0< slotPrice := by linarith [q0_bounds.2,slotPrice_mem.1]
end
end Cycle153Endpoint.Arithmetic
#print axioms Cycle153Endpoint.Arithmetic.dMinus_bounds
#print axioms Cycle153Endpoint.Arithmetic.t0_bounds

