import Mathlib

namespace OAI

noncomputable section

namespace SevenEighths.QuasiPerturbationParameters

def tau : ℝ := 1/1000000

def E : ℝ := 1/6+tau

def M : ℝ := 1-E

def lx : ℝ := 17/48-tau/2

def ly : ℝ := 23/48-tau/2

def sigma : ℝ := 7/8-tau/4

theorem tau_pos : 0<tau := by norm_num [tau]

theorem E_nonneg : 0≤E := by norm_num [E,tau]

theorem E_le_one_fifth : E≤1/5 := by norm_num [E,tau]

theorem M_add_E : M+E=1 := by norm_num [M,E,tau]

theorem source_exponents_sum : lx+ly=1-E := by
  norm_num [lx,ly,E,tau]

theorem E_lt_lx : E<lx := by
  norm_num [E,lx,tau]

theorem lx_lt_ly : lx<ly := by
  norm_num [lx,ly,tau]

theorem E_lt_two_lx_sub_ly : E<2*lx-ly := by
  norm_num [E,lx,ly,tau]

theorem gram_exponent_exact :
    lx/2+(ly-lx)/12=3/16-tau/4 := by
  norm_num [lx,ly,tau]

theorem gram_exponent_eq_sigma :
    lx/2+(ly-lx)/12=sigma-11/16 := by
  norm_num [lx,ly,sigma,tau]

theorem sigma_exact : sigma=(3499999:ℝ)/4000000 := by
  norm_num [sigma,tau]

theorem sigma_lt_seven_eighths : sigma<7/8 := by
  norm_num [sigma,tau]

end SevenEighths.QuasiPerturbationParameters

end

end OAI
