/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional

/- BEGIN ORIGINAL Cycle61.Arithmetic.Constants; sha256 8634ec692170f496a80bb682dc582b4d62e99acdf4fe0f4df055df7bfecadc04 -/
section
                               
                             

namespace Cycle61.Arithmetic

noncomputable section

def theta : ℝ := 4374299 / 5000000
def c : ℝ := 625701 / 5000000
def h : ℝ := 3969737987 / 5000000000
def ell : ℝ := 627103 / 3750000
def x : ℝ := 5599198039 / 15000000000
def y : ℝ := 6892389961 / 15000000000
def kappaStar : ℝ := 1874299 / 2500000
def dMinus : ℝ := 3964737987 / 5000000000
def dPlus : ℝ := 317579039 / 400000000
def d0 : ℝ := 1 / 200
def lambda : ℝ := 16281 / 4106
def B : ℝ := 202497947 / 205300000
def B0 : ℝ := 2025 / 2053
def q0 : ℝ := 67 / 100
def rho0 : ℝ := 214 / 549
def Ka : ℝ := 67 / 48
def alpha : ℝ := 1 / 400000
def t0 : ℝ := 1 / 1000

theorem theta_eq : theta = 1 - c := by norm_num [theta, c]
theorem ell_eq : ell = 11 / 3 - 4 * theta := by norm_num [ell, theta]
theorem x_eq : x = 1 + ell - h := by norm_num [x, ell, h]
theorem y_eq : y = h - 2 * ell := by norm_num [y, ell, h]
theorem kappaStar_eq : kappaStar = 2 * theta - 1 := by norm_num [kappaStar, theta]
theorem dMinus_eq : dMinus = h - 1 / 1000 := by norm_num [dMinus, h]
theorem dPlus_eq : dPlus = h + 1 / 10000000000 := by norm_num [dPlus, h]
theorem B_eq : B = B0 - 1 / 100000 := by norm_num [B, B0]

theorem ell_pos : 0 < ell := by norm_num [ell]
theorem ell_lt_x : ell < x := by norm_num [ell, x]
theorem x_lt_y : x < y := by norm_num [x, y]
theorem y_lt_two_x : y < 2 * x := by norm_num [y, x]
theorem y_lt_half : y < 1 / 2 := by norm_num [y]
theorem half_lt_h : 1 / 2 < h := by norm_num [h]
theorem h_lt_two_y : h < 2 * y := by norm_num [h, y]
theorem sixth_lt_ell : 1 / 6 < ell := by norm_num [ell]
theorem ell_lt_fifth : ell < 1 / 5 := by norm_num [ell]
theorem four_ell_lt_h : 4 * ell < h := by norm_num [ell, h]
theorem x_add_y : x + y = 1 - ell := by norm_num [x, y, ell]
theorem d0_pos : 0 < d0 := by norm_num [d0]
theorem half_lt_dMinus : 1 / 2 < dMinus := by norm_num [dMinus]
theorem dMinus_lt_h : dMinus < h := by norm_num [dMinus, h]
theorem h_lt_dPlus : h < dPlus := by norm_num [h, dPlus]
theorem dPlus_lt_one : dPlus < 1 := by norm_num [dPlus]
theorem kappaStar_mem : 7 / 10 ≤ kappaStar ∧ kappaStar ≤ 3 / 4 := by
  norm_num [kappaStar]
theorem alpha_pos : 0 < alpha := by norm_num [alpha]
theorem lambda_pos : 0 < lambda := by norm_num [lambda]
theorem B_pos : 0 < B := by norm_num [B]

end

end Cycle61.Arithmetic

end
/- END ORIGINAL Cycle61.Arithmetic.Constants -/

/- BEGIN ORIGINAL Cycle61.Arithmetic.LocalReserves; sha256 47090ea113190f16dcc86937f5b09c1ebec25d46e3edaace753e10db3489888a -/
section
                                   
                              
                          

namespace Cycle61.Arithmetic

noncomputable section

def g (b : ℝ) : ℝ := B - 1 + (9 / 2 - lambda) * b
def amp (b : ℝ) : ℝ := Ka * g b + alpha
-- The lower edge is one mesh step below the cell's upper edge.
def totalA (b : ℝ) : ℝ := B - (lambda - 1) * (b - 1 / 100000)
def cellUpper (j : ℕ) : ℝ := 17 / 500 + (j : ℝ) / 100000

theorem cellUpper_bounds {j : ℕ} (hj1 : 1 ≤ j) (hj600 : j ≤ 600) :
    3401 / 100000 ≤ cellUpper j ∧ cellUpper j ≤ 1 / 25 := by
  have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have h600 : (j : ℝ) ≤ (600 : ℝ) := by exact_mod_cast hj600
  constructor <;> unfold cellUpper <;> linarith

theorem g_bounds {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    186449/41060000 ≤ g b ∧ g b ≤ 1589947/205300000 := by
  constructor <;> norm_num [g, B, lambda] at * <;> linarith

theorem g_pos {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    0 < g b := by
  have hg := (g_bounds hb).1
  linarith

theorem amp_bounds {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    62485051/9854400000 ≤ amp b ∧ amp b ≤ 21310217/1970880000 := by
  constructor <;> norm_num [amp, g, Ka, alpha, B, lambda] at * <;> linarith

theorem totalA_upper {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    totalA b ≤ 181800447/205300000 := by
  norm_num [totalA, B, lambda] at *
  linarith

theorem amp_pos {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    0 < amp b := by
  have ha := (amp_bounds hb).1
  linarith

theorem low_reserve (b : ℝ) :
    amp b * (1 - 4 * q0 / 3) - (2 * q0 / 9) * g b = 1/3750000 := by
  norm_num [amp, g, Ka, alpha, B, lambda, q0]
  ring

theorem high_slope_cancellation :
    q0 * (lambda - 1) = Ka * (5 - 6 * rho0) * (9 / 2 - lambda) := by
  norm_num [q0, lambda, Ka, rho0]

theorem high_reserve (b : ℝ) :
    1 - rho0 - q0 * totalA b - amp b * (5 - 6 * rho0) =
      781136071/45083880000000 := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda, q0, rho0]
  ring

theorem first_error_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    32653211/39417600000 ≤ amp b / 4 - g b / 6 := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda] at *
  linarith

theorem sixth_error_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    782473823/39417600000 ≤ 13 * amp b / 4 - g b / 6 := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda] at *
  linarith

theorem seventh_error_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    60620561/2463600000 ≤ 4 * amp b - g b / 6 := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda] at *
  linarith

theorem second_zero_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    770250919/9854400000 ≤ 1 - totalA b - 5 * amp b := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda] at *
  linarith

theorem main_fixed_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    219200501/2463600000 ≤ 1 - totalA b - 4 * amp b := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda] at *
  linarith

theorem error_fixed_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    114682193/3284800000 ≤ 1 - totalA b - 9 * amp b := by
  norm_num [totalA, amp, g, Ka, alpha, B, lambda] at *
  linarith

theorem support_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    343548481/1970880000 ≤ 1 / 4 - 7 * amp b := by
  have ha := (amp_bounds hb).2
  linarith

theorem high_derivative_reserve {b : ℝ} (hb : 3401 / 100000 ≤ b ∧ b ≤ 1 / 25) :
    2866346894063/10312937550000 ≤
      50 * (1 - 6 * amp b) / (3 * (5 - 2 * q0) ^ 2) - totalA b := by
  have ha := (amp_bounds hb).2
  have hA := totalA_upper hb
  norm_num [q0] at *
  linarith

theorem cell_terminal_reserves {j : ℕ} (hj1 : 1 ≤ j) (hj600 : j ≤ 600) :
    0 < amp (cellUpper j) * (1 - 4 * q0 / 3) - (2 * q0 / 9) * g (cellUpper j) ∧
    0 < 1 - rho0 - q0 * totalA (cellUpper j) - amp (cellUpper j) * (5 - 6 * rho0) ∧
    0 < amp (cellUpper j) / 4 - g (cellUpper j) / 6 ∧
    0 < 13 * amp (cellUpper j) / 4 - g (cellUpper j) / 6 ∧
    0 < 4 * amp (cellUpper j) - g (cellUpper j) / 6 ∧
    0 < 1 - totalA (cellUpper j) - 5 * amp (cellUpper j) ∧
    0 < 1 - totalA (cellUpper j) - 4 * amp (cellUpper j) ∧
    0 < 1 - totalA (cellUpper j) - 9 * amp (cellUpper j) := by
  have hb := cellUpper_bounds hj1 hj600
  have hl := low_reserve (cellUpper j)
  have hh := high_reserve (cellUpper j)
  have h1 := first_error_reserve hb
  have h6 := sixth_error_reserve hb
  have h7 := seventh_error_reserve hb
  have hz := second_zero_reserve hb
  have hm := main_fixed_reserve hb
  have he := error_fixed_reserve hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem comparison_budget :
    (1 : ℝ) / 4 + 1 / 2 + (9 / 2) * (1 / 25) = 93 / 100 := by norm_num

theorem small_slot_complement :
    (2 : ℝ) * (264 / 625) + (9 / 2) * (17 / 500) = 1 - 11 / 5000 := by norm_num

theorem small_plain_complement :
    (41 : ℝ) / 100 + 264 / 625 + (9 / 2) * (37 / 1000) =
      1 - 11 / 10000 := by norm_num

theorem supply_lower :
    ell / dPlus - 4 / 21 = 44798188/2223053273 := by norm_num [ell, dPlus]

theorem supply_half :
    2 * ell - 1 / 3 = 701/625000 := by norm_num [ell]

theorem supply_four :
    4 * ell - y = 1047086013/5000000000 := by norm_num [ell, y]

theorem lower_row_reserve :
    theta - (7 / 8 - 49 * h / 150 + 7 * ell / 8 + 33 * d0 / 50) =
      82193986363/750000000000 := by norm_num [theta, h, ell, d0]

theorem floor_reserve :
    theta - (51 / 100 + h / 3 + 51 * ell / 100) =
      223868893/15000000000 := by norm_num [theta, h, ell]

theorem new_feedback_bound :
    5 * dPlus / 288 = 317579039 / 23040000000 ∧
      5 * dPlus / 288 < 1 / 50 := by norm_num [dPlus]

theorem old_feedback_bound : (695 : ℝ) / 14112 < 1 / 8 := by norm_num

theorem endpoint_extension_saving :
    (1 : ℝ) / 1000000 - 2 * (dPlus - h) = 4999 / 5000000000 := by
  norm_num [dPlus, h]

theorem principal_y_reserve :
    y / 20 - (1 + h) / 1000 - 1 / 4000 =
      313960284089/15000000000000 := by norm_num [y, h]

theorem principal_h_reserve :
    h / 600 - 1 / 1000 - 1 / 4000 =
      219737987 / 3000000000000 := by norm_num [h]

end

end Cycle61.Arithmetic


end
/- END ORIGINAL Cycle61.Arithmetic.LocalReserves -/

/- BEGIN ORIGINAL Cycle61.Assembly.Geometry; sha256 4bb6b6db323fbd4397b399850bc2e4ed07f66f01c491daacb9d644612e2b2579 -/
section
                                       

/-! Physical probe geometry at the exact rational Cycle61 boundary. -/
namespace Cycle61.Assembly
noncomputable section
open Arithmetic

def signalShift : ℝ := -(5/6-x/3-ell/6)
def signal (s : ℝ) : ℝ := s+signalShift

theorem theta_gt_half : (1/2 : ℝ) < theta := by norm_num [theta]
theorem theta_lt_seven_eighths : theta < (7/8 : ℝ) := by norm_num [theta]
theorem theta_lt_one : theta < 1 := by norm_num [theta]

theorem signalShift_eq : signalShift = -(4+(y-x))/6 := by
  unfold signalShift
  linarith [x_add_y]

theorem signal_at_boundary : signal theta = x/2+(y-x)/12 := by
  unfold signal signalShift
  linarith [ell_eq, x_add_y]

theorem signal_slope (s t : ℝ) : signal s-signal t = s-t := by
  unfold signal
  ring

theorem row_endpoint : h = 1-x+ell := by linarith [x_eq]

theorem marked_tuple_margin :
    1+3*ell-2*(x+y) = -(122897/750000 : ℝ) := by
  norm_num [ell, x, y]

theorem marked_short_margin :
    y-2*x+ell = -(599198039/5000000000 : ℝ) := by
  norm_num [ell, x, y]

theorem marked_subset_decreases {v : ℝ} (hv : 0 ≤ v) :
    -v+max 0 (1+3*ell-2*(x+y)+v)/8 ≤ 0 := by
  have hnegative : 1+3*ell-2*(x+y) < 0 := by
    rw [marked_tuple_margin]
    norm_num
  have hm : max 0 (1+3*ell-2*(x+y)+v) ≤ 8*v :=
    max_le (by linarith) (by linarith)
  linarith

theorem principal_remainders_positive : 0 < y/4 ∧ 0 < h/24 := by
  norm_num [y, h]

end
end Cycle61.Assembly

end
/- END ORIGINAL Cycle61.Assembly.Geometry -/

/- BEGIN ORIGINAL Cycle61.Assembly.Final.Baseline; sha256 e63816008b91366585a1a2699435d832ebd2669cabee4d78e4c6e622cfdf278c -/
section
                                                                      
                                

set_option autoImplicit false
namespace Cycle61.FinalAssembly
open OAI.SevenEighths

theorem baseline_beta : HeckeZeroSupremum.beta≤(7/8:ℝ) :=
  HeckeCommonProbe.beta_le_seven_eighths
    (ProbeFinalAssembly.common_probe_of_chosen_moments
      (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified
        ProbeFinalAssemblyUnconditional.detector_certified_bands))

theorem moment_parameter_gates (hβ : Arithmetic.theta<HeckeZeroSupremum.beta) :
    (7/10:ℝ)≤2*HeckeZeroSupremum.beta-1 ∧
      2*HeckeZeroSupremum.beta-1≤(3/4:ℝ) ∧ (51/100:ℝ)≤HeckeZeroSupremum.beta := by
  have ht : (85/100:ℝ)<Arithmetic.theta := by norm_num [Arithmetic.theta]
  have hi:=baseline_beta
  constructor
  · linarith
  constructor <;> linarith
end Cycle61.FinalAssembly

end
/- END ORIGINAL Cycle61.Assembly.Final.Baseline -/
