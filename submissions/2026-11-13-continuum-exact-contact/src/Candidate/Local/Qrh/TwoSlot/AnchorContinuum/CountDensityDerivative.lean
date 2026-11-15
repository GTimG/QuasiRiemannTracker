/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Differentiate the admitted exact count in density and define its positive
stationary conductor cutoff. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.CriticalReturn

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section
open Qrh.TwoSlot.AnchorZeroLoss.Affine.Return

def jSlope : ℝ := -2-2*exactLine.g1
def criticalU : ℝ := ExactWindow.UI (1/2)
def densityRate (d : ℝ) : ℝ := -1+criticalU*
  ((5/6-2*d)*ExactWindow.JI d (1/2)-(5/6-d)*d*jSlope)/(ExactWindow.JI d (1/2))^2

theorem J_density_deriv (d : ℝ) :
    HasDerivAt (fun x => ExactWindow.JI x (1/2)) jSlope d := by
  have hh := (((hasDerivAt_id d).const_sub (5/6)).const_mul 3).add
    ((hasDerivAt_id d).const_mul (2*ExactWindow.kI (1/2)))
  convert hh using 1
  · funext x
    dsimp [ExactWindow.JI]
    ring
  · unfold jSlope ExactWindow.kI
    ring

theorem N_density_deriv (d : ℝ) : HasDerivAt (fun x => ExactWindow.NI x (1/2))
    (-ExactWindow.JI d (1/2)+(1-d)*jSlope+(5/6-2*d)*criticalU) d := by
  have hh := (((hasDerivAt_id d).const_sub 1).mul (J_density_deriv d)).add
    ((((hasDerivAt_id d).const_sub (5/6)).mul (hasDerivAt_id d)).const_mul criticalU)
  convert hh using 1
  · funext x
    dsimp [ExactWindow.NI,criticalU]
    ring
  · dsimp
    ring

theorem value_density_deriv {d : ℝ} (hj : ExactWindow.JI d (1/2) ≠ 0) :
    HasDerivAt (fun x => ExactWindow.valueI x (1/2)) (densityRate d) d := by
  have hh := (N_density_deriv d).div (J_density_deriv d) hj
  convert hh using 1
  · rfl
  · unfold densityRate ExactWindow.NI criticalU
    field_simp [hj]
    <;> ring

theorem critical_J_bounds : (3/2:ℝ) ≤ ExactWindow.JI density (1/2) ∧
    ExactWindow.JI density (1/2) ≤ 2 := by
  have hc := tangent_coefficient_bounds
  have hd := density_range
  have hm0 := mul_nonneg (show 0 ≤ -tangentSlope by linarith [hc.2.2.1])
    (show 0 ≤ density by linarith [hd.1])
  have hm1 := mul_nonneg (show 0 ≤ 1/10-(-tangentSlope) by linarith [hc.2.2.2])
    (show 0 ≤ density by linarith [hd.1])
  dsimp [ExactWindow.JI,ExactWindow.kI,exactLine]
  constructor <;> nlinarith [hd.1,hd.2]

theorem critical_U_bounds : 0 ≤ criticalU ∧ criticalU ≤ 1 := by
  have hc := tangent_coefficient_bounds
  dsimp [criticalU,ExactWindow.UI,exactLine]
  constructor <;> linarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

theorem jSlope_bounds : -(3:ℝ) ≤ jSlope ∧ jSlope ≤ -2 := by
  have hc := tangent_coefficient_bounds
  dsimp [jSlope,exactLine]
  constructor <;> linarith [hc.2.2.1,hc.2.2.2]

theorem densityRate_negative : densityRate density < 0 := by
  have hd := density_range
  have hj := critical_J_bounds
  have hu := critical_U_bounds
  have hs := jSlope_bounds
  have ht0 : 0 ≤ (5/6-density)*density :=
    mul_nonneg (by linarith [hd.2]) (by linarith [hd.1])
  have ht1 : (5/6-density)*density ≤ (1/4:ℝ) := by
    nlinarith [sq_nonneg (density-5/12)]
  have hm := mul_le_mul_of_nonneg_left hs.1 ht0
  have hn : (5/6-2*density)*ExactWindow.JI density (1/2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith [hd.1]) (by linarith [hj.1])
  have hb : (5/6-2*density)*ExactWindow.JI density (1/2)-
      (5/6-density)*density*jSlope ≤ (3/4:ℝ) := by nlinarith only [hm,hn,ht1]
  have hmU := mul_le_mul_of_nonneg_left hb hu.1
  have hUB : criticalU*((5/6-2*density)*ExactWindow.JI density (1/2)-
      (5/6-density)*density*jSlope) ≤ (3/4:ℝ) := by nlinarith only [hmU,hu.2]
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1)
    (show (1:ℝ) ≤ ExactWindow.JI density (1/2) by linarith [hj.1]) 2
  have hp : 0 < (ExactWindow.JI density (1/2))^2 := sq_pos_of_pos critical_denominator_pos
  have hh := (div_lt_one hp).mpr (show criticalU*((5/6-2*density)*
    ExactWindow.JI density (1/2)-(5/6-density)*density*jSlope) <
      (ExactWindow.JI density (1/2))^2 by nlinarith only [hUB,hsq])
  unfold densityRate
  linarith

def stationaryCutoff : ℝ := (1/2+ell)/(1/8-(3/4)*densityRate density)

theorem stationary_denominator_pos : 0 < (1/8:ℝ)-(3/4)*densityRate density := by
  linarith [densityRate_negative]

theorem stationaryCutoff_pos : 0 < stationaryCutoff := by
  have ht := theta_range.2
  exact div_pos (by unfold ell; linarith) stationary_denominator_pos

theorem stationary_cutoff_balance :
    stationaryCutoff*(1/8-(3/4)*densityRate density) = 1/2+ell := by
  unfold stationaryCutoff
  exact div_mul_cancel₀ _ stationary_denominator_pos.ne'

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.value_density_deriv
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.stationaryCutoff_pos
