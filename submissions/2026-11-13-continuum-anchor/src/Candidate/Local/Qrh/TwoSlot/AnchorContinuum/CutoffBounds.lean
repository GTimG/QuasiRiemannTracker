/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Rational enclosure of the stationary cutoff from exact coefficient and
density bounds. All products retain their signs explicitly. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.StationaryReturn

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Qrh.TwoSlot.AnchorContinuum.Contact
noncomputable section
open Qrh.TwoSlot.AnchorZeroLoss.Affine.Return

theorem critical_J_sharp : (7917/5000:ℝ) ≤ ExactWindow.JI density (1/2) ∧
    ExactWindow.JI density (1/2) ≤ 7919/5000 := by
  have hc := tangent_coefficient_bounds
  have hd := density_range
  have hm0 := mul_le_mul hc.2.2.1.le hd.1.le (by norm_num : (0:ℝ) ≤ 2129/5000)
    (show 0 ≤ -tangentSlope by linarith [hc.2.2.1])
  have hm1 := mul_le_mul hc.2.2.2.le hd.2.le (show 0 ≤ density by linarith [hd.1])
    (by norm_num : (0:ℝ) ≤ 379981/5000000)
  dsimp [ExactWindow.JI,ExactWindow.kI,exactLine]
  constructor <;> nlinarith [hd.1,hd.2]

theorem critical_U_sharp : (2389/5000:ℝ) ≤ criticalU ∧ criticalU ≤ 4779/10000 := by
  have hc := tangent_coefficient_bounds
  dsimp [criticalU,ExactWindow.UI,exactLine]
  constructor <;> linarith [hc.1,hc.2.1,hc.2.2.1,hc.2.2.2]

theorem negative_jSlope_sharp : (21519/10000:ℝ) ≤ -jSlope ∧ -jSlope ≤ 269/125 := by
  have hc := tangent_coefficient_bounds
  dsimp [jSlope,exactLine]
  constructor <;> linarith [hc.2.2.1,hc.2.2.2]

theorem density_product_bounds : (347/2000:ℝ) ≤ (5/6-density)*density ∧
    (5/6-density)*density ≤ 217/1250 := by
  have hd := density_range
  have hm0 := mul_nonneg (show 0 ≤ 4259/10000-density by linarith [hd.2])
    (show 0 ≤ density+4259/10000-5/6 by linarith [hd.1])
  have hm1 := mul_nonneg (show 0 ≤ density-2129/5000 by linarith [hd.1])
    (show 0 ≤ density+2129/5000-5/6 by linarith [hd.1])
  constructor <;> nlinarith only [hm0,hm1]

def rateNumerator : ℝ :=
  (5/6-2*density)*ExactWindow.JI density (1/2)-(5/6-density)*density*jSlope

theorem rateNumerator_bounds : (344107/1000000:ℝ) ≤ rateNumerator ∧
    rateNumerator ≤ 43083/125000 := by
  have hd := density_range
  have hj := critical_J_sharp
  have hs := negative_jSlope_sharp
  have ht := density_product_bounds
  have ha0 : (137/7500:ℝ) ≤ 2*density-5/6 := by linarith [hd.1]
  have ha1 : 2*density-5/6 ≤ (277/15000:ℝ) := by linarith [hd.2]
  have hm0 := mul_le_mul ha0 hj.1 (by norm_num : (0:ℝ) ≤ 7917/5000)
    (show 0 ≤ 2*density-5/6 by linarith)
  have hm1 := mul_le_mul ha1 hj.2 (show 0 ≤ ExactWindow.JI density (1/2) by linarith [hj.1])
    (by norm_num : (0:ℝ) ≤ 277/15000)
  have hn0 := mul_le_mul ht.1 hs.1 (by norm_num : (0:ℝ) ≤ 21519/10000)
    (show 0 ≤ (5/6-density)*density by linarith [ht.1])
  have hn1 := mul_le_mul ht.2 hs.2 (show 0 ≤ -jSlope by linarith [hs.1])
    (by norm_num : (0:ℝ) ≤ 217/1250)
  unfold rateNumerator
  constructor <;> nlinarith only [hm0,hm1,hn0,hn1]

theorem densityRate_bounds : -(1869/2000:ℝ) ≤ densityRate density ∧
    densityRate density ≤ -(9343/10000:ℝ) := by
  have hu := critical_U_sharp
  have hb := rateNumerator_bounds
  have hj := critical_J_sharp
  have hm0 := mul_le_mul hu.1 hb.1 (by norm_num : (0:ℝ) ≤ 344107/1000000)
    (show 0 ≤ criticalU by linarith [hu.1])
  have hm1 := mul_le_mul hu.2 hb.2 (show 0 ≤ rateNumerator by linarith [hb.1])
    (by norm_num : (0:ℝ) ≤ 4779/10000)
  have hsq0 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 7917/5000) hj.1 2
  have hsq1 := pow_le_pow_left₀ (show 0 ≤ ExactWindow.JI density (1/2) by linarith [hj.1]) hj.2 2
  have hp : 0 < (ExactWindow.JI density (1/2))^2 := sq_pos_of_pos critical_denominator_pos
  have hl : (131/2000:ℝ) ≤ criticalU*rateNumerator/(ExactWindow.JI density (1/2))^2 :=
    (le_div_iff₀ hp).mpr (by nlinarith only [hm0,hsq1])
  have hh : criticalU*rateNumerator/(ExactWindow.JI density (1/2))^2 ≤ (657/10000:ℝ) :=
    (div_le_iff₀ hp).mpr (by nlinarith only [hm1,hsq0])
  change _ ≤ -1+criticalU*rateNumerator/(ExactWindow.JI density (1/2))^2 ∧
    -1+criticalU*rateNumerator/(ExactWindow.JI density (1/2))^2 ≤ _
  constructor <;> linarith

theorem ell_bounds : (2166/12500:ℝ) < ell ∧ ell < 17329/100000 := by
  have ht := theta_isolated
  unfold ell
  norm_num [lower,upper] at ht
  constructor <;> linarith [ht.1,ht.2]

theorem stationaryCutoff_bounds : (163/200:ℝ) < stationaryCutoff ∧
    stationaryCutoff < 102/125 := by
  have hr := densityRate_bounds
  have he := ell_bounds
  unfold stationaryCutoff
  constructor
  · apply (lt_div_iff₀ stationary_denominator_pos).mpr
    linarith [hr.1,he.1]
  · apply (div_lt_iff₀ stationary_denominator_pos).mpr
    linarith [hr.2,he.2]

theorem stationaryCutoff_tight : (1019/1250:ℝ) < stationaryCutoff ∧
    stationaryCutoff < 4077/5000 := by
  have hr := densityRate_bounds
  have he := ell_bounds
  unfold stationaryCutoff
  constructor
  · apply (lt_div_iff₀ stationary_denominator_pos).mpr
    linarith [hr.1,he.1]
  · apply (div_lt_iff₀ stationary_denominator_pos).mpr
    linarith [hr.2,he.2]

/-- The residual capacity, rather than the physical cap, is active at the
top conductor of the limiting geometry. -/
theorem critical_capacity_active :
    0 < (stationaryCutoff-4*ell)/2 ∧
    (stationaryCutoff-4*ell)/2 < (3/40)*stationaryCutoff := by
  have hh := stationaryCutoff_tight
  have he := ell_bounds
  constructor <;> linarith [hh.1,hh.2,he.1,he.2]

end
end Qrh.TwoSlot.AnchorContinuum.Contact
#print axioms Qrh.TwoSlot.AnchorContinuum.Contact.stationaryCutoff_bounds
