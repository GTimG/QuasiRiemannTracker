/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109Admission.Coverage
set_option autoImplicit false
namespace Record12518109Admission
noncomputable section

theorem raw_nominal_balance (c : Cell) (b : ℝ) (hden : scheduleDenominator c ≠ 0) :
 omega*rawGain c b-(1-omega)*naturalDelta c b=lowFee := by
 have hbalance : omega*rawGain c b-(1-omega)*naturalDelta c b=
     scheduleDenominator c*amplifier c b-c.q*(Qmix c*plainCap c b+b-Pmix c) := by
  unfold rawGain naturalDelta nominalRadius scheduleDenominator Pmix Qmix
  norm_num [K, incumbent, div_eq_mul_inv]
  ring
 rw [hbalance]
 have ha : scheduleDenominator c*amplifier c b=
     c.q*(Qmix c*plainCap c b+b-Pmix c)+lowFee := by
  unfold amplifier
  field_simp [hden]
 rw [ha]
 ring

def paddedLowBalance (c : Cell) (b : ℝ) : ℝ :=
 omega*(rawGain c b-c.q*c.priorB/c.priorL*pad)-
 (1-omega)*(naturalDelta c b+c.q/K*pad)-pad

theorem raw_padded_balance (c : Cell) (b : ℝ) (hden : scheduleDenominator c ≠ 0) :
 paddedLowBalance c b=ordinary c 5 b := by
 have hn := raw_nominal_balance c b hden
 dsimp only [paddedLowBalance, ordinary, Pmix]
 simp only [div_eq_mul_inv]
 linear_combination hn

theorem seed_nominal_balance (b : ℝ) :
 seedA b-seedQ*(seedD b+6*seedA b)/K=lowFee := by
 norm_num [seedA, seedD, seedQ, seedB, seedL, K, incumbent, lowFee]
 ring
theorem cell0_parameter_bounds : 31/50 ≤ cell0.q ∧ cell0.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell0.tinyRadius ∧ cell0.tinyRadius ≤ 1/25 ∧ 1 < cell0.L ∧ 1 < cell0.priorL ∧
 1/4 ≤ cell0.plainLo ∧ 1/4 ≤ cell0.priorPlainLo ∧ 0 < cell0.cut ∧ 0 < cell0.lo ∧ cell0.lo < cell0.hi := by
 norm_num [cell0, incumbent]
theorem cell0_denominator_pos : 0 < scheduleDenominator cell0 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell0]
theorem cell0_nominal_balance (b : ℝ) :
 omega*rawGain cell0 b-(1-omega)*naturalDelta cell0 b=lowFee :=
 raw_nominal_balance cell0 b (ne_of_gt cell0_denominator_pos)
theorem cell0_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (39/2000) (3/125)) :
 0 < paddedLowBalance cell0 b := by
 rw [raw_padded_balance cell0 b (ne_of_gt cell0_denominator_pos)]
 exact cell0_ordinary5 (ν := (357/500:ℝ)) hb (by norm_num)
theorem cell1_parameter_bounds : 31/50 ≤ cell1.q ∧ cell1.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell1.tinyRadius ∧ cell1.tinyRadius ≤ 1/25 ∧ 1 < cell1.L ∧ 1 < cell1.priorL ∧
 1/4 ≤ cell1.plainLo ∧ 1/4 ≤ cell1.priorPlainLo ∧ 0 < cell1.cut ∧ 0 < cell1.lo ∧ cell1.lo < cell1.hi := by
 norm_num [cell1, incumbent]
theorem cell1_denominator_pos : 0 < scheduleDenominator cell1 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell1]
theorem cell1_nominal_balance (b : ℝ) :
 omega*rawGain cell1 b-(1-omega)*naturalDelta cell1 b=lowFee :=
 raw_nominal_balance cell1 b (ne_of_gt cell1_denominator_pos)
theorem cell1_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (49/2000) (7/200)) :
 0 < paddedLowBalance cell1 b := by
 rw [raw_padded_balance cell1 b (ne_of_gt cell1_denominator_pos)]
 exact cell1_ordinary5 (ν := (429/625:ℝ)) hb (by norm_num)
theorem cell2_parameter_bounds : 31/50 ≤ cell2.q ∧ cell2.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell2.tinyRadius ∧ cell2.tinyRadius ≤ 1/25 ∧ 1 < cell2.L ∧ 1 < cell2.priorL ∧
 1/4 ≤ cell2.plainLo ∧ 1/4 ≤ cell2.priorPlainLo ∧ 0 < cell2.cut ∧ 0 < cell2.lo ∧ cell2.lo < cell2.hi := by
 norm_num [cell2, incumbent]
theorem cell2_denominator_pos : 0 < scheduleDenominator cell2 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell2]
theorem cell2_nominal_balance (b : ℝ) :
 omega*rawGain cell2 b-(1-omega)*naturalDelta cell2 b=lowFee :=
 raw_nominal_balance cell2 b (ne_of_gt cell2_denominator_pos)
theorem cell2_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (17/500) (9/250)) :
 0 < paddedLowBalance cell2 b := by
 rw [raw_padded_balance cell2 b (ne_of_gt cell2_denominator_pos)]
 exact cell2_ordinary5 (ν := (399/625:ℝ)) hb (by norm_num)
theorem cell3_parameter_bounds : 31/50 ≤ cell3.q ∧ cell3.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell3.tinyRadius ∧ cell3.tinyRadius ≤ 1/25 ∧ 1 < cell3.L ∧ 1 < cell3.priorL ∧
 1/4 ≤ cell3.plainLo ∧ 1/4 ≤ cell3.priorPlainLo ∧ 0 < cell3.cut ∧ 0 < cell3.lo ∧ cell3.lo < cell3.hi := by
 norm_num [cell3, incumbent]
theorem cell3_denominator_pos : 0 < scheduleDenominator cell3 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell3]
theorem cell3_nominal_balance (b : ℝ) :
 omega*rawGain cell3 b-(1-omega)*naturalDelta cell3 b=lowFee :=
 raw_nominal_balance cell3 b (ne_of_gt cell3_denominator_pos)
theorem cell3_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (9/250) (3/80)) :
 0 < paddedLowBalance cell3 b := by
 rw [raw_padded_balance cell3 b (ne_of_gt cell3_denominator_pos)]
 exact cell3_ordinary5 (ν := (1589/2500:ℝ)) hb (by norm_num)
theorem cell4_parameter_bounds : 31/50 ≤ cell4.q ∧ cell4.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell4.tinyRadius ∧ cell4.tinyRadius ≤ 1/25 ∧ 1 < cell4.L ∧ 1 < cell4.priorL ∧
 1/4 ≤ cell4.plainLo ∧ 1/4 ≤ cell4.priorPlainLo ∧ 0 < cell4.cut ∧ 0 < cell4.lo ∧ cell4.lo < cell4.hi := by
 norm_num [cell4, incumbent]
theorem cell4_denominator_pos : 0 < scheduleDenominator cell4 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell4]
theorem cell4_nominal_balance (b : ℝ) :
 omega*rawGain cell4 b-(1-omega)*naturalDelta cell4 b=lowFee :=
 raw_nominal_balance cell4 b (ne_of_gt cell4_denominator_pos)
theorem cell4_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (3/80) (39/1000)) :
 0 < paddedLowBalance cell4 b := by
 rw [raw_padded_balance cell4 b (ne_of_gt cell4_denominator_pos)]
 exact cell4_ordinary5 (ν := (1271/2000:ℝ)) hb (by norm_num)
theorem cell5_parameter_bounds : 31/50 ≤ cell5.q ∧ cell5.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell5.tinyRadius ∧ cell5.tinyRadius ≤ 1/25 ∧ 1 < cell5.L ∧ 1 < cell5.priorL ∧
 1/4 ≤ cell5.plainLo ∧ 1/4 ≤ cell5.priorPlainLo ∧ 0 < cell5.cut ∧ 0 < cell5.lo ∧ cell5.lo < cell5.hi := by
 norm_num [cell5, incumbent]
theorem cell5_denominator_pos : 0 < scheduleDenominator cell5 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell5]
theorem cell5_nominal_balance (b : ℝ) :
 omega*rawGain cell5 b-(1-omega)*naturalDelta cell5 b=lowFee :=
 raw_nominal_balance cell5 b (ne_of_gt cell5_denominator_pos)
theorem cell5_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (39/1000) (1/25)) :
 0 < paddedLowBalance cell5 b := by
 rw [raw_padded_balance cell5 b (ne_of_gt cell5_denominator_pos)]
 exact cell5_ordinary5 (ν := (627/1000:ℝ)) hb (by norm_num)
theorem cell6_parameter_bounds : 31/50 ≤ cell6.q ∧ cell6.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell6.tinyRadius ∧ cell6.tinyRadius ≤ 1/25 ∧ 1 < cell6.L ∧ 1 < cell6.priorL ∧
 1/4 ≤ cell6.plainLo ∧ 1/4 ≤ cell6.priorPlainLo ∧ 0 < cell6.cut ∧ 0 < cell6.lo ∧ cell6.lo < cell6.hi := by
 norm_num [cell6, incumbent]
theorem cell6_denominator_pos : 0 < scheduleDenominator cell6 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell6]
theorem cell6_nominal_balance (b : ℝ) :
 omega*rawGain cell6 b-(1-omega)*naturalDelta cell6 b=lowFee :=
 raw_nominal_balance cell6 b (ne_of_gt cell6_denominator_pos)
theorem cell6_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (17/500) (9/250)) :
 0 < paddedLowBalance cell6 b := by
 rw [raw_padded_balance cell6 b (ne_of_gt cell6_denominator_pos)]
 exact cell6_ordinary5 (ν := (1289/2000:ℝ)) hb (by norm_num)
theorem cell7_parameter_bounds : 31/50 ≤ cell7.q ∧ cell7.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell7.tinyRadius ∧ cell7.tinyRadius ≤ 1/25 ∧ 1 < cell7.L ∧ 1 < cell7.priorL ∧
 1/4 ≤ cell7.plainLo ∧ 1/4 ≤ cell7.priorPlainLo ∧ 0 < cell7.cut ∧ 0 < cell7.lo ∧ cell7.lo < cell7.hi := by
 norm_num [cell7, incumbent]
theorem cell7_denominator_pos : 0 < scheduleDenominator cell7 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell7]
theorem cell7_nominal_balance (b : ℝ) :
 omega*rawGain cell7 b-(1-omega)*naturalDelta cell7 b=lowFee :=
 raw_nominal_balance cell7 b (ne_of_gt cell7_denominator_pos)
theorem cell7_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (9/250) (3/80)) :
 0 < paddedLowBalance cell7 b := by
 rw [raw_padded_balance cell7 b (ne_of_gt cell7_denominator_pos)]
 exact cell7_ordinary5 (ν := (1587/2500:ℝ)) hb (by norm_num)
theorem cell8_parameter_bounds : 31/50 ≤ cell8.q ∧ cell8.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell8.tinyRadius ∧ cell8.tinyRadius ≤ 1/25 ∧ 1 < cell8.L ∧ 1 < cell8.priorL ∧
 1/4 ≤ cell8.plainLo ∧ 1/4 ≤ cell8.priorPlainLo ∧ 0 < cell8.cut ∧ 0 < cell8.lo ∧ cell8.lo < cell8.hi := by
 norm_num [cell8, incumbent]
theorem cell8_denominator_pos : 0 < scheduleDenominator cell8 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell8]
theorem cell8_nominal_balance (b : ℝ) :
 omega*rawGain cell8 b-(1-omega)*naturalDelta cell8 b=lowFee :=
 raw_nominal_balance cell8 b (ne_of_gt cell8_denominator_pos)
theorem cell8_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (3/80) (39/1000)) :
 0 < paddedLowBalance cell8 b := by
 rw [raw_padded_balance cell8 b (ne_of_gt cell8_denominator_pos)]
 exact cell8_ordinary5 (ν := (6287/10000:ℝ)) hb (by norm_num)
theorem cell9_parameter_bounds : 31/50 ≤ cell9.q ∧ cell9.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell9.tinyRadius ∧ cell9.tinyRadius ≤ 1/25 ∧ 1 < cell9.L ∧ 1 < cell9.priorL ∧
 1/4 ≤ cell9.plainLo ∧ 1/4 ≤ cell9.priorPlainLo ∧ 0 < cell9.cut ∧ 0 < cell9.lo ∧ cell9.lo < cell9.hi := by
 norm_num [cell9, incumbent]
theorem cell9_denominator_pos : 0 < scheduleDenominator cell9 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell9]
theorem cell9_nominal_balance (b : ℝ) :
 omega*rawGain cell9 b-(1-omega)*naturalDelta cell9 b=lowFee :=
 raw_nominal_balance cell9 b (ne_of_gt cell9_denominator_pos)
theorem cell9_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (39/1000) (1/25)) :
 0 < paddedLowBalance cell9 b := by
 rw [raw_padded_balance cell9 b (ne_of_gt cell9_denominator_pos)]
 exact cell9_ordinary5 (ν := (3129/5000:ℝ)) hb (by norm_num)
theorem cell10_parameter_bounds : 31/50 ≤ cell10.q ∧ cell10.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell10.tinyRadius ∧ cell10.tinyRadius ≤ 1/25 ∧ 1 < cell10.L ∧ 1 < cell10.priorL ∧
 1/4 ≤ cell10.plainLo ∧ 1/4 ≤ cell10.priorPlainLo ∧ 0 < cell10.cut ∧ 0 < cell10.lo ∧ cell10.lo < cell10.hi := by
 norm_num [cell10, incumbent]
theorem cell10_denominator_pos : 0 < scheduleDenominator cell10 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell10]
theorem cell10_nominal_balance (b : ℝ) :
 omega*rawGain cell10 b-(1-omega)*naturalDelta cell10 b=lowFee :=
 raw_nominal_balance cell10 b (ne_of_gt cell10_denominator_pos)
theorem cell10_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (1/25) (81/2000)) :
 0 < paddedLowBalance cell10 b := by
 rw [raw_padded_balance cell10 b (ne_of_gt cell10_denominator_pos)]
 exact cell10_ordinary5 (ν := (6239/10000:ℝ)) hb (by norm_num)
theorem cell11_parameter_bounds : 31/50 ≤ cell11.q ∧ cell11.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell11.tinyRadius ∧ cell11.tinyRadius ≤ 1/25 ∧ 1 < cell11.L ∧ 1 < cell11.priorL ∧
 1/4 ≤ cell11.plainLo ∧ 1/4 ≤ cell11.priorPlainLo ∧ 0 < cell11.cut ∧ 0 < cell11.lo ∧ cell11.lo < cell11.hi := by
 norm_num [cell11, incumbent]
theorem cell11_denominator_pos : 0 < scheduleDenominator cell11 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell11]
theorem cell11_nominal_balance (b : ℝ) :
 omega*rawGain cell11 b-(1-omega)*naturalDelta cell11 b=lowFee :=
 raw_nominal_balance cell11 b (ne_of_gt cell11_denominator_pos)
theorem cell11_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (81/2000) (41/1000)) :
 0 < paddedLowBalance cell11 b := by
 rw [raw_padded_balance cell11 b (ne_of_gt cell11_denominator_pos)]
 exact cell11_ordinary5 (ν := (6217/10000:ℝ)) hb (by norm_num)
theorem cell12_parameter_bounds : 31/50 ≤ cell12.q ∧ cell12.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell12.tinyRadius ∧ cell12.tinyRadius ≤ 1/25 ∧ 1 < cell12.L ∧ 1 < cell12.priorL ∧
 1/4 ≤ cell12.plainLo ∧ 1/4 ≤ cell12.priorPlainLo ∧ 0 < cell12.cut ∧ 0 < cell12.lo ∧ cell12.lo < cell12.hi := by
 norm_num [cell12, incumbent]
theorem cell12_denominator_pos : 0 < scheduleDenominator cell12 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell12]
theorem cell12_nominal_balance (b : ℝ) :
 omega*rawGain cell12 b-(1-omega)*naturalDelta cell12 b=lowFee :=
 raw_nominal_balance cell12 b (ne_of_gt cell12_denominator_pos)
theorem cell12_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (41/1000) (83/2000)) :
 0 < paddedLowBalance cell12 b := by
 rw [raw_padded_balance cell12 b (ne_of_gt cell12_denominator_pos)]
 exact cell12_ordinary5 (ν := (1557/2500:ℝ)) hb (by norm_num)
theorem cell13_parameter_bounds : 31/50 ≤ cell13.q ∧ cell13.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell13.tinyRadius ∧ cell13.tinyRadius ≤ 1/25 ∧ 1 < cell13.L ∧ 1 < cell13.priorL ∧
 1/4 ≤ cell13.plainLo ∧ 1/4 ≤ cell13.priorPlainLo ∧ 0 < cell13.cut ∧ 0 < cell13.lo ∧ cell13.lo < cell13.hi := by
 norm_num [cell13, incumbent]
theorem cell13_denominator_pos : 0 < scheduleDenominator cell13 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell13]
theorem cell13_nominal_balance (b : ℝ) :
 omega*rawGain cell13 b-(1-omega)*naturalDelta cell13 b=lowFee :=
 raw_nominal_balance cell13 b (ne_of_gt cell13_denominator_pos)
theorem cell13_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (83/2000) (21/500)) :
 0 < paddedLowBalance cell13 b := by
 rw [raw_padded_balance cell13 b (ne_of_gt cell13_denominator_pos)]
 exact cell13_ordinary5 (ν := (3111/5000:ℝ)) hb (by norm_num)
theorem cell14_parameter_bounds : 31/50 ≤ cell14.q ∧ cell14.q < incumbent ∧ incumbent < 3/4 ∧
 0 < cell14.tinyRadius ∧ cell14.tinyRadius ≤ 1/25 ∧ 1 < cell14.L ∧ 1 < cell14.priorL ∧
 1/4 ≤ cell14.plainLo ∧ 1/4 ≤ cell14.priorPlainLo ∧ 0 < cell14.cut ∧ 0 < cell14.lo ∧ cell14.lo < cell14.hi := by
 norm_num [cell14, incumbent]
theorem cell14_denominator_pos : 0 < scheduleDenominator cell14 := by
 norm_num [scheduleDenominator, Pmix, K, incumbent, omega, cell14]
theorem cell14_nominal_balance (b : ℝ) :
 omega*rawGain cell14 b-(1-omega)*naturalDelta cell14 b=lowFee :=
 raw_nominal_balance cell14 b (ne_of_gt cell14_denominator_pos)
theorem cell14_padded_low_pos {b : ℝ} (hb : b ∈ Set.Icc (21/500) (43/1000)) :
 0 < paddedLowBalance cell14 b := by
 rw [raw_padded_balance cell14 b (ne_of_gt cell14_denominator_pos)]
 exact cell14_ordinary5 (ν := (3123/5000:ℝ)) hb (by norm_num)
end
end Record12518109Admission
