/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalLedger

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace Cycle153.FixedStages
noncomputable section
open Cycle63.Optimization

/-- Stage 0; fixed rational data from the priced five-stage argument. -/
def stage0 : RegionalStage where
  q := (127604383/200000000:ℝ)
  lam := (329956163680853485282867923636152689767654715507615953261620968235438902692223089116358959199861693000368331363955693/88192178367938882647736127702504050241299135674720205790519673580377960007184113093769047066398565099317579025603487:ℝ)
  price := (348304162270373263705960301936971458826525120191792362365107385589339077/520061477653773063826255649074195179732561721150754174190644313536034462:ℝ)
  intercept := (1287143469639679686937537996934217729594808245187419539924946711845151667/1300153694134432659565639122685487949331404302876885435476610783840086155:ℝ)
  zeroSaving := (1/20:ℝ)
  primeFraction := (99/100:ℝ)
  q_pos := by norm_num
  q_floor := by norm_num
  price_pos := by norm_num
  price_le_one := by norm_num
  q_le_price := by norm_num
  q_intercept_lt_price := by norm_num
  one_le_lam := by norm_num
  lam_le_six_price := by norm_num
  zeroSaving_pos := by norm_num
  primeFraction_half := by norm_num
  primeFraction_one := by norm_num
  lam_le_six_old := by norm_num [slotPrice, betaBound]
  low_reserve_cap := by norm_num [lowReserveAt, lowReserveWeight, allowanceUnit]
theorem stage0_ratio_bound : amplifierRatio stage0.price stage0.intercept stage0.q≤7 := by
  norm_num [stage0, amplifierRatio]
theorem stage0_slope_bound : stage0.lam≤5 := by norm_num [stage0]

/-- Stage 1; fixed rational data from the priced five-stage argument. -/
def stage1 : RegionalStage where
  q := (676506091/1000000000:ℝ)
  lam := (348304162270373263705960301936971458826525120191792362365107385589339077/86676912942295510637709274845699196622093620191792362365107385589339077:ℝ)
  price := (3492140652204252985490844368535924067892717648044679111/5069587694592831216226672748036094407356305888268074666:ℝ)
  intercept := (2516744594931318608918280476140232670724949148588757925/2534793847296415608113336374018047203678152944134037333:ℝ)
  zeroSaving := (1/100:ℝ)
  primeFraction := (99/100:ℝ)
  q_pos := by norm_num
  q_floor := by norm_num
  price_pos := by norm_num
  price_le_one := by norm_num
  q_le_price := by norm_num
  q_intercept_lt_price := by norm_num
  one_le_lam := by norm_num
  lam_le_six_price := by norm_num
  zeroSaving_pos := by norm_num
  primeFraction_half := by norm_num
  primeFraction_one := by norm_num
  lam_le_six_old := by norm_num [slotPrice, betaBound]
  low_reserve_cap := by norm_num [lowReserveAt, lowReserveWeight, allowanceUnit]
theorem stage1_ratio_bound : amplifierRatio stage1.price stage1.intercept stage1.q≤7 := by
  norm_num [stage1, amplifierRatio]
theorem stage1_slope_bound : stage1.lam≤5 := by norm_num [stage1]

/-- Stage 2; fixed rational data from the priced five-stage argument. -/
def stage2 : RegionalStage where
  q := (693781289/1000000000:ℝ)
  lam := (3492140652204252985490844368535924067892717648044679111/844931282432138536037778791339349067892717648044679111:ℝ)
  price := (269813837551089325202799031444440059/380807241088706305360974188666640354:ℝ)
  intercept := (135393878749136580688352305134408113/136002586103109394771776495952371555:ℝ)
  zeroSaving := (1/100:ℝ)
  primeFraction := (99/100:ℝ)
  q_pos := by norm_num
  q_floor := by norm_num
  price_pos := by norm_num
  price_le_one := by norm_num
  q_le_price := by norm_num
  q_intercept_lt_price := by norm_num
  one_le_lam := by norm_num
  lam_le_six_price := by norm_num
  zeroSaving_pos := by norm_num
  primeFraction_half := by norm_num
  primeFraction_one := by norm_num
  lam_le_six_old := by norm_num [slotPrice, betaBound]
  low_reserve_cap := by norm_num [lowReserveAt, lowReserveWeight, allowanceUnit]
theorem stage2_ratio_bound : amplifierRatio stage2.price stage2.intercept stage2.q≤7 := by
  norm_num [stage2, amplifierRatio]
theorem stage2_slope_bound : stage2.lam≤5 := by norm_num [stage2]

/-- Stage 3; fixed rational data from the priced five-stage argument. -/
def stage3 : RegionalStage where
  q := (142343339/200000000:ℝ)
  lam := (269813837551089325202799031444440059/63467873514784384226829031444440059:ℝ)
  price := (12550898365191723707/17222127978271342242:ℝ)
  intercept := (8592952672500196895/8611063989135671121:ℝ)
  zeroSaving := (1/100:ℝ)
  primeFraction := (99/100:ℝ)
  q_pos := by norm_num
  q_floor := by norm_num
  price_pos := by norm_num
  price_le_one := by norm_num
  q_le_price := by norm_num
  q_intercept_lt_price := by norm_num
  one_le_lam := by norm_num
  lam_le_six_price := by norm_num
  zeroSaving_pos := by norm_num
  primeFraction_half := by norm_num
  primeFraction_one := by norm_num
  lam_le_six_old := by norm_num [slotPrice, betaBound]
  low_reserve_cap := by norm_num [lowReserveAt, lowReserveWeight, allowanceUnit]
theorem stage3_ratio_bound : amplifierRatio stage3.price stage3.intercept stage3.q≤7 := by
  norm_num [stage3, amplifierRatio]
theorem stage3_slope_bound : stage3.lam≤5 := by norm_num [stage3]

/-- Stage 4; fixed rational data from the priced five-stage argument. -/
def stage4 : RegionalStage where
  q := (730301837/1000000000:ℝ)
  lam := (12550898365191723707/2870354663045223707:ℝ)
  price := (4499/6000:ℝ)
  intercept := (1/1:ℝ)
  zeroSaving := (1/100:ℝ)
  primeFraction := (99/100:ℝ)
  q_pos := by norm_num
  q_floor := by norm_num
  price_pos := by norm_num
  price_le_one := by norm_num
  q_le_price := by norm_num
  q_intercept_lt_price := by norm_num
  one_le_lam := by norm_num
  lam_le_six_price := by norm_num
  zeroSaving_pos := by norm_num
  primeFraction_half := by norm_num
  primeFraction_one := by norm_num
  lam_le_six_old := by norm_num [slotPrice, betaBound]
  low_reserve_cap := by norm_num [lowReserveAt, lowReserveWeight, allowanceUnit]
theorem stage4_ratio_bound : amplifierRatio stage4.price stage4.intercept stage4.q≤7 := by
  norm_num [stage4, amplifierRatio]
theorem stage4_slope_bound : stage4.lam≤5 := by norm_num [stage4]

end
end Cycle153.FixedStages

#print axioms Cycle153.FixedStages.stage4
#print axioms Cycle153.FixedStages.stage4_ratio_bound
