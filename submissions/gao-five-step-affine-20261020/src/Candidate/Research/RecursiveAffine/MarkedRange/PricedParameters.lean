/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.FixedStages
import Candidate.Research.RecursiveAffine.MarkedRange.RootBudget
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Cycle153.MarkedRootPrice
noncomputable section
open Cycle63.Optimization
def price : ℝ := Cycle153.FixedStages.stage0.price
def intercept : ℝ := Cycle153.FixedStages.stage0.intercept
def q : ℝ := Cycle153.FixedStages.stage0.q
def lambda : ℝ := Cycle153.FixedStages.stage0.lam
def B : ℝ := (18767487223416391834064569594363209332507915203299559923866443891942888098667853973693252077030625996356624104246276902412635109875927755490474333178781015079084539556698361407568181709371343649701393698420472934209822921806477506758480866628067754095992378338031176149156952588250753650209798776733040486658858005166457451154051/19110919888706709812766290819916485826208191340940770791940702158912085371003996164860792695046462830308466233784371844086544474228752143390838017296992738341176272874121327652590702574747109891599960269958366455044116610842062086316294176128155115437457794003213275776601341582216676004415608049429998920487638804738048000000000:ℝ)
def top : ℝ := (2019049/50000000:ℝ)
def bottom : ℝ := firstCellTop
theorem price_bounds : price∈Set.Icc (167434129058033253/250000000000000000:ℝ) (669736516232133013/1000000000000000000:ℝ) := by
  norm_num [price,Cycle153.FixedStages.stage0]
theorem intercept_bounds : intercept∈Set.Icc (494996659028294947/500000000000000000:ℝ) (197998663611317979/200000000000000000:ℝ) := by
  norm_num [intercept,Cycle153.FixedStages.stage0]
theorem q_bounds : q∈Set.Icc (127604383/200000000:ℝ) (638021915000000001/1000000000000000000:ℝ) := by
  norm_num [q,Cycle153.FixedStages.stage0]
theorem lambda_bounds : lambda∈Set.Icc (2993065097489913/800000000000000:ℝ) (3741331371862391251/1000000000000000000:ℝ) := by
  norm_num [lambda,Cycle153.FixedStages.stage0]
theorem B_bounds : B∈Set.Icc (491014753154471021/500000000000000000:ℝ) (982029506308942043/1000000000000000000:ℝ) := by
  norm_num [B,Cycle153.FixedStages.stage0]

theorem q_native : Cycle63.Arithmetic.q0≤q := by
  norm_num [q,Cycle153.FixedStages.stage0,Cycle63.Arithmetic.q0,firstJunction]
theorem q_two_thirds : q<2/3 := by norm_num [q,Cycle153.FixedStages.stage0]
theorem top_pos : 0<top := by norm_num [top]
theorem window_ends : bottom<top := by
  norm_num [bottom,top,firstCellTop,slotFloor,cellMesh,allowanceUnit]
theorem low_reserve_pos : 0<lowReserveAt price intercept q := by
  have hk:=price_bounds;have hi:=intercept_bounds;have hq:=q_bounds
  simp only [lowReserveAt,lowReserveWeight,allowanceUnit]
  rat_pos [hk,hi,hq]

macro "priced_channels" : tactic => `(tactic|
  (simp only [Cycle63.Optimization.rateChannel,Cycle63.Optimization.linearChannel,
    Cycle63.Optimization.mixedChannel,Cycle63.Optimization.inverseChannel,
    Cycle63.Optimization.cappedChannel,Cycle63.Optimization.planeHigh,
    Cycle63.Optimization.planeFrequency,Cycle63.Optimization.planeAmplifier,
    Cycle63.Optimization.highFee,Cycle63.Optimization.inverseCapAt,
    Cycle63.Optimization.plainCapAt,Cycle63.Optimization.capUnitAt,
    Cycle63.Optimization.chosenPerUnit,Cycle63.Optimization.plainCapacityCost,
    Cycle63.Optimization.halfGain,Cycle63.Optimization.amplifierRatio,
    Cycle63.Optimization.density,Cycle63.Optimization.lowReserveAt,
    Cycle63.Optimization.markedLossAt,Cycle63.Optimization.markedRate,
    Cycle63.Optimization.markedPad,Cycle63.Optimization.markedBinWidth,
    Cycle63.Optimization.geometryLossCap,Cycle63.Optimization.lowReserveWeight,
    Cycle63.Optimization.allowanceUnit,Cycle63.Optimization.suppliedAt,
    Cycle63.Optimization.cellMesh,Cycle63.Optimization.supplyLoss,
    Cycle63.Optimization.commonAllocationLoss,Cycle63.Optimization.tinySlotLoss,
    Cycle63.Optimization.frequencyLossCap,Cycle63.Optimization.tailSlack,
    Cycle63.Optimization.slotPrice,Cycle63.Optimization.betaBound,
    Cycle63.Optimization.firstCellTop,Cycle63.Optimization.slotFloor,
    Cycle153.MarkedRootPrice.bottom,Cycle153.MarkedRootPrice.top]))
end
end Cycle153.MarkedRootPrice
