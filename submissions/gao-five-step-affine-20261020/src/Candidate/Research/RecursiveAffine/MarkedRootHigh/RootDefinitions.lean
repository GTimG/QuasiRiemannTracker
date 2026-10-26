/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.MarkedRange.PricedConsumers
import Candidate.Cycle63.Physical.InitialMass.MarkedGeometryPayment
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Cycle153.MarkedRootPrice
noncomputable section
open Cycle63.Optimization
open OAI.SevenEighths.LocalMoment

def amp (b : ℝ) : ℝ := planeAmplifier price intercept q lambda B b
def totalA (b : ℝ) : ℝ := B-(lambda-1)*(b-cellMesh)
def frequencyAt (b : ℝ) : ℝ := 1-6*amp b-frequencyLossCap
def highMainReserve (b d : ℝ) : ℝ := planeHigh price intercept q lambda B d b
def lowReserve : ℝ := lowReserveAt price intercept q
def markedLoss : ℝ := markedLossAt top

theorem highFee_eq : highFee price intercept q top=lowReserve+markedLoss := rfl

theorem highMainReserve_le_reserve {b d M A a : ℝ}
    (hd : Cycle63.Arithmetic.q0≤d ∧ d≤3/4)
    (hA : A≤M*totalA b) (ha : a≤M*amp b) :
    M*highMainReserve b d≤M*(1-unmarkedDensity d)-d*A-a*(5-6*unmarkedDensity d) := by
  have hcoef : 0≤5-6*unmarkedDensity d := by
    linarith [Cycle63.Arithmetic.rho0_bounds.2,(Cycle63.Physical.high_density_bounds hd).2.1]
  have hA':=mul_le_mul_of_nonneg_left hA
    (by linarith [Cycle63.Arithmetic.q0_bounds.1,hd.1] : (0:ℝ)≤d)
  have ha':=mul_le_mul_of_nonneg_right ha hcoef
  simp only [highMainReserve,planeHigh,totalA,amp] at *
  change M*(1-unmarkedDensity d-d*(B-(lambda-1)*(b-cellMesh))-
    planeAmplifier price intercept q lambda B b*(5-6*unmarkedDensity d))≤_
  nlinarith only [hA',ha']

/-- This is the literal coordinate calculation before multiplication by the native core. -/
theorem raw_frequency_lower (M c d b a R Lc ω err freq cell : ℝ)
    (hc : 0≤c) (hd : 0≤d) (hb : 0≤b) (hR : R≤c) (hLc : 0≤Lc)
    (ha : a≤M*amp cell) (hω : ω≤M*frequencyLossCap) (herr : 0≤err)
    (hq : freq=M-R-max (c-d) 0+Lc-6*a-ω+err) :
    frequencyAt cell*M-2*(c+b)≤freq := by
  have hm : max (c-d) 0≤c := max_le (by linarith) hc
  unfold frequencyAt
  linarith

theorem frequencyAt_lower {b : ℝ} (hb : b∈Set.Icc bottom top) :
    4/5+2*suppliedAt b≤frequencyAt b := by
  have hk:=price_bounds;have hi:=intercept_bounds;have hq:=q_bounds
  have hl:=lambda_bounds;have hB:=B_bounds
  have hcell : b∈Set.Icc (3400001/100000000:ℝ) (2019049/50000000) := by
    convert hb using 1 <;> norm_num [bottom,top,firstCellTop,slotFloor,cellMesh,allowanceUnit]
  apply le_of_lt
  simp only [frequencyAt,amp]
  priced_channels
  rat_pos [hcell,hk,hi,hq,hl,hB]
end
end Cycle153.MarkedRootPrice

#print axioms Cycle153.MarkedRootPrice.highMainReserve_le_reserve
#print axioms Cycle153.MarkedRootPrice.raw_frequency_lower
#print axioms Cycle153.MarkedRootPrice.frequencyAt_lower
