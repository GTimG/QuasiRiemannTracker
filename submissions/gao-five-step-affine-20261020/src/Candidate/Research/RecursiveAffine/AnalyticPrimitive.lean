/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.PrimitiveStageSchedule
import Candidate.Research.RecursiveAffine.RootLedgerBinding
import Candidate.Research.RecursiveAffine.ActualHighNodeProducer
import Candidate.Cycle63.Physical.InitialMass.GeometryFinalLowLoss

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OAI.SevenEighths.Cycle153AnalyticPrimitive
noncomputable section
open Cycle63InitialMass Cycle153RecursiveHighProvider Cycle153.RegionalSchedule
open Cycle153 Cycle63.Optimization

/-- The analytic tolerance is distinct from the unchanged rational-coordinate grid. -/
def analyticError : ℝ := 1/(10:ℝ)^14
def mu : ℝ := analyticError/128
def detectorExtra : ℝ := 1/(10:ℝ)^20
def finiteTolerance : ℝ := 1/(10:ℝ)^15

theorem mu_pos : 0< mu := by norm_num [mu,analyticError]
theorem analytic_grid_distinct : (1/(gridSize:ℝ))< analyticError := by
  norm_num [gridSize,analyticError]

/-- Every actual fixed stage has this same native analytic loss unit. -/
theorem stage_mu (j : Fin 5) : stageMu (stage j) analyticError=mu := by
  fin_cases j <;>
    norm_num [stageMu,stage,analyticError,mu,lowReserveAt,lowReserveWeight,allowanceUnit,
      Cycle153.FixedStages.stage0,Cycle153.FixedStages.stage1,Cycle153.FixedStages.stage2,
      Cycle153.FixedStages.stage3,Cycle153.FixedStages.stage4]

theorem native_stage_mu (j : Fin 5) (i : RegionalIndex (stage j) gridSize) :
    @geometryLossUnit (regionalFamily (stage j) gridSize i) 1 analyticError=mu :=
  (stageMu_eq_native (stage j) gridSize i analyticError).trans (stage_mu j)

theorem actual_root_mu :
    @geometryLossUnit Cycle153.Root.rootLedger 1 analyticError=mu := by
  have hr : @Cycle63.AffineLedger.lowReserve Cycle153.Root.rootLedger =
      lowReserveAt Cycle153.MarkedRootPrice.price Cycle153.MarkedRootPrice.intercept
        Cycle153.MarkedRootPrice.q := rfl
  simp only [geometryLossUnit,hr,mul_one]
  norm_num [mu,analyticError,Cycle153.MarkedRootPrice.price,
    Cycle153.MarkedRootPrice.intercept,Cycle153.MarkedRootPrice.q,
    Cycle153.FixedStages.stage0,lowReserveAt,lowReserveWeight,allowanceUnit]

theorem actual_native_reserve [Cycle63.AffineLedger]
    (hmu : geometryLossUnit 1 analyticError=mu) :
    128*mu≤ Cycle63.AffineLedger.lowReserve := by
  have h:=(geometry_loss_unit_reserve 1 analyticError 1 le_rfl).2
  rw [hmu] at h
  norm_num only [one_mul] at h
  linarith only [h]

theorem marked_cap : mu≤ geometryLossCap := by
  norm_num [mu,analyticError,geometryLossCap,lowReserveWeight,allowanceUnit,
    slotPrice,betaBound,planeQuadratic]

theorem actual_high_mu : highSourceLossUnit analyticError=mu := by
  have hr := Cycle63.Arithmetic.lowRegionRatio_bounds
  have hlow : analyticError≤ @Cycle63.AffineLedger.lowReserve Cycle63.Arithmetic.firstLevelLedger := by
    change analyticError≤ Cycle63.Arithmetic.lowReserve
    unfold Cycle63.Arithmetic.lowReserve lowReserveAt lowReserveWeight allowanceUnit
    norm_num only [analyticError]
    nlinarith only [hr.2]
  unfold highSourceLossUnit geometryLossUnit mu
  apply min_eq_left
  apply le_min (by simpa only [mul_one] using
    div_le_div_of_nonneg_right hlow (by norm_num : (0:ℝ)≤ 128))
  norm_num [analyticError]

theorem actual_high_affine_domain : analyticError≤  secondStepAffineLoss := by
  norm_num [analyticError,secondStepAffineLoss]

def driverRate (N : ℕ) : ℝ :=
  geometryFinalDictionaryRate mu 31 3 4 3 130 (3*((N:ℝ)+2)) N

theorem driver_budgets (N : ℕ) :
    0< driverRate N ∧ driverRate N≤ mu/128 ∧
      2*driverRate N*31*(N:ℝ)≤ mu/32 := by
  have h:=geometry_final_dictionary_budgets mu 31 3 4 3 130 (3*((N:ℝ)+2)) N
    mu_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by positivity)
  rcases h with ⟨hpos,hcommon,hcap,hplain,hlow,hhigh,hslot,hplaincost,hjoined⟩
  exact ⟨hpos,hcap,hslot⟩

/-- The native HIGH returned loss, not an invented output loss, fits below E. -/
theorem actual_high_loss (N : ℕ) :
    highSourceLossNeeded analyticError N≤ 2*mu ∧ 2*mu< finiteTolerance := by
  rw [highSourceLossNeeded,actual_high_mu]
  have hd := (driver_budgets N).1
  have hs : driverRate N≤ mu/(2048*((N:ℝ)+1)) := by
    have h : driverRate N≤ mu/(64*((31:ℝ)+1)*((N:ℝ)+1)) := by
      unfold driverRate geometryFinalDictionaryRate
      exact min_le_right _ _
    simpa only [show (64:ℝ)*(31+1)=2048 by norm_num] using h
  have hprod := (le_div_iff₀ (by positivity : 0< 2048*((N:ℝ)+1))).mp hs
  have hN : (0:ℝ)≤ N := Nat.cast_nonneg N
  constructor
  · change 13/8*mu+(9*(N:ℝ)+282)*driverRate N≤ 2*mu
    nlinarith only [hprod,hd,mul_nonneg hN hd.le]
  · norm_num [mu,analyticError,finiteTolerance]

/-- This pays actual detector overshoot and independent OLD analytic fees
inside ONE pre-existing mu/8 term of the native LOW target. -/
theorem old_extra_room {q u childError coefficientFee terminalError : ℝ}
    (hq0 : 0≤ q) (hq1 : q≤ 1) (hu1 : u≤ 1)
    (hchild0 : 0≤ childError) (hchild : childError≤ mu/1024)
    (hcoefficient : coefficientFee≤ mu/1024)
    (hterminal : terminalError≤ 2*mu/1024) :
    u*childError+q*detectorExtra+coefficientFee+terminalError≤ mu/128 ∧
    mu/128< mu/8 := by
  have hc:=mul_le_mul_of_nonneg_right hu1 hchild0
  have hq:=mul_le_mul_of_nonneg_right hq1 (by norm_num [detectorExtra] : 0≤ detectorExtra)
  constructor
  · have he : detectorExtra+4*mu/1024≤ mu/128 := by norm_num [detectorExtra,mu,analyticError]
    linarith only [hc,hq,hchild,hcoefficient,hterminal,he]
  · nlinarith only [mu_pos]

/-- Exact OLD exponent consumer: the source unit and rounded deletion are
the actual ones. Only their native scalar identities are used; there is
no energy estimate in the assumptions. This leaves 15mu/128 unspent in
the mu/8 term already present in the native target. -/
theorem actual_old_exponent_paid
    {q u childError coefficientFee terminalError nominal width amp reserve allowance deletion mesh : ℝ}
    (hq0 : 0≤ q) (hq1 : q≤ 1) (hu1 : u≤ 1)
    (hchild0 : 0≤ childError) (hchild : childError≤ mu/1024)
    (hcoefficient : coefficientFee≤ mu/1024)
    (hterminal : terminalError≤ 2*mu/1024)
    (hunit : u=nominal+width)
    (hprice : q*deletion≤ amp-reserve+allowance) :
    u*(1+childError)+q*(deletion+detectorExtra)+coefficientFee+terminalError+q*mesh≤
      nominal+amp+(width-reserve+mu/8+q*mesh)+allowance-15*mu/128 := by
  have h:= (old_extra_room hq0 hq1 hu1 hchild0 hchild hcoefficient hterminal).1
  nlinarith only [h,hprice,hunit]

/-- The rounded native deletion pays its OLD reserve by the actual ledger
identity, for root and inner ledgers alike. No desired capacity inequality
is supplied as an assumption. -/
theorem native_affine_deletion_identity [Cycle63.AffineLedger] (cell : ℝ) :
    Cycle63.AffineLedger.q*((Cycle63.AffineLedger.regionGap cell+
      6*Cycle63.AffineLedger.intercept*Cycle63.AffineLedger.amp cell)/
        (6*Cycle63.AffineLedger.price))=
      Cycle63.AffineLedger.amp cell-Cycle63.AffineLedger.lowReserve := by
  have h:=Cycle63.AffineLedger.low_reserve cell
  have hp : Cycle63.AffineLedger.price≠0:=Cycle63.AffineLedger.price_pos.ne'
  unfold Cycle63.AffineLedger.lowRate at h
  field_simp [hp] at h ⊢
  nlinarith only [h]

/-- The complete OLD scalar consumer at the actual native rounded cell. -/
theorem native_selected_old_exponent_paid [Cycle63.AffineLedger]
    (cell : ℝ) {u childError coefficientFee terminalError nominal width mesh : ℝ}
    (hu1 : u≤1) (hchild0 : 0≤childError) (hchild : childError≤ mu/1024)
    (hcoefficient : coefficientFee≤ mu/1024)
    (hterminal : terminalError≤2*mu/1024) (hunit : u=nominal+width) :
    u*(1+childError)+Cycle63.AffineLedger.q*
      ((Cycle63.AffineLedger.regionGap cell+
          6*Cycle63.AffineLedger.intercept*Cycle63.AffineLedger.amp cell)/
        (6*Cycle63.AffineLedger.price)+detectorExtra)+coefficientFee+terminalError+
          Cycle63.AffineLedger.q*mesh≤
      nominal+Cycle63.AffineLedger.amp cell+
        (width-Cycle63.AffineLedger.lowReserve+mu/8+Cycle63.AffineLedger.q*mesh)-15*mu/128 := by
  have h:=actual_old_exponent_paid Cycle63.AffineLedger.q_pos.le
    Cycle63.AffineLedger.q_le_one hu1 hchild0 hchild hcoefficient hterminal hunit
    (allowance:=0) (mesh:=mesh) (by simpa only [add_zero] using (native_affine_deletion_identity cell).le)
  simpa only [add_zero] using h

/-- Even the new analytic losses plus measured finite coordinate pads fit
the unchanged E=1e-15 geometry tolerance at each of the five stages. -/
theorem finite_error_budget :
    mu+2*detectorExtra+2202/(gridSize:ℝ)< finiteTolerance ∧
    2*mu+2*detectorExtra+2202/(gridSize:ℝ)< finiteTolerance ∧
    detectorExtra+252/(gridSize:ℝ)< mu/1024 := by
  norm_num [mu,analyticError,detectorExtra,gridSize,finiteTolerance]

/-- Five terminal HIGH losses and five path-fee budgets fit the existing
1e-12 aggregate path allowance without changing any geometric dual. -/
theorem five_stage_error_budget :
    5*(2*mu+finiteTolerance)< 1/(10:ℝ)^12 := by
  norm_num [mu,analyticError,finiteTolerance]

/-- The full literal native LOW consumer ledger remains valid, with its
reserve intact. This invokes the original consumer theorem at the new mu. -/
theorem native_low_consumer_budget [Cycle63.AffineLedger]
    (N : ℕ) (omega mesh amp : ℝ)
    (homega : omega≤ 33*mu/128) (hmesh : mesh≤ mu/8) :
    let delta:=driverRate N
    let error:=mu/8+mu/128-Cycle63.AffineLedger.lowReserve+mu/8+2*delta*31*N+
      Cycle63.AffineLedger.lowRate*(omega+mu/8)+Cycle63.AffineLedger.q*mesh+mu/8
    let target:=3*delta+amp+error+delta+4*delta+delta+delta+
      (delta+3*(((N:ℝ)+2)*3)*delta)+delta
    target+3*delta-amp≤ -Cycle63.AffineLedger.lowReserve+2*mu := by
  have h:=geometry_final_main_low_consumer_ledger mu 31 3 4 3 130
    (3*((N:ℝ)+2)) omega mesh amp N mu_pos (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by positivity) homega hmesh
  convert h using 1 <;> dsimp only [driverRate] <;> ring


end
end OAI.SevenEighths.Cycle153AnalyticPrimitive
#print axioms OAI.SevenEighths.Cycle153AnalyticPrimitive.stage_mu
#print axioms OAI.SevenEighths.Cycle153AnalyticPrimitive.actual_high_loss
#print axioms OAI.SevenEighths.Cycle153AnalyticPrimitive.actual_old_exponent_paid
#print axioms OAI.SevenEighths.Cycle153AnalyticPrimitive.native_selected_old_exponent_paid
#print axioms OAI.SevenEighths.Cycle153AnalyticPrimitive.finite_error_budget
#print axioms OAI.SevenEighths.Cycle153AnalyticPrimitive.native_low_consumer_budget
