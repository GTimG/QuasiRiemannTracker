/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualRecordRebase
import Candidate.Research.RecursiveAffine.DepthReturnedFamily

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily Cycle63Moment Cycle153SourceReturn

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Enlarge only the uniform ideal/row-times-missing cap. The literal
classes, labels, witnesses, exponents and values are unchanged. -/
def widenHighRecord {Base : Type} {base : Base → Character} {eta : Character}
    {Z Bsmall Blarge T : ℝ} {left : Bool} {v : O} {unit : FirstSourceLabel → O}
    (hZ : 1 ≤ Z) (hB : Bsmall ≤ Blarge)
    (R : SecondStepHighCount M H hH base eta Z Bsmall T left v unit) :
    SecondStepHighCount M H hH base eta Z Blarge T left v unit where
  Class := R.Class
  labels := R.labels
  exponent := R.exponent
  rowExp := R.rowExp
  missExp := R.missExp
  zeroBin := R.zeroBin
  witness := R.witness
  zero_le := R.zero_le
  row_le := R.row_le
  supported := R.supported
  same_support := R.same_support
  row_cap := fun s l hl => (R.row_cap s l hl).trans
    (Real.rpow_le_rpow_of_exponent_le hZ hB)
  ideal_cap := by
    intro s l hl
    have h := R.ideal_cap s l hl
    have hc := Real.rpow_le_rpow_of_exponent_le hZ hB
    exact ⟨h.1.trans hc, h.2.1.trans hc, h.2.2.1.trans hc, h.2.2.2.trans hc⟩
  missing_le := R.missing_le

variable {M H hH}

/-- Only a source capacity is enlarged; a Pays proof is preserved exactly. -/
theorem widenHighRecord_pays {Base : Type} {base : Base → Character} {eta : Character}
    {Z Bsmall Blarge T : ℝ} {left : Bool} {v : O} {unit : FirstSourceLabel → O}
    (hZ : 1 ≤ Z) (hB : Bsmall ≤ Blarge)
    (R : SecondStepHighCount M H hH base eta Z Bsmall T left v unit)
    (q m A a loss : ℝ) (hp : R.Pays q m A a loss) :
    (widenHighRecord M H hH hZ hB R).Pays q m A a loss := hp

theorem widenHighRecord_value {Base : Type} {base : Base → Character} {eta : Character}
    {Z Bsmall Blarge T : ℝ} {left : Bool} {v : O} {unit : FirstSourceLabel → O}
    (hZ : 1 ≤ Z) (hB : Bsmall ≤ Blarge)
    (R : SecondStepHighCount M H hH base eta Z Bsmall T left v unit) :
    (widenHighRecord M H hH hZ hB R).value = R.value := rfl

/-- Literal part rebase at the fixed public cap, using the actual physical
unit bound U≤1. The record remains the same actual attaining HIGH source. -/
def rebaseReturnedPartFixedCap {Base : Type} {base : Character → Base → Character}
    {eta : Character} {Z B T U q : ℝ} {v : O}
    (hZ : 1 < Z) (hU : 0 < U) (hU1 : U ≤ 1) (hB : 0 ≤ B)
    (P : ReturnedPartAt M H hH q base eta (Z^U) B T v) :
    ReturnedPartAt M H hH q base eta Z B T v where
  unit := P.unit
  record := fun b => widenHighRecord M H hH hZ.le
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hU1 hB)
    (rebaseHighRecord M H hH (zero_lt_one.trans hZ) (P.record b))
  scale := U*P.scale
  length := U*P.length
  amp := U*P.amp
  loss := U*P.loss
  pays := fun b => rebaseHighRecord_pays hZ hU (P.record b)
    q P.scale P.length P.amp P.loss (P.pays b)

theorem rebaseReturnedPartFixedCap_value {Base : Type} {base : Character → Base → Character}
    {eta : Character} {Z B T U q : ℝ} {v : O}
    (hZ : 1 < Z) (hU : 0 < U) (hU1 : U ≤ 1) (hB : 0 ≤ B)
    (P : ReturnedPartAt M H hH q base eta (Z^U) B T v) :
    (rebaseReturnedPartFixedCap hZ hU hU1 hB P).value = P.value := by
  unfold ReturnedPartAt.value
  apply Finset.sum_congr rfl
  intro b _
  exact rebaseHighRecord_value (zero_lt_one.trans hZ) (P.record b)

/-- Rebase the actual finite returned family. Every physical prefix,
attaining part, multiplier and scalar source weight is retained. Historical
missing-radical logs, like every native exponent, acquire the actual unit U.
No new prefix, factor Z^m or unproved energy bound is introduced. -/
def rebaseDepthReturnedFamily {Depth : Type} [Fintype Depth]
    {junction : Depth → ℝ} {Base : Depth → Type}
    {base : (d : Depth) → Character → Base d → Character}
    {eta : Character} {Z B T U : ℝ} {root : O}
    (hZ : 1 < Z) (hU : 0 < U) (hU1 : U ≤ 1) (hB : 0 ≤ B)
    (F : DepthReturnedFamily M H hH junction Base base eta (Z^U) B T root) :
    DepthReturnedFamily M H hH junction Base base eta Z B T root where
  Prefix := F.Prefix
  prefixFintype := F.prefixFintype
  multiplier := F.multiplier
  root_divides := F.root_divides
  historyMissing := fun d p => U*F.historyMissing d p
  historyMissing_nonneg := fun d p => mul_nonneg hU.le (F.historyMissing_nonneg d p)
  part := fun d p => rebaseReturnedPartFixedCap hZ hU hU1 hB (F.part d p)
  weight := F.weight
  weight_nonneg := F.weight_nonneg

/-- Family return values are exact absolute count sums through a native
base change. Only their coordinate descriptions change. -/
theorem rebaseDepthReturnedFamily_value {Depth : Type} [Fintype Depth]
    {junction : Depth → ℝ} {Base : Depth → Type}
    {base : (d : Depth) → Character → Base d → Character}
    {eta : Character} {Z B T U : ℝ} {root : O}
    (hZ : 1 < Z) (hU : 0 < U) (hU1 : U ≤ 1) (hB : 0 ≤ B)
    (F : DepthReturnedFamily M H hH junction Base base eta (Z^U) B T root) :
    (rebaseDepthReturnedFamily hZ hU hU1 hB F).value = F.value := by
  unfold DepthReturnedFamily.value
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro p _
  change F.weight d p * (rebaseReturnedPartFixedCap hZ hU hU1 hB (F.part d p)).value = _
  rw [rebaseReturnedPartFixedCap_value hZ hU hU1 hB (F.part d p)]

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.rebaseReturnedPartFixedCap_value
#print axioms OAI.SevenEighths.Cycle153RegionalLow.rebaseDepthReturnedFamily_value
