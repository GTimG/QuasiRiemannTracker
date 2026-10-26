/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalReturned

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CenteredMomentEnergyState Cycle63Moment

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The same literal HIGH classes and witnesses, expressed at the original
base rather than the actual continuation base. No extra energy-scale factor
is inserted in the value. -/
def rebaseHighRecord {Base : Type} {base : Base → Character} {eta : Character}
    {Z B T U : ℝ} {left : Bool} {v : O} {unit : FirstSourceLabel → O}
    (hZ : 0 < Z)
    (R : SecondStepHighCount M H hH base eta (Z^U) B T left v unit) :
    SecondStepHighCount M H hH base eta Z (U*B) T left v unit where
  Class := R.Class
  labels := R.labels
  exponent := fun s => U * R.exponent s
  rowExp := fun s => U * R.rowExp s
  missExp := fun s => U * R.missExp s
  zeroBin := R.zeroBin
  witness := R.witness
  zero_le := R.zero_le
  row_le := by
    intro s l hl
    simpa only [← Real.rpow_mul hZ.le] using R.row_le s l hl
  supported := R.supported
  same_support := R.same_support
  row_cap := by
    intro s l hl
    simpa only [← Real.rpow_mul hZ.le] using R.row_cap s l hl
  ideal_cap := by
    intro s l hl
    simpa only [← Real.rpow_mul hZ.le] using R.ideal_cap s l hl
  missing_le := by
    intro s l hl
    simpa only [← Real.rpow_mul hZ.le] using R.missing_le s l hl

variable {M H hH}

/-- A native record value is already an absolute energy count. Rebasing
multiplies each exponent by the actual unit and preserves its value exactly. -/
theorem rebaseHighRecord_value {Base : Type} {base : Base → Character} {eta : Character}
    {Z B T U : ℝ} {left : Bool} {v : O} {unit : FirstSourceLabel → O}
    (hZ : 0 < Z)
    (R : SecondStepHighCount M H hH base eta (Z^U) B T left v unit) :
    (rebaseHighRecord M H hH hZ R).value = R.value := by
  unfold SecondStepHighCount.value
  apply Finset.sum_congr rfl
  intro s _
  change Z ^ (U * R.exponent s) * _ = (Z^U) ^ R.exponent s * _
  rw [Real.rpow_mul hZ.le]
  rfl

/-- `Pays` is homogeneous under this same base change, including its
subtracted scale and literal multiplier norm. It gives no licence to multiply
a return by a second copy of the intermediate energy scale. -/
theorem rebaseHighRecord_pays {Base : Type} {base : Base → Character} {eta : Character}
    {Z B T U : ℝ} {left : Bool} {v : O} {unit : FirstSourceLabel → O}
    (hZ : 1 < Z) (hU : 0 < U)
    (R : SecondStepHighCount M H hH base eta (Z^U) B T left v unit)
    (q m A a loss : ℝ) (hp : R.Pays q m A a loss) :
    (rebaseHighRecord M H hH (zero_lt_one.trans hZ) R).Pays
      q (U*m) (U*A) (U*a) (U*loss) := by
  intro s
  have hs := hp s
  refine ⟨hs.1, hs.2.1, ?_⟩
  have hpay := mul_le_mul_of_nonneg_left hs.2.2 hU.le
  have hlog : U * Real.logb (Z^U) ((Ideal.span {v}).absNorm : ℝ) =
      Real.logb Z ((Ideal.span {v}).absNorm : ℝ) := by
    rw [Real.logb, Real.logb, Real.log_rpow (zero_lt_one.trans hZ)]
    have hzlog : Real.log Z ≠ 0 := ne_of_gt (Real.log_pos hZ)
    field_simp
  change U * R.exponent s - U*m + U * R.missExp s +
      LocalMoment.unmarkedDensity (2*R.zeroBin s-1) *
        (U * R.rowExp s - Real.logb Z ((Ideal.span {v}).absNorm : ℝ)) ≤
      U*loss - (U*m*(1-LocalMoment.unmarkedDensity (2*R.zeroBin s-1)) -
        (2*R.zeroBin s-1)*(U*A) - (U*a)*(5-6*LocalMoment.unmarkedDensity (2*R.zeroBin s-1)))
  rw [← hlog]
  convert hpay using 1 <;> ring


open Cycle153SourceReturn

/-- A source-produced returned part at the actual continuation base, with
all payment quantities transported by the same physical unit. -/
def rebaseReturnedPart {Base : Type} {base : Character → Base → Character}
    {eta : Character} {Z B T U q : ℝ} {v : O}
    (hZ : 1 < Z) (hU : 0 < U)
    (P : ReturnedPartAt M H hH q base eta (Z^U) B T v) :
    ReturnedPartAt M H hH q base eta Z (U*B) T v where
  unit := P.unit
  record := fun b => rebaseHighRecord M H hH (zero_lt_one.trans hZ) (P.record b)
  scale := U*P.scale
  length := U*P.length
  amp := U*P.amp
  loss := U*P.loss
  pays := fun b => rebaseHighRecord_pays hZ hU (P.record b)
    q P.scale P.length P.amp P.loss (P.pays b)

/-- Exact absolute count conservation for the returned part, with no
additional factor depending on its energy scale. -/
theorem rebaseReturnedPart_value {Base : Type} {base : Character → Base → Character}
    {eta : Character} {Z B T U q : ℝ} {v : O}
    (hZ : 1 < Z) (hU : 0 < U)
    (P : ReturnedPartAt M H hH q base eta (Z^U) B T v) :
    (rebaseReturnedPart hZ hU P).value = P.value := by
  unfold ReturnedPartAt.value
  apply Finset.sum_congr rfl
  intro b _
  exact rebaseHighRecord_value (zero_lt_one.trans hZ) (P.record b)

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.rebaseHighRecord_value
#print axioms OAI.SevenEighths.Cycle153RegionalLow.rebaseHighRecord_pays

#print axioms OAI.SevenEighths.Cycle153RegionalLow.rebaseReturnedPart_value
