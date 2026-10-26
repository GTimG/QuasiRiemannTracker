/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The logarithmic geometry is derived from actual ideal and numerator identities,
not asserted as a replacement source hypothesis. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103CommonGeometry.FourStrata

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103CommonGeometry
noncomputable section
open scoped Classical BigOperators
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentSecondCanonical CenteredMomentRankinRadical
open CanonicalQuadraticSieve Cycle61Moment
local notation "O" => ActualEisensteinCubic.O

def normLog (Z : ℝ) (I : Ideal O) : ℝ := Real.logb Z (I.absNorm:ℝ)

def stratumWidth (Z : ℝ) (C D : Ideal O) (m n : ℕ) : ℝ :=
  normLog Z (stratumRadical C D m n)

theorem normLog_mul (Z : ℝ) (I J : Ideal O) (hI : I≠0) (hJ : J≠0) :
    normLog Z (I*J)=normLog Z I+normLog Z J := by
  unfold normLog
  rw [map_mul,Nat.cast_mul,Real.logb_mul
    (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI))
    (Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ))]

theorem normLog_pow (Z : ℝ) (I : Ideal O) (n : ℕ) :
    normLog Z (I^n)=(n:ℝ)*normLog Z I := by
  simp only [normLog,map_pow,Nat.cast_pow,Real.logb_pow]

theorem normLog_nonneg (Z : ℝ) (hZ : 1<Z) (I : Ideal O) (hI : I≠0) :
    0≤normLog Z I := by
  apply Real.logb_nonneg hZ
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem stratumWidth_nonneg (Z : ℝ) (hZ : 1<Z) (C D : Ideal O) (m n : ℕ) :
    0≤stratumWidth Z C D m n :=
  normLog_nonneg Z hZ _ (stratumRadical_ne_zero C D m n)

theorem left_common_width (Z : ℝ) (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    normLog Z (commonPart C D)=stratumWidth Z C D 1 1+stratumWidth Z C D 1 2+
      2*stratumWidth Z C D 2 1+2*stratumWidth Z C D 2 2 := by
  rw [common_left_four_strata C D hC hD]
  simp only [normLog_mul Z _ _ (mul_ne_zero
      (mul_ne_zero (stratumRadical_ne_zero C D 1 1) (stratumRadical_ne_zero C D 1 2))
      (pow_ne_zero 2 (stratumRadical_ne_zero C D 2 1)))
      (pow_ne_zero 2 (stratumRadical_ne_zero C D 2 2)),
    normLog_mul Z _ _ (mul_ne_zero (stratumRadical_ne_zero C D 1 1)
      (stratumRadical_ne_zero C D 1 2)) (pow_ne_zero 2 (stratumRadical_ne_zero C D 2 1)),
    normLog_mul Z _ _ (stratumRadical_ne_zero C D 1 1) (stratumRadical_ne_zero C D 1 2),
    normLog_pow,stratumWidth,Nat.cast_ofNat]

theorem right_common_width (Z : ℝ) (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    normLog Z (commonPart D C)=stratumWidth Z C D 1 1+2*stratumWidth Z C D 1 2+
      stratumWidth Z C D 2 1+2*stratumWidth Z C D 2 2 := by
  rw [common_right_four_strata C D hC hD]
  simp only [normLog_mul Z _ _ (mul_ne_zero
      (mul_ne_zero (stratumRadical_ne_zero C D 1 1) (pow_ne_zero 2 (stratumRadical_ne_zero C D 1 2)))
      (stratumRadical_ne_zero C D 2 1)) (pow_ne_zero 2 (stratumRadical_ne_zero C D 2 2)),
    normLog_mul Z _ _ (mul_ne_zero (stratumRadical_ne_zero C D 1 1)
      (pow_ne_zero 2 (stratumRadical_ne_zero C D 1 2))) (stratumRadical_ne_zero C D 2 1),
    normLog_mul Z _ _ (stratumRadical_ne_zero C D 1 1) (pow_ne_zero 2 (stratumRadical_ne_zero C D 1 2)),
    normLog_pow,stratumWidth,Nat.cast_ofNat]

theorem common_radical_width (Z : ℝ) (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    normLog Z (commonRadical C D)=stratumWidth Z C D 1 1+stratumWidth Z C D 1 2+
      stratumWidth Z C D 2 1+stratumWidth Z C D 2 2 := by
  rw [common_radical_four_strata C D hC hD]
  simp only [normLog_mul Z _ _ (mul_ne_zero
      (mul_ne_zero (stratumRadical_ne_zero C D 1 1) (stratumRadical_ne_zero C D 1 2))
      (stratumRadical_ne_zero C D 2 1)) (stratumRadical_ne_zero C D 2 2),
    normLog_mul Z _ _ (mul_ne_zero (stratumRadical_ne_zero C D 1 1)
      (stratumRadical_ne_zero C D 1 2)) (stratumRadical_ne_zero C D 2 1),
    normLog_mul Z _ _ (stratumRadical_ne_zero C D 1 1) (stratumRadical_ne_zero C D 1 2),stratumWidth]

theorem active_width (Z : ℝ) (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    normLog Z (Ideal.span {activeConductor C D})=
      stratumWidth Z C D 1 2+stratumWidth Z C D 2 1 := by
  rw [active_conductor_two_strata C D hC hD,
    normLog_mul Z _ _ (stratumRadical_ne_zero C D 1 2) (stratumRadical_ne_zero C D 2 1)]
  rfl

theorem left_numerator_width (Z : ℝ) (C D : Ideal O) (hCs : Supported C)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    normLog Z (Ideal.span {firstLeftUncancelled C D})=2*stratumWidth Z C D 2 1 := by
  rw [left_numerator_stratum C D hCs hC hD,normLog_pow]
  rfl

theorem right_numerator_width (Z : ℝ) (C D : Ideal O) (hCs : Supported C)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    normLog Z (Ideal.span {firstRightUncancelled C D})=2*stratumWidth Z C D 1 2 := by
  rw [right_numerator_stratum C D hCs hC hD,normLog_pow]
  rfl

theorem left_cancelled_width (Z : ℝ) (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    normLog Z (firstLeftCancelledRadical C D)=stratumWidth Z C D 1 2 := by
  rw [left_cancelled_stratum C D hC hD]
  rfl

theorem right_cancelled_width (Z : ℝ) (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    normLog Z (firstRightCancelledRadical C D)=stratumWidth Z C D 2 1 := by
  rw [right_cancelled_stratum C D hC hD]
  rfl

/-- The exact restored signed-row exponent; the parameter F may be set
to 1−6a, with frequency and rounding losses kept separately. -/
theorem restored_raw_exponent (Z F : ℝ) (C D : Ideal O) (hCs : Supported C)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    F-normLog Z (Ideal.span {activeConductor C D})-
        max (normLog Z (commonPart C D)-normLog Z (commonPart D C)) 0+
        normLog Z (Ideal.span {firstLeftUncancelled C D})=
      F-max (normLog Z (commonPart D C)-normLog Z (commonPart C D)) 0 := by
  rw [active_width Z C D hC hD,left_numerator_width Z C D hCs hC hD,
    left_common_width Z C D hC hD,right_common_width Z C D hC hD]
  rw [max_def,max_def]
  split_ifs <;> linarith

theorem restored_raw_exponent_right (Z F : ℝ) (C D : Ideal O) (hCs : Supported C)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    F-normLog Z (Ideal.span {activeConductor C D})-
        max (normLog Z (commonPart D C)-normLog Z (commonPart C D)) 0+
        normLog Z (Ideal.span {firstRightUncancelled C D})=
      F-max (normLog Z (commonPart C D)-normLog Z (commonPart D C)) 0 := by
  rw [active_width Z C D hC hD,right_numerator_width Z C D hCs hC hD,
    left_common_width Z C D hC hD,right_common_width Z C D hC hD]
  rw [max_def,max_def]
  split_ifs <;> linarith

theorem deficit_bounds (Z : ℝ) (hZ : 1<Z) (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    let δ := max (normLog Z (commonPart D C)-normLog Z (commonPart C D)) 0
    δ≤stratumWidth Z C D 1 2 ∧ δ≤normLog Z (commonPart C D) ∧
      2*δ≤normLog Z (commonPart D C) := by
  dsimp only
  rw [left_common_width Z C D hC hD,right_common_width Z C D hC hD]
  have hA := stratumWidth_nonneg Z hZ C D 1 1
  have hB := stratumWidth_nonneg Z hZ C D 1 2
  have hC' := stratumWidth_nonneg Z hZ C D 2 1
  have hD' := stratumWidth_nonneg Z hZ C D 2 2
  rw [max_def]
  split_ifs <;> refine ⟨?_,?_,?_⟩ <;> linarith

theorem allowance_and_sigma (Z : ℝ) (hZ : 1<Z) (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D) :
    let c := normLog Z (commonPart C D)
    let d := normLog Z (commonPart D C)
    let R := normLog Z (Ideal.span {activeConductor C D})
    let p := normLog Z (commonRadical C D)
    max (3*c-5*d-R) 0/6=0 ∧ max (3*d-5*c-R) 0/6=0 ∧
      (c+d-2*p-R)/2=stratumWidth Z C D 2 2 := by
  dsimp only
  rw [left_common_width Z C D hC hD,right_common_width Z C D hC hD,
    active_width Z C D hC hD,common_radical_width Z C D hC hD]
  have hA := stratumWidth_nonneg Z hZ C D 1 1
  have hB := stratumWidth_nonneg Z hZ C D 1 2
  have hC' := stratumWidth_nonneg Z hZ C D 2 1
  have hD' := stratumWidth_nonneg Z hZ C D 2 2
  rw [max_eq_right (by linarith),max_eq_right (by linarith)]
  constructor
  · norm_num
  constructor
  · norm_num
  · ring

/-- Divisibility of the complete right common ideal into the actual right
column supplies the width cap used with 2δ≤d. -/
theorem common_right_width_le_column (Z : ℝ) (hZ : 1<Z) (I J : Ideal O) (hJ : J≠0) :
    normLog Z (commonPart J I)≤normLog Z J := by
  apply Real.logb_le_logb_of_le hZ
    (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero J I)))
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ))
    (map_dvd Ideal.absNorm (commonPart_dvd J I hJ))

theorem raw_exponent_lower (Z F T : ℝ) (hZ : 1<Z) (C D : Ideal O)
    (hC : ValuationAtMostTwo C) (hD : ValuationAtMostTwo D)
    (hT : normLog Z (commonPart D C)≤T) :
    F-T/2≤F-max (normLog Z (commonPart D C)-normLog Z (commonPart C D)) 0 := by
  have h := (deficit_bounds Z hZ C D hC hD).2.2
  linarith

end
end OAI.SevenEighths.Record1252270103CommonGeometry

#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.restored_raw_exponent
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.restored_raw_exponent_right
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.deficit_bounds
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.allowance_and_sigma
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.common_right_width_le_column
#print axioms OAI.SevenEighths.Record1252270103CommonGeometry.raw_exponent_lower
