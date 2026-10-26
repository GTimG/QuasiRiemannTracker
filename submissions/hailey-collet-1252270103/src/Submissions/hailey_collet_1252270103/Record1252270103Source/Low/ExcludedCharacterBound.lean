/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.ExcludedCharacter
import Submissions.hailey_collet_1252270103.Cycle61.Moment.LowBranch.Conductor

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalSource
local notation "O" => HeckeFamily.O

/-- The excluded character has the original modulus times the actual radical. -/
theorem excluded_character_modulus (χ : Character) (R : Ideal O) (hR : R≠0) :
    (excluded χ R).modulus=χ.modulus*R.radical := by
  change χ.modulus*(∏P∈CompletedGauss.primeSupport R,P)=_
  rw [primeSupport_product_radical R hR]

theorem excluded_character_norm (χ : Character) (R : Ideal O) (hR : R≠0) :
    (excluded χ R).modulus.absNorm=χ.modulus.absNorm*R.radical.absNorm :=
  Cycle61Moment.LowBranch.excluded_conductor χ R hR

theorem excluded_character_norm_le (χ : Character) (R : Ideal O) (hR : R≠0) :
    (excluded χ R).modulus.absNorm≤χ.modulus.absNorm*R.absNorm := by
  have hrad : R.radical.absNorm≤R.absNorm :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hR))
      (map_dvd Ideal.absNorm (Ideal.dvd_iff_le.mpr (Ideal.le_radical (I:=R))))
  rw [excluded_character_norm χ R hR]
  exact Nat.mul_le_mul_left _ hrad

/-- The power budget is fixed before the moving character and exclusion ideal.
No threshold or constant depends on R. -/
theorem excluded_character_power_bound (Z Bχ BR : ℝ) (hZ : 0<Z)
    (χ : Character) (R : Ideal O) (hR : R≠0)
    (hχ : (χ.modulus.absNorm:ℝ)≤Z^Bχ) (hmask : (R.absNorm:ℝ)≤Z^BR) :
    ((excluded χ R).modulus.absNorm:ℝ)≤Z^(Bχ+BR) := by
  have hn : ((excluded χ R).modulus.absNorm:ℝ)≤
      (χ.modulus.absNorm:ℝ)*(R.absNorm:ℝ) := by
    exact_mod_cast excluded_character_norm_le χ R hR
  apply hn.trans
  rw [Real.rpow_add hZ]
  exact mul_le_mul hχ hmask (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.excluded_character_modulus
#print axioms QRH.Record1252270103Low.excluded_character_norm_le
#print axioms QRH.Record1252270103Low.excluded_character_power_bound
