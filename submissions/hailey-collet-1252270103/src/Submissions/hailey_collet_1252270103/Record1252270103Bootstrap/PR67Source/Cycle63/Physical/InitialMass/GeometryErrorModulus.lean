import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryErrorActiveInput
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondRadicalBudget
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows CenteredMomentAmplificationRadicalFamily
open CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentAmplificationErrorEnergy CenteredMomentSecondRadicalBudget
local notation "O" => HeckeFamily.O

/-- The conductor furnished by actual amplification has one uniform
fixed factor and exactly the moving-prime power used in the error geometry. -/
theorem actual_error_moving_modulus (η υ : Character)(ψ : RayCharacter)
    (p : O)(hp : p≠0)(Z : ℝ)(hZ : 1<Z)(i : Fin 3)
    (hυ : υ.modulus.absNorm≤ radicalBound (childCharacter η ψ) fixedBadMask p
      (errorMovingExponent (errorIndex i))) :
    (υ.modulus.absNorm:ℝ)≤(fixedFactor:ℝ)*(η.modulus.absNorm:ℝ)*
      Z^(errorMoving p Z (errorIndex i+1)) := by
  have hh : (υ.modulus.absNorm:ℝ)≤
      (radicalBound (childCharacter η ψ) fixedBadMask p (errorMovingExponent (errorIndex i)):ℝ) := by
    exact_mod_cast hυ
  rw [radicalBound_error_power _ _ p hp Z hZ (errorIndex i) (errorIndex_cases i)] at hh
  have hm : ((childCharacter η ψ).modulus.absNorm:ℝ)≤
      (η.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm := by
    exact_mod_cast child_modulus_bound η ψ
  apply hh.trans
  calc
    _≤(((η.modulus.absNorm:ℝ)*(Ideal.span {(12:O)}).absNorm)*
        (Ideal.span {fixedBadMask}).absNorm*(Ideal.span {(72:O)}).absNorm)*
          Z^(errorMoving p Z (errorIndex i+1)) := by
      have hz : 0<Z := zero_lt_one.trans hZ
      gcongr
    _=_ := by simp only [fixedFactor,Nat.cast_mul];ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
