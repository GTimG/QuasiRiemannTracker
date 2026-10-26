import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.JointKernel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondSectorChildren
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PlainChildEnergy
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorChildren
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow CenteredMomentFixedRay
open CenteredMomentChildAssembly CenteredMomentCauchy CenteredMomentSmooth
open CenteredMomentSecondScaled
open CenteredMomentPlainChildEnergy RayFourExpansion
local notation "O" => HeckeFamily.O

structure CanonicalSectorSource where
  C : Ideal O
  D : Ideal O
  supportedC : Supported C
  supportedD : Supported D
  sameSupport : primeSupport C = primeSupport D
  pool : Finset (Ideal O)
  coefficient : Ideal O → ℂ
  character : Character
  height : ℝ
  frequency : O
  projector : Ideal O
  leftRay : RayCharacter
  rightRay : RayCharacter
  leftScale : ℝ
  rightScale : ℝ

abbrev CanonicalSectorSource.LeftIndex (s : CanonicalSectorSource) :=
  sectorPool s.C s.supportedC.1 s.pool
abbrev CanonicalSectorSource.RightIndex (s : CanonicalSectorSource) :=
  sectorPool s.D s.supportedD.1 s.pool

def CanonicalSectorSource.leftCoefficient (s : CanonicalSectorSource)
    (i : s.LeftIndex) : ℂ :=
  divisorCoefficient s.projector (sectorElement s.C s.supportedC.1 s.pool)
    (movingCoefficient s.frequency (sectorElement s.C s.supportedC.1 s.pool)
      (fun I => s.coefficient (s.C*I)*heightCoeff s.character s.height I)) s.leftRay i

def CanonicalSectorSource.rightCoefficient (s : CanonicalSectorSource)
    (i : s.RightIndex) : ℂ :=
  divisorCoefficient s.projector (sectorElement s.D s.supportedD.1 s.pool)
    (movingCoefficient s.frequency (sectorElement s.D s.supportedD.1 s.pool)
      (fun I => s.coefficient (s.D*I)*heightCoeff s.character s.height I)) s.rightRay⁻¹ i

def CanonicalSectorSource.leftLog (s : CanonicalSectorSource) (i : s.LeftIndex) : ℝ :=
  Real.log ((i.val.absNorm:ℝ)/s.leftScale)
def CanonicalSectorSource.rightLog (s : CanonicalSectorSource) (i : s.RightIndex) : ℝ :=
  Real.log ((i.val.absNorm:ℝ)/s.rightScale)

def CanonicalSectorSource.signedWeight (s : CanonicalSectorSource) (q : ℂ) : ℂ :=
  (UniqueFactorizationMonoid.moebius s.projector:ℂ)*
    pairCoeff (phaseTable (primaryGenerator s.C) (primaryGenerator s.D))
      s.leftRay s.rightRay*q

theorem canonical_sector_signed_weight_norm (s : CanonicalSectorSource)
    (q : ℂ) (hq : ‖q‖ ≤ 1) : ‖s.signedWeight q‖ ≤ 1 := by
  have hμ := CubicEisenstein.norm_ideal_moebius_le_one s.projector
  have hp := pairCoeff_norm_le (phaseTable (primaryGenerator s.C) (primaryGenerator s.D))
    1 (fun _ _ => phaseTable_norm _ _ _ _) s.leftRay s.rightRay
  rw [CanonicalSectorSource.signedWeight, norm_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul hμ hp (norm_nonneg _) (by positivity)) (norm_nonneg _)).trans
      (by simpa only [one_mul, mul_one] using hq)

end
end OAI.SevenEighths.Cycle63Moment

end Record1252270103Bootstrap.PR67
