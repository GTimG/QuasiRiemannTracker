import Candidate.Cycle63.Physical.InitialMass.SecondActive
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonSectorWindow

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonSectorWindow
open CenteredMomentCommonWindowColumn CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentChildAssembly CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth CenteredMomentCauchy
open CenteredMomentLogDyadic CenteredMomentConjugateWindow
open Cycle63Moment RayFourExpansion
local notation "O" => HeckeFamily.O
local instance secondWindowsDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def originalSecondSector (s : Input ι) (R seed : Ideal O) (η : Character) (t : ℝ)
    (A : O) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (L : Ideal O) (χ ψ : RayCharacter)
    (X Y : ℝ) : CanonicalSectorSource where
  C := C
  D := D
  supportedC := hC
  supportedD := hD
  sameSupport := hCD
  pool := finiteColumns (Fintype.piFinset s.pools)
  coefficient := finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  character := η
  height := t
  frequency := A
  projector := L
  leftRay := χ
  rightRay := ψ
  leftScale := X
  rightScale := Y

omit [DecidableEq ι] in
theorem actual_second_left_window (s : Input ι) (R seed : Ideal O) (η τ : Character)
    (t θ X Y : ℝ) (A z : O) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (L : Ideal O) (χ ψ : RayCharacter)
    (V : ℝ→ℂ)
    (hτ : ∀I : Ideal O,Supported I → IsCoprime C I → ∀v : ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) :
    let src := originalSecondSector s R seed η t A C D hC hD hCD L χ ψ X Y
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
      leftColumn Finset.univ (fun I=>src.leftCoefficient I*idealRowHom z I) V src.leftLog θ=
        windowColumn s C hC R seed L τ t θ X V z := by
  dsimp only
  rw [←actual_sector_window s η τ χ A C hC R seed L t θ X V z hτ]
  congr 1
  simp only [leftColumn,rowPolynomial,CanonicalSectorSource.leftCoefficient,
    CanonicalSectorSource.leftLog,originalSecondSector,CenteredMomentSecondSectorColumns.sectorElement_span]
  apply Finset.sum_congr rfl
  intro I hI
  ring

omit [DecidableEq ι] in
theorem actual_second_right_window (s : Input ι) (R seed : Ideal O) (η τ : Character)
    (t θ X Y : ℝ) (A z : O) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (L : Ideal O) (χ ψ : RayCharacter)
    (V : ℝ→ℂ)
    (hτ : ∀I : Ideal O,Supported I → IsCoprime D I → ∀v : ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter ψ⁻¹ (primaryGenerator I)) :
    let src := originalSecondSector s R seed η t A C D hC hD hCD L χ ψ X Y
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
      rightColumn Finset.univ (fun I=>src.rightCoefficient I*idealRowHom (-z) I) V src.rightLog θ=
        star (windowColumn s D hD R seed L τ t (-θ) Y (fun x=>star (V x)) (-z)) := by
  dsimp only
  rw [←actual_sector_window s η τ ψ⁻¹ A D hD R seed L t (-θ) Y (fun x=>star (V x)) (-z) hτ]
  have hs : star ((Real.sqrt (volume s.toData):ℂ)⁻¹)=
      (Real.sqrt (volume s.toData):ℂ)⁻¹ := by simp
  simp only [rightColumn,rowPolynomial,CanonicalSectorSource.rightCoefficient,
    CanonicalSectorSource.rightLog,originalSecondSector,
    CenteredMomentSecondSectorColumns.sectorElement_span,star_mul,star_sum,hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [←star_columnPhase,star_star]
  ring

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_left_window
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_right_window
