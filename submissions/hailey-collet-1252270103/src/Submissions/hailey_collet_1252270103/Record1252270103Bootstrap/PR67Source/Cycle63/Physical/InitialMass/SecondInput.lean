import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondWindows
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondBatch
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonWindowColumn CenteredMomentExceptionalAmplitudePair
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst
open CenteredMomentHeckeColumnWindow CenteredMomentCauchy CenteredMomentSectorLocalization
open Cycle63Moment RayFourExpansion
local notation "O" => HeckeFamily.O
local instance secondInputDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The second block of the literal finite source polynomial. -/
def originalSecondBlock (s : Input ι) (R seed : Ideal O)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ) : SecondBlockSource where
  character := s.η
  height := s.t
  pool := finiteColumns (Fintype.piFinset s.pools)
  beta := finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  C := C
  D := D
  hC := hC
  hD := hD
  sameSupport := hCD
  inactive := U
  radius := radius
  rows := rows
  rows_ne := hrows
  K := K
  K_pos := hK
  dyad := n

omit [DecidableEq ι] in
theorem actual_original_second_left_window (s : Input ι) (R seed : Ideal O)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ) (L : Ideal O) (χ ψ : RayCharacter)
    (τ : RayCharacter→ Character) (hτ : Family s.η C D hC hD U τ)
    (z : O) (θ : ℝ) (V : ℝ→ℂ) :
    let B := originalSecondBlock s R seed C D hC hD hCD U radius rows hrows K hK n
    let src := B.sector L χ ψ
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
      leftColumn Finset.univ (fun I=>src.leftCoefficient I*idealRowHom z I) V src.leftLog θ=
        windowColumn s C hC R seed L (τ χ) s.t θ (dyadicScale (n 2)) V z := by
  exact actual_second_left_window s R seed s.η (τ χ) s.t θ
    (dyadicScale (n 2)) (dyadicScale (n 3)) _ z C D hC hD hCD L χ ψ V
    (fun I hI hc v=>hτ.height_eq χ I hI (Or.inl hc) v)

omit [DecidableEq ι] in
theorem actual_original_second_right_window (s : Input ι) (R seed : Ideal O)
    (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (U : Finset (CommonIndex C D))
    (radius : ℝ) (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (K : ℝ) (hK : 0<K) (n : Fin 4→ℤ) (L : Ideal O) (χ ψ : RayCharacter)
    (τ : RayCharacter→ Character) (hτ : Family s.η C D hC hD U τ)
    (z : O) (θ : ℝ) (V : ℝ→ℂ) :
    let B := originalSecondBlock s R seed C D hC hD hCD U radius rows hrows K hK n
    let src := B.sector L χ ψ
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
      rightColumn Finset.univ (fun I=>src.rightCoefficient I*idealRowHom (-z) I) V src.rightLog θ=
        star (windowColumn s D hD R seed L (τ ψ⁻¹) s.t (-θ) (dyadicScale (n 3))
          (fun x=>star (V x)) (-z)) := by
  exact actual_second_right_window s R seed s.η (τ ψ⁻¹) s.t θ
    (dyadicScale (n 2)) (dyadicScale (n 3)) _ z C D hC hD hCD L χ ψ V
    (fun I hI hc v=>hτ.height_eq ψ⁻¹ I hI (Or.inr hc) v)

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
