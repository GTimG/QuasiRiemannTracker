import Candidate.Cycle63.Physical.FinalLow.Chain
import Candidate.Cycle63.Physical.FinalCapacity.Geometry

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.SevenEighths.Cycle63FinalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentCompleteCommon CenteredMomentSecondHeightFamily ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentSecondExceptionalFamily
open CenteredMomentSecondPhysicalBlock CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentCommonRadialData CenteredMomentCommonRawScale
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open Cycle63FinalNatural Cycle63FinalCapacity
variable {α : Type*} [Fintype α] [DecidableEq α]

def mainRadius {s : Input α} (q : Chain s) (D₁ : Ideal O) (E : Finset (CommonIndex q.C₁ D₁))
    (Z Mrow amp δ reserve ξ b : ℝ) (N : ℕ) : ℝ :=
  frequencyRadius ((b^N*volume s/(q.C₁.absNorm:ℝ))^2/
    mainCommonRadius Z (Real.logb Z (D₁.absNorm:ℝ))
      (nominalLog q.C₁ D₁ (Ideal.span {primeSubsetGenerator (fun j:CommonIndex q.C₁ D₁=>j.val) E})
        (Z^Mrow) (volume s) Z) (Real.logb Z (q.C₁.absNorm:ℝ)) (3*amp) δ reserve) Z ξ

/-- Genuine main second-transform data. Every field is a physical support,
 character, coefficient or radius identity; no norm or capacity estimate. -/
structure MainGeometry (s : Input α) (q : Chain s) (Z Mrow amp omega ξ b : ℝ) (N : ℕ) where
  D₁ : Ideal O
  hC₁ : Supported q.C₁
  hD₁ : Supported D₁
  heq₁ : primeSupport q.C₁=primeSupport D₁
  E : Finset (CommonIndex q.C₁ D₁)
  hmod : q.η₁.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
    Ideal.span {primeSubsetGenerator (fun j:CommonIndex q.C₁ D₁=>j.val) E*activeConductor q.C₁ D₁}
  δ : ℝ
  reserve : ℝ
  homega : δ+reserve=omega
  C : Ideal O
  D : Ideal O
  hC : Supported C
  hD : Supported D
  heq : primeSupport C=primeSupport D
  U : Finset (CommonIndex C D)
  τ : RayFourExpansion.RayCharacter→ Character
  family : Family q.η₁ C D hC hD U τ
  label : q.E₂=C ∨ q.E₂=D
  first_nonzero : frozenCoefficient q.B₁.val q.C₁ q.R₁ s.ν s.W s.P≠0
  second_nonzero : frozenCoefficient q.B₂.val q.E₂ q.R₂ q.first.ν q.first.W q.first.P≠0
  cols : Finset (Ideal O)
  coefficient : Ideal O→ℂ
  frequencies : Finset O
  profile : 𝓢(ℝ,ℂ)
  scale : ℝ
  scale_pos : 0<scale
  bin : Fin 4→ℤ
  block_nonzero : physicalBlock q.η₁ q.t₁ cols coefficient C D hC hD U
    (mainRadius q D₁ E Z Mrow amp δ reserve ξ b N) frequencies profile scale bin≠0

end
end OAI.SevenEighths.Cycle63FinalLow
