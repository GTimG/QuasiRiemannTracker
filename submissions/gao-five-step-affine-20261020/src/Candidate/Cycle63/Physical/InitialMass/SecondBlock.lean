import Candidate.Cycle63.Moment.ActualJointKernel
import Candidate.Cycle63.Moment.JointWindowFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorChildren
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondRadicalBlock CenteredMomentSectorLocalization
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentMobiusRegroup CenteredMomentChildAssembly CenteredMomentFixedRay
open CenteredMomentSecondScaled CenteredMomentSourceRow Cycle63Moment RayFourExpansion
open CenteredMomentSupport CenteredMomentCauchy
local notation "O" => HeckeFamily.O

/-- Literal retained second-block data. The canonical partition remains
inside its signed weight throughout the joint expansion. -/
structure SecondBlockSource where
  character : Character
  height : ℝ
  pool : Finset (Ideal O)
  beta : Ideal O→ℂ
  C : Ideal O
  D : Ideal O
  hC : Supported C
  hD : Supported D
  sameSupport : primeSupport C=primeSupport D
  inactive : Finset (CommonIndex C D)
  radius : ℝ
  rows : Finset O
  rows_ne : ∀z∈rows,z≠0
  K : ℝ
  K_pos : 0<K
  dyad : Fin 4→ℤ

def SecondBlockSource.frequency (s : SecondBlockSource) :=
  commonFrequencyGenerator s.C s.D*nonunitFrequencyGenerator s.C s.D s.inactive
abbrev SecondBlockSource.divisors (s : SecondBlockSource) :=
  divisorPool Finset.univ (fun J : sectorPool s.D s.hD.1 s.pool=>(J:Ideal O))
def SecondBlockSource.ratio (s : SecondBlockSource) :=
  dyadicScale (s.dyad 0)*dyadicScale (s.dyad 1)/(dyadicScale (s.dyad 2)*dyadicScale (s.dyad 3))
def SecondBlockSource.rho (s : SecondBlockSource) :=
  Real.log (secondEffectiveScale s.C s.D s.frequency s.K/dyadicScale (s.dyad 0))
def SecondBlockSource.x (s : SecondBlockSource) (z : O) :=
  Real.log (normValue z/dyadicScale (s.dyad 1))
def SecondBlockSource.rowWeight (s : SecondBlockSource) (z : O) :=
  retainedScalar s.C s.D s.inactive s.radius z*idealCorrelation s.C s.D s.hC s.hD (s.frequency*z)

def SecondBlockSource.sector (s : SecondBlockSource) (L : Ideal O) (χ ψ : RayCharacter) :
    CanonicalSectorSource where
  C := s.C
  D := s.D
  supportedC := s.hC
  supportedD := s.hD
  sameSupport := s.sameSupport
  pool := s.pool
  coefficient := s.beta
  character := s.character
  height := s.height
  frequency := s.frequency
  projector := L
  leftRay := χ
  rightRay := ψ
  leftScale := dyadicScale (s.dyad 2)
  rightScale := dyadicScale (s.dyad 3)

def secondSectorTerm (s : SecondBlockSource) (W : 𝓢(ℝ,ℂ))
    (L : Ideal O) (χ ψ : RayCharacter) (z : O) : ℂ :=
  let src := s.sector L χ ψ
  src.signedWeight (s.rowWeight z)*
    ∑I : src.LeftIndex,∑J : src.RightIndex,
      ((src.leftCoefficient I*idealRowHom z I)*star (src.rightCoefficient J*idealRowHom (-z) J))*
        wholeKernel W (fun _=>logAnnulus) s.ratio s.rho (s.x z) (src.leftLog I) (src.rightLog J)

/-- Exact second-transform expansion, before any Cauchy inequality,
absolute values or estimates of individual source labels. -/
theorem actual_second_block_expression (s : SecondBlockSource) (W : 𝓢(ℝ,ℂ)) :
    normalizedBlock s.character s.height s.pool s.beta s.C s.D s.hC s.hD s.inactive
      s.radius s.rows W s.K s.dyad=
      ∑L∈s.divisors,∑χ : RayCharacter,∑ψ : RayCharacter,∑z∈s.rows,
        secondSectorTerm s W L χ ψ z := by
  have he := sector_correlation_children s.character s.height s.pool s.beta s.C s.D s.hC s.hD
    s.sameSupport s.frequency s.rows
    (retainedScalar s.C s.D s.inactive s.radius)
    (fun z I J=>wholeKernel W (fun _=>logAnnulus) s.ratio s.rho (s.x z)
      (Real.log ((I.absNorm:ℝ)/dyadicScale (s.dyad 2)))
      (Real.log ((J.absNorm:ℝ)/dyadicScale (s.dyad 3))))
  apply he.trans
  simp only [Finset.mul_sum,secondSectorTerm,SecondBlockSource.sector,
    CanonicalSectorSource.signedWeight,CanonicalSectorSource.leftCoefficient,
    CanonicalSectorSource.rightCoefficient,CanonicalSectorSource.leftLog,
    CanonicalSectorSource.rightLog,SecondBlockSource.rowWeight]
  refine Finset.sum_congr rfl fun L hL => Finset.sum_congr rfl fun χ hχ => Finset.sum_congr rfl fun ψ hψ => Finset.sum_congr rfl fun z hz => Finset.sum_congr rfl fun I hI => Finset.sum_congr rfl fun J hJ => ?_
  ring

theorem actual_second_physical_block_expression (s : SecondBlockSource) (W : 𝓢(ℝ,ℂ)) :
    physicalBlock s.character s.height s.pool s.beta s.C s.D s.hC s.hD s.inactive
      s.radius s.rows W s.K s.dyad=
      (outerScalar s.C s.D s.K s.dyad:ℂ)*(normalizer s.C s.D s.inactive:ℂ)*
        ∑L∈s.divisors,∑χ : RayCharacter,∑ψ : RayCharacter,∑z∈s.rows,
          secondSectorTerm s W L χ ψ z := by
  rw [physicalBlock_eq _ _ _ _ _ _ _ _ _ _ _ s.rows_ne _ _ s.K_pos,
    actual_second_block_expression]

theorem actual_second_row_weight_norm (s : SecondBlockSource) (z : O) :
    ‖s.rowWeight z‖≤1 :=
  actual_retained_scalar_norm s.C s.D s.hC s.hD s.sameSupport s.inactive s.radius z

end
end OAI.SevenEighths.Cycle63InitialMass
