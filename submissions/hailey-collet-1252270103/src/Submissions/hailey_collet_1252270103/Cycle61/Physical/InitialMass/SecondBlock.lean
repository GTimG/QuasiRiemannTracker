import Submissions.hailey_collet_1252270103.Cycle61.Moment.ActualJointKernel
import Submissions.hailey_collet_1252270103.Cycle61.Moment.JointWindowFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
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
open CenteredMomentSecondScaled CenteredMomentSourceRow Cycle61Moment RayFourExpansion
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
  apply Finset.sum_congr rfl
  intro L hL
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ψ hψ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
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

/-- The literal second-sector terms, jointly over all source labels and
rows in one ratio group. Scalar factors stay inside their column energies. -/
theorem actual_joint_second_block_bound (W : 𝓢(ℝ,ℂ)) (A J : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r : ℝ, 0<r →
      ∀ {Label : Type*} [Fintype Label] [DecidableEq Label]
        (s : Label→SecondBlockSource) (L : Label→Ideal O) (χ ψ : Label→RayCharacter)
        (rows : Finset (Label×O)) (a b : Label×O→ℂ),
      (∀k∈rows,(s k.1).ratio=r) → ∀ E : ℝ, 0≤E →
      (∀t : ℝ,
        Real.sqrt (∑k∈rows,‖leftColumn Finset.univ
          (actualJointLeft (fun l=>(s l).sector (L l) (χ l) (ψ l)) a k)
          logAnnulus ((s k.1).sector (L k.1) (χ k.1) (ψ k.1)).leftLog t‖^2)*
        Real.sqrt (∑k∈rows,‖rightColumn Finset.univ
          (actualJointRight (fun l=>(s l).sector (L l) (χ l) (ψ l)) b k)
          logAnnulus ((s k.1).sector (L k.1) (χ k.1) (ψ k.1)).rightLog t‖^2)≤
        E*(1+‖t‖)^J) →
      (1+r)^A*‖∑k∈rows,a k*star (b k)*
        secondSectorTerm (s k.1) W (L k.1) (χ k.1) (ψ k.1) k.2‖≤C*E := by
  obtain ⟨C,hC,hbound⟩ := actual_joint_sector_kernel_bound W (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num))
    (fun _ _ hn=>CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure _ hn) A J
  refine ⟨C,hC,?_⟩
  intro r hr Label _ _ s L χ ψ rows a b hratio E hE he
  have hh := hbound r hr (fun l=>(s l).sector (L l) (χ l) (ψ l)) rows a b
    (fun k=>(s k.1).rowWeight k.2) (fun k=>(s k.1).rho) (fun k=>(s k.1).x k.2)
    (fun k _=>actual_second_row_weight_norm _ _) (fun _ _=>logAnnulus_norm _)
    (fun _ _=>logAnnulus_norm _) E hE he
  convert hh using 2
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [secondSectorTerm,hratio k hk,actualJointLeft,actualJointRight,
    star_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_block_expression
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_physical_block_expression
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_row_weight_norm
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_second_block_bound
