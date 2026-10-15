import Candidate.Cycle62.Moment.JointKernel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondSectorChildren
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PlainChildEnergy

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OAI.SevenEighths.Cycle62Moment
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

def actualJointLeft {Label : Type*} (source : Label → CanonicalSectorSource)
    (scalar : Label×O → ℂ) (k : Label×O) (i : (source k.1).LeftIndex) : ℂ :=
  scalar k*(source k.1).leftCoefficient i*idealRowHom k.2 i

def actualJointRight {Label : Type*} (source : Label → CanonicalSectorSource)
    (scalar : Label×O → ℂ) (k : Label×O) (i : (source k.1).RightIndex) : ℂ :=
  scalar k*(source k.1).rightCoefficient i*idealRowHom (-k.2) i

/-- Cauchy is applied to the actual source-coordinate × row space before any
first-label or sector-label supremum. Both scalars and the signed residual
projector remain in the literal second-transform expression. -/
theorem actual_joint_sector_kernel_bound (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {Label : Type*} [Fintype Label] [DecidableEq Label]
        (source : Label → CanonicalSectorSource)
        (rows : Finset (Label×O)) (leftScalar rightScalar q : Label×O → ℂ)
        (ρ x : Label×O → ℝ),
      (∀ k ∈ rows, ‖q k‖ ≤ 1) →
      (∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) → (∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1) →
      ∀ E : ℝ, 0 ≤ E →
      (∀ t : ℝ,
        Real.sqrt (∑ k ∈ rows,
          ‖leftColumn Finset.univ (actualJointLeft source leftScalar k) (V 2)
            (source k.1).leftLog t‖^2) *
        Real.sqrt (∑ k ∈ rows,
          ‖rightColumn Finset.univ (actualJointRight source rightScalar k) (V 3)
            (source k.1).rightLog t‖^2) ≤ E*(1+‖t‖)^J) →
      (1+R)^A * ‖∑ k ∈ rows, (source k.1).signedWeight (q k)*
        (∑ i : (source k.1).LeftIndex, ∑ j : (source k.1).RightIndex,
          (actualJointLeft source leftScalar k i * star (actualJointRight source rightScalar k j))*
            wholeKernel W V R (ρ k) (x k) ((source k.1).leftLog i)
              ((source k.1).rightLog j))‖ ≤ C*E := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_dependent_row_estimate W V M hM hV A J
  refine ⟨C,hC,?_⟩
  intro R hR Label _ _ source rows leftScalar rightScalar q ρ x hq hV₀ hV₁ E hE henergy
  exact hbound R hR (Label := Label) (κ := Label×O)
    (α := fun l => (source l).LeftIndex) (β := fun l => (source l).RightIndex)
    rows Prod.fst (actualJointLeft source leftScalar)
    (actualJointRight source rightScalar) (fun l => (source l).leftLog)
    (fun l => (source l).rightLog) ρ x (fun k => (source k.1).signedWeight (q k))
    (fun k hk => canonical_sector_signed_weight_norm _ _ (hq k hk)) hV₀ hV₁ E hE henergy

#print axioms canonical_sector_signed_weight_norm
#print axioms actual_joint_sector_kernel_bound
end
end OAI.SevenEighths.Cycle62Moment
