/- Copyright (c) 2026 Sil. Apache-2.0.
The moving initial profile is replaced by ONE diagonalControl factor
and fixed ballProfile, used only after the root centering dispatch.
The full energy remains an actual expression, not an assumed estimate.

-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RecenteredRootReferenceFamily
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.FixedRadialSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RecenteredRootFixedMajorant
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentAbsoluteEnergy CenteredMomentHeckeExpansion
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentNaturalFixedRaySource CenteredMomentDetectorEnergyInitialState
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFixedRadialSource
open MixedInnerExceptionalBlock CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedPrincipalWindow MixedFirstRebase MixedLiveNormalization
open MixedFirstReferenceEnergy RestoredInitialSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {α : Type u} [Fintype α] {a b : ℝ}

theorem natural_row_weight (η : Character) (z : O) (hz : z≠0) (I : Id) :
    idealCoeff (naturalCharacter η z) I=rowWeight η fixedBadMask 1 z 0 I := by
  rw [naturalCharacter_eq η z hz,(naturalRow η z hz).ideal]
  change idealCoeff η I*idealRowHom (fixedBadMask^6*z) I=
    (idealCoeff η I*idealRowHom (fixedBadMask^6*(1*z)) I)*(I.absNorm:ℂ)^(Complex.I*0)
  simp only [one_mul,mul_zero,Complex.cpow_zero,mul_one]

theorem weighted_natural_norm (s : Source α a b) (ha : 0 < a) (η : Character) (z : O) (hz : z≠0) :
    ‖weightedRow s ha 1 (idealCoeff (naturalCharacter η z))‖^2=
      ‖∑I∈sourceColumns s,sourceCoefficient s ha 1 I*rowWeight η fixedBadMask 1 z 0 I‖^2/sourceVolume s := by
  unfold weightedRow
  rw [norm_mul,mul_pow,normalization_sq (s.X₁*s.X₂)
    (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)) s.P
    (fun i => zero_lt_one.trans_le (s.hP i))]
  simp_rw [natural_row_weight η z hz]
  unfold sourceVolume
  ring

theorem profile_re_le_fixed_ball (Φ : 𝓢(ℝ,ℂ)) (Z bΦ : ℝ) (hZ : 0 < Z) (hbΦ : 0 < bΦ)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Iic bΦ) (z : O) :
    (Φ (‖eisEmbedding z‖^2/Z)).re ≤
      diagonalControl Φ*(ballProfile (‖eisEmbedding z‖^2/(bΦ*Z))).re := by
  by_cases hn : Φ (‖eisEmbedding z‖^2/Z)=0
  · rw [hn,Complex.zero_re]
    exact mul_nonneg (diagonalControl_nonneg Φ) (ballProfile_nonneg _)
  · have hrad : ‖eisEmbedding z‖^2 ≤ bΦ*Z := (div_le_iff₀ hZ).mp (hs hn)
    have hone := ballProfile_one (‖eisEmbedding z‖^2/(bΦ*Z))
      (div_nonneg (sq_nonneg _) (mul_pos hbΦ hZ).le) ((div_le_one (mul_pos hbΦ hZ)).mpr hrad)
    rw [hone,Complex.one_re,mul_one]
    exact (Complex.re_le_norm _).trans (norm_le_diagonalControl Φ _)

def fullBallCost (s : Source α a b) (ha : 0 < a) (η : Character) (K : ℝ) : ℝ :=
  ‖finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s)
      (sourceCoefficient s ha 1) ballProfile K‖/sourceVolume s

theorem fullBallCost_nonneg (s : Source α a b) (ha : 0 < a) (η : Character) (K : ℝ) :
    0 ≤ fullBallCost s ha η K := div_nonneg (norm_nonneg _) (sourceVolume_pos s).le

set_option maxHeartbeats 700000 in
/-- The profile and keep are enlarged only in this positive comparison.
For high roots the caller applies it to the NEW centered Source. There
is precisely one diagonalControl(Phi), and the fixed kernel is ballProfile. -/
theorem finite_kept_le_fixed_ball (s : Source α a b) (ha : 0 < a)
    (η η₀ : Character) (Q : Id) (Φ : 𝓢(ℝ,ℂ)) (Z bΦ : ℝ)
    (hZ : 0 < Z) (hbΦ : 0 < bΦ) (hs : Function.support (Φ:ℝ→ℂ) ⊆ Iic bΦ)
    (rows : Finset O) :
    (∑z∈rows,initialWeight η η₀ Q Φ Z z*‖weightedRow s ha 1 (idealCoeff (naturalCharacter η z))‖^2) ≤
      diagonalControl Φ*fullBallCost s ha η (bΦ*Z) := by
  let f : O → ℂ := fun z => ∑I∈sourceColumns s,sourceCoefficient s ha 1 I*rowWeight η fixedBadMask 1 z 0 I
  let g : O → ℝ := fun z => ‖f z‖^2*(ballProfile (‖eisEmbedding z‖^2/(bΦ*Z))).re
  have hg : ∀z,0 ≤ g z := fun z => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _)
  have hsum := finite_hecke_energy_summable η fixedBadMask 1 0 (sourceColumns s)
    (sourceCoefficient s ha 1) ballProfile (bΦ*Z) (mul_pos hbΦ hZ)
  have hre : HasSum g (finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s)
      (sourceCoefficient s ha 1) ballProfile (bΦ*Z)).re := by
    have hh := Complex.hasSum_re hsum.hasSum
    simpa only [f,g,finiteHeckeEnergy,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using hh
  have hp (z : O) :
      initialWeight η η₀ Q Φ Z z*‖weightedRow s ha 1 (idealCoeff (naturalCharacter η z))‖^2 ≤
        diagonalControl Φ*g z/sourceVolume s := by
    by_cases hk : initialKeep η (internalQ Q η₀) z
    · rw [initialWeight,if_pos hk,weighted_natural_norm s ha η z hk.1]
      have he := mul_le_mul_of_nonneg_right (profile_re_le_fixed_ball Φ Z bΦ hZ hbΦ hs z)
        (div_nonneg (sq_nonneg ‖f z‖) (sourceVolume_pos s).le)
      convert he using 1 <;> dsimp only [f,g] <;> ring
    · simp only [initialWeight,hk,ite_false,zero_mul]
      exact div_nonneg (mul_nonneg (diagonalControl_nonneg Φ) (hg z)) (sourceVolume_pos s).le
  calc
    _ ≤ ∑z∈rows,diagonalControl Φ*g z/sourceVolume s := Finset.sum_le_sum (fun z _ => hp z)
    _ = diagonalControl Φ*(∑z∈rows,g z)/sourceVolume s := by
      simp only [Finset.mul_sum,Finset.sum_div]
    _ ≤ diagonalControl Φ*(finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s)
        (sourceCoefficient s ha 1) ballProfile (bΦ*Z)).re/sourceVolume s := by
      apply div_le_div_of_nonneg_right _ (sourceVolume_pos s).le
      exact mul_le_mul_of_nonneg_left
        ((hre.summable.sum_le_tsum rows (fun z _ => hg z)).trans_eq hre.tsum_eq)
        (diagonalControl_nonneg Φ)
    _ ≤ _ := by
      unfold fullBallCost
      exact (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (diagonalControl_nonneg Φ))
          (sourceVolume_pos s).le).trans_eq (by ring)

/-- The kept reference contributes no second profile factor. -/
theorem radialControl_le_diagonalControl (Φ : 𝓢(ℝ,ℂ)) : radialControl Φ ≤ diagonalControl Φ := by
  have hs : SchwartzMap.seminorm ℝ 0 0 Φ ≤
      (Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ :=
    Seminorm.le_def.mp (Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ)
      (by simp : (0,0)∈Finset.Iic (2,0))) Φ
  have hs' : radialControl Φ ≤ (Finset.Iic (2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ := by
    simpa only [radialControl,sourceControl,Finset.sup_singleton,schwartzSeminormFamily] using hs
  apply hs'.trans
  unfold diagonalControl
  exact le_mul_of_one_le_left (by positivity) (by nlinarith [Real.pi_nonneg])

end
end Candidate.FourthPower.RecenteredRootFixedMajorant
