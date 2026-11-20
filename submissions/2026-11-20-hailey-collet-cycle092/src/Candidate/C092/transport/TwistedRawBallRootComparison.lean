/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Colored positive comparison; adapted from Sil's RecenteredRootFixedMajorant.
   The original keep and its character are independent of the common row anchor. -/
import Candidate.C092.transport.TwistedRawBallRootProducer
import Submissions.sil_density_split_20261026.CubeFree.FP.RecenteredRootFixedMajorant
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBallRootProducer
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcreteTraceCRT CenteredMomentLattice CenteredMomentAddedZeroUniform
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRow
open CenteredMomentAbsoluteEnergy CenteredMomentHeckeExpansion
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalPair MixedPrincipalWindow MixedLiveNormalization MixedInnerExceptionalBlock RestoredInitialSource
open RecenteredRootFixedMajorant
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def coloredWeightedRow (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id→ℂ)
    (χ : Character) : ℂ :=
  normalization (s.X₁*s.X₂) s.P *
    ∑I∈sourceColumns s,sourceColumn s ha ω₁ ω₂ 1 I*idealCoeff χ I

def coloredFullBallCost (s : Source ι a b) (ha : 0 < a) (ω₁ ω₂ : Id→ℂ)
    (η : Character) (K : ℝ) : ℝ :=
  ‖finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s)
    (sourceColumn s ha ω₁ ω₂ 1) ballProfile K‖ / sourceVolume s

theorem colored_weighted_natural_norm (s : Source ι a b) (ha : 0 < a)
    (ω₁ ω₂ : Id→ℂ) (η : Character) (z : O) (hz : z≠0) :
    ‖coloredWeightedRow s ha ω₁ ω₂ (naturalCharacter η z)‖^2 =
      ‖∑I∈sourceColumns s,sourceColumn s ha ω₁ ω₂ 1 I*
        rowWeight η fixedBadMask 1 z 0 I‖^2/sourceVolume s := by
  unfold coloredWeightedRow
  rw [norm_mul,mul_pow,normalization_sq (s.X₁*s.X₂)
    (mul_pos (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)) s.P
    (fun i => zero_lt_one.trans_le (s.hP i))]
  simp_rw [natural_row_weight η z hz]
  unfold sourceVolume
  ring

/-- Both independent colors stay in the source, while the caller's original
    keep (with its own character) is retained throughout the positive sum. -/
theorem colored_finite_kept_le_fixed_ball (s : Source ι a b) (ha : 0 < a)
    (ω₁ ω₂ : Id→ℂ) (η ηkeep η₀ : Character) (Q : Id) (Φ : 𝓢(ℝ,ℂ)) (Z bΦ : ℝ)
    (hZ : 0 < Z) (hbΦ : 0 < bΦ) (hs : Function.support (Φ:ℝ→ℂ) ⊆ Iic bΦ)
    (rows : Finset O) :
    (∑z∈rows,initialWeight ηkeep η₀ Q Φ Z z*
      ‖coloredWeightedRow s ha ω₁ ω₂ (naturalCharacter η z)‖^2) ≤
      diagonalControl Φ*coloredFullBallCost s ha ω₁ ω₂ η (bΦ*Z) := by
  let f : O → ℂ := fun z => ∑I∈sourceColumns s,
    sourceColumn s ha ω₁ ω₂ 1 I*rowWeight η fixedBadMask 1 z 0 I
  let g : O → ℝ := fun z => ‖f z‖^2*(ballProfile (‖eisEmbedding z‖^2/(bΦ*Z))).re
  have hg : ∀z,0 ≤ g z := fun z => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _)
  have hsum := finite_hecke_energy_summable η fixedBadMask 1 0 (sourceColumns s)
    (sourceColumn s ha ω₁ ω₂ 1) ballProfile (bΦ*Z) (mul_pos hbΦ hZ)
  have hre : HasSum g (finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s)
      (sourceColumn s ha ω₁ ω₂ 1) ballProfile (bΦ*Z)).re := by
    have hh := Complex.hasSum_re hsum.hasSum
    simpa only [f,g,finiteHeckeEnergy,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using hh
  have hp (z : O) :
      initialWeight ηkeep η₀ Q Φ Z z*
        ‖coloredWeightedRow s ha ω₁ ω₂ (naturalCharacter η z)‖^2 ≤
        diagonalControl Φ*g z/sourceVolume s := by
    by_cases hk : initialKeep ηkeep
        (internalQ Q η₀) z
    · rw [initialWeight,if_pos hk,colored_weighted_natural_norm s ha ω₁ ω₂ η z hk.1]
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
        (sourceColumn s ha ω₁ ω₂ 1) ballProfile (bΦ*Z)).re/sourceVolume s := by
      apply div_le_div_of_nonneg_right _ (sourceVolume_pos s).le
      exact mul_le_mul_of_nonneg_left
        ((hre.summable.sum_le_tsum rows (fun z _ => hg z)).trans_eq hre.tsum_eq)
        (diagonalControl_nonneg Φ)
    _ ≤ _ := by
      unfold coloredFullBallCost
      exact (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (diagonalControl_nonneg Φ))
          (sourceVolume_pos s).le).trans_eq (by ring)

#print axioms colored_weighted_natural_norm
#print axioms colored_finite_kept_le_fixed_ball
end
end QRH.Cycle092.TwistedRawBallRootProducer
