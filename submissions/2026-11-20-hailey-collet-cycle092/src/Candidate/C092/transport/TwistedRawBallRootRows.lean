/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   The original finite nonzero rows are a positive sub-sum of the actual colored ball. -/
import Candidate.C092.transport.TwistedRawBallRootFinite
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBallRootProducer
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ConcreteTraceCRT CenteredMomentAddedZeroUniform CenteredMomentLattice
open CenteredMomentAbsoluteEnergy CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentFirstAmplificationChoice
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalAllocations MixedPrincipalPair MixedPrincipalWindow MixedInnerExceptionalBlock
open MixedLiveNormalization RestoredInitialSource
open QRH.Cycle092.TwistedRawSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

/-- The finite input row set itself is used; no new exceptional keep is installed. -/
theorem colored_finite_rows_le_fixed_ball (s : Source ι a b) (ha : 0<a)
    (ω₁ ω₂ : Id→ℂ) (η : Character) (K : ℝ) (hK : 0<K)
    (rows : Finset O) (hnz : ∀z∈rows,z≠0)
    (hrad : ∀z∈rows,‖eisEmbedding z‖^2 ≤ K) :
    (∑z∈rows,‖coloredWeightedRow s ha ω₁ ω₂ (naturalCharacter η z)‖^2) ≤
      coloredFullBallCost s ha ω₁ ω₂ η K := by
  let f : O→ℂ := fun z=>∑I∈sourceColumns s,
    sourceColumn s ha ω₁ ω₂ 1 I*rowWeight η fixedBadMask 1 z 0 I
  let g : O→ℝ := fun z=>‖f z‖^2*(ballProfile (‖eisEmbedding z‖^2/K)).re
  have hg : ∀z,0 ≤ g z := fun z=>mul_nonneg (sq_nonneg _) (ballProfile_nonneg _)
  have hsum := finite_hecke_energy_summable η fixedBadMask 1 0 (sourceColumns s)
    (sourceColumn s ha ω₁ ω₂ 1) ballProfile K hK
  have hre : HasSum g (finiteHeckeEnergy η fixedBadMask 1 0 (sourceColumns s)
      (sourceColumn s ha ω₁ ω₂ 1) ballProfile K).re := by
    have hh := Complex.hasSum_re hsum.hasSum
    simpa only [f,g,finiteHeckeEnergy,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using hh
  have he : (∑z∈rows,‖coloredWeightedRow s ha ω₁ ω₂ (naturalCharacter η z)‖^2) =
      (∑z∈rows,g z)/sourceVolume s := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z hz
    rw [colored_weighted_natural_norm s ha ω₁ ω₂ η z (hnz z hz)]
    dsimp only [g,f]
    rw [ballProfile_one _ (div_nonneg (sq_nonneg _) hK.le)
      ((div_le_one hK).mpr (hrad z hz)),Complex.one_re,mul_one]
  rw [he]
  unfold coloredFullBallCost
  apply div_le_div_of_nonneg_right _ (sourceVolume_pos s).le
  exact (((hre.summable.sum_le_tsum rows (fun z _=>hg z)).trans_eq hre.tsum_eq).trans
    (Complex.re_le_norm _))

theorem finite_signed_rows_le_fixed_ball (s : Source ι a b) (ha : 0<a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (hH : s.H=∅) (hd : s.d=(1,1)) (hR : s.R=1)
    (ω₁ ω₂ : Id→*₀ℂ) (η : Character) (K : ℝ) (hK : 0<K)
    (rows : Finset O) (hnz : ∀z∈rows,z≠0)
    (hrad : ∀z∈rows,‖eisEmbedding z‖^2 ≤ K) :
    (∑z∈rows,‖sourceSignedRow s ha (naturalCharacter η z) ω₁ ω₂‖^2) ≤
      coloredFullBallCost s ha ω₁ ω₂ η K := by
  have he : (∑z∈rows,‖sourceSignedRow s ha (naturalCharacter η z) ω₁ ω₂‖^2) =
      ∑z∈rows,‖coloredWeightedRow s ha ω₁ ω₂ (naturalCharacter η z)‖^2 := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [sourceSignedRow_eq_weighted s ha hb cover hH hd hR _ ω₁ ω₂
      (RestoredInitialSource.natural_character_off_supported η z (hnz z hz))]
  rw [he]
  exact colored_finite_rows_le_fixed_ball s ha ω₁ ω₂ η K hK rows hnz hrad

#print axioms colored_finite_rows_le_fixed_ball
#print axioms finite_signed_rows_le_fixed_ball
end
end QRH.Cycle092.TwistedRawBallRootProducer
