/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Literal signed restored rows under the original finite keep. -/
import Candidate.C092.transport.TwistedRawBallRootCentered
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBallRootProducer
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve QuadraticInitialBound
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentLattice
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState
open QRH.SilDensitySplit.CubeFree.FP
open MixedPrincipalAllocations MixedPrincipalPair MixedPrincipalWindow
open MixedInnerExceptionalBlock MixedLiveNormalization RestoredInitialSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def sourceSignedRow (s : Source ι a b) (ha : 0<a) (χ : Character) (ω₁ ω₂ : Id→*₀ℂ) : ℂ :=
  let β := fun i I=>s.ν i I*s.Wslot i (I.absNorm/s.P i)
  let V₁ := normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁
  let V₂ := normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂
  restoredRow χ ω₁ ω₂ s.S s.pool β s.P V₁ V₂ b s.X₁ s.X₂-
    restoredRow χ ω₁ ω₂ s.S s.pool β s.P V₁ V₂ b s.Y₁ s.Y₂

theorem sourceSignedRow_eq_weighted (s : Source ι a b) (ha : 0<a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (hH : s.H=∅) (hd : s.d=(1,1)) (hR : s.R=1)
    (χ : Character) (ω₁ ω₂ : Id→*₀ℂ) (hoff : ∀I,¬Supported I→idealCoeff χ I=0) :
    sourceSignedRow s ha χ ω₁ ω₂ = coloredWeightedRow s ha ω₁ ω₂ χ :=
  (actual_source_signed_unpunctured s ha hb cover hH hd hR χ ω₁ ω₂ hoff).symm

/-- No row filter is changed by the canonical signed-row dictionary.
    Its common anchor can differ from the original keep's character. -/
theorem finite_signed_kept_le_fixed_ball (s : Source ι a b) (ha : 0<a) (hb : 0 ≤ b)
    (cover : OriginalEnclosure s) (hH : s.H=∅) (hd : s.d=(1,1)) (hR : s.R=1)
    (ω₁ ω₂ : Id→*₀ℂ) (η ηkeep η₀ : Character) (Q : Id) (Φ : 𝓢(ℝ,ℂ)) (Z bΦ : ℝ)
    (hZ : 0<Z) (hbΦ : 0<bΦ) (hs : Function.support (Φ:ℝ→ℂ) ⊆ Iic bΦ)
    (rows : Finset O) :
    (∑z∈rows,initialWeight ηkeep η₀ Q Φ Z z*
      ‖sourceSignedRow s ha (naturalCharacter η z) ω₁ ω₂‖^2) ≤
      diagonalControl Φ*coloredFullBallCost s ha ω₁ ω₂ η (bΦ*Z) := by
  have he : (∑z∈rows,initialWeight ηkeep η₀ Q Φ Z z*
      ‖sourceSignedRow s ha (naturalCharacter η z) ω₁ ω₂‖^2) =
    ∑z∈rows,initialWeight ηkeep η₀ Q Φ Z z*
      ‖coloredWeightedRow s ha ω₁ ω₂ (naturalCharacter η z)‖^2 := by
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hk : initialKeep ηkeep (internalQ Q η₀) z
    · rw [sourceSignedRow_eq_weighted s ha hb cover hH hd hR _ ω₁ ω₂
        (RestoredInitialSource.natural_character_off_supported η z hk.1)]
    · simp only [initialWeight,hk,ite_false,zero_mul]
  rw [he]
  exact colored_finite_kept_le_fixed_ball s ha ω₁ ω₂ η ηkeep η₀ Q Φ Z bΦ hZ hbΦ hs rows

#print axioms sourceSignedRow_eq_weighted
#print axioms finite_signed_kept_le_fixed_ball
end
end QRH.Cycle092.TwistedRawBallRootProducer
