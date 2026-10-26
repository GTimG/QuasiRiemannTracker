/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.EndpointStageParameters
import Candidate.Uneven.MainInitialContract
import Candidate.Cycle63.Moment.InitialAffineContract

/-! Genuine two-profile initial affine source contract for the new planes.
This module defines the premise and asserts no analytic estimate. -/

namespace OAI.SevenEighths.UnevenEndpoint.Physical
variable [config : Configuration]
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge
open CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (H : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ H)

/-- The required moment applies to the fixed initial parent, uniformly over
a compact positive width interval and all live canonical slot parameters. -/
def InitialAffineAt (P : SourcePlane) (W : ℝ → ℂ) (bslot a b bΦ mesh lo hi Mmin Mmax ε Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ T : Finset α, ∀ (θ : T → RayQuotient.Characters rayModulus H)
      (w σ v : T → ℝ) (t height : ℝ),
    (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
    (∀ i, lo ≤ σ i) → (∀ i, σ i ≤ hi) →
    0 ≤ height → (∀ i, |v i| ≤ height) →
  ∀ M : ℝ, Mmin ≤ M → M ≤ Mmax →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
    (∀ x, 0 ≤ (Φ x).re) →
  ∀ p : Profiles a b, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    plainLower*M ≤ length Z X₁ → length Z X₁ ≤ plainUpper*M →
    plainLower*M ≤ length Z X₂ → length Z X₂ ≤ plainUpper*M →
    widthLower*M ≤ ∑ i, w i → (∑ i, w i) ≤ widthUpper*M →
    length Z X₁ + length Z X₂ + P.lambda*(∑ i, w i) ≤
      P.B*M →
    energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayModulus H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayModulus H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M) ≤
      C*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
        (1+|t|+height)^degree*Z^(M+ε)

end
end OAI.SevenEighths.UnevenEndpoint.Physical

