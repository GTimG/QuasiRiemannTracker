/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
The restricted source differs from the literal initial energy only by the
ordinary-pair squarefree projector and one fixed finite small-prime hole. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract
import Submissions.hailey_collet_1252270103.Record1252270103KernelMass.All
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainSource

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot CenteredMomentSourceMass
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open Record1252270103KernelMass
local notation "O" => HeckeFamily.O

/-- This fixed finite hole acts only on the two ordinary ideals. -/
def ordinarySmallHole (I J : Ideal O) : Prop :=
  ∀ P ∈ smallPrimes, valuation I P.val=0 ∧ valuation J P.val=0

def plainPairPool (b X₁ X₂ : ℝ) : Finset IdealPair := idealBall (b*X₁) ×ˢ idealBall (b*X₂)

def squarefreePlainSum (ψ : Ideal O →*₀ ℂ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) : ℂ :=
  ∑ n ∈ plainPairPool b X₁ X₂, if ordinarySmallHole n.1 n.2 then
    (squarefreeIndicator (n.1*n.2) : ℂ)*ψ (n.1*n.2)*
      W₁ ((Ideal.absNorm n.1:ℝ)/X₁)*W₂ ((Ideal.absNorm n.2:ℝ)/X₂) else 0

def squarefreePositiveSlotRow {ι : Type*} [Fintype ι]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) : ℂ :=
  (Real.sqrt (X₁*X₂*∏ i,P i):ℂ)⁻¹ *
    (squarefreePlainSum (rowWeight η m A z t) W₁ W₂ b X₁ X₂ *
      ∏ i,rowSlot η m A z (S i) (β i) t)

def squarefreeEnergy {ι : Type*} [Fintype ι]
    (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (X₁ X₂ : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, if keep z then ‖squarefreePositiveSlotRow η m A z W₁ W₂ b S β P t X₁ X₂‖^2*
    (Φ (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O⧸rayModulus) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (H : Subgroup (O⧸rayModulus)ˣ) (hH : RayOrthogonality.globalUnits rayModulus ≤ H)

def SquarefreeInitialAffineAt (face : SourceFace) (W : ℝ→ℂ)
    (bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ)
    (η η₀ : Character) (Q R₀ : Ideal O) (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  ∀ T : Finset α, ∀ (θ : T→RayQuotient.Characters rayModulus H)
      (w σ v : T→ℝ) (t height : ℝ),
    (∀ i,0≤w i) → (∀ i,w i≤mesh) → (∀ i,σlo≤σ i) → (∀ i,σ i≤σhi) →
    0≤height → (∀ i,|v i|≤height) →
  ∀ M : ℝ, Mmin≤M → M≤Mmax →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀ x,0≤(Φ x).re) →
  ∀ p : Profiles a b, ∀ X₁ X₂ : ℝ, 0<X₁ → 0<X₂ →
    face.Admissible (length Z X₁) (length Z X₂) (∑ i,w i) M →
    squarefreeEnergy η (fixedBadMask*idealGenerator R₀) 1 t (p.profile 0) (p.profile 1) b
      (fun i=>primePool rayModulus H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter rayModulus H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M) ≤
      C*QuadraticInitialBound.diagonalControl Φ*(p.control controls)^2*
        (1+|t|+height)^degree*Z^(M+ε)

def SquarefreeUnitFaceSource (face : SourceFace) (mesh ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α],
  ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H),
  ∀ (W : ℝ→ℂ), ContDiff ℝ ∞ W → Function.support W⊆Set.Icc (1:ℝ) 2 →
  ∀ bΦ : ℝ, 2≤bΦ → ∀ (η η₀ : Character) (Q : Ideal O),
    Q≤rayM → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    internalQ Q η₀≤Ideal.span {(72:O)} →
  ∀ R₀ : Ideal O, R₀≠0 →
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0<C ∧
      ∀ᶠ Z : ℝ in Filter.atTop,
        SquarefreeInitialAffineAt (α:=α) rayM H hH face W 2 (1/4) (9/4) bΦ mesh
          (33/50) (33/50) 1 1 ε Z η η₀ Q R₀ degree controls C

def UniformSquarefreeUnitFaceSource (B lam cap : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ mesh : ℝ, 0<mesh ∧
    SquarefreeUnitFaceSource (QRH.Record1252270103Source.globalFace B lam cap) mesh ε

end
end QRH.Record1252270103Restoration
