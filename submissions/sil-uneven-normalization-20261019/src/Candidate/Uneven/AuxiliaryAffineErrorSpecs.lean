/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.AuxiliaryAmplifiedRemainder
import Candidate.Uneven.AuxiliaryErrorMain
import Candidate.Uneven.AuxiliaryCellGeometry
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Uneven.AuxiliaryAffineErrorNormalized
import Candidate.Uneven.AuxiliaryAffineErrorPayment

set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.AuxiliaryErrorReconstruction
open OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open OAI.SevenEighths.AuxiliaryReconstruction
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondEnergySplit
open CenteredMomentAmplificationErrorEnergy CenteredMomentAllocatedRayDictionary
open CenteredMomentPrimeElements CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice
open CenteredMomentLogDyadic RayFourExpansion
open Filter CenteredMomentCommonProfile CenteredMomentEnergyState CenteredMomentEnergyBands
open Cycle63InitialSource CenteredMomentAmplificationRadicalFamily CenteredMomentChildRows
open CenteredMomentSecondHeightFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentFiniteProfileExceptional
local notation "O" => HeckeFamily.O
attribute [local instance] geometryErrorOrdinaryContractionDecidable

variable {α : Type}[Fintype α]

private theorem affine_error_complete_profile_zero (p : Profiles (1/4) (9/4))(i : Fin 2) :
    p.profile i 0=0 := by
  by_contra h
  have hh:=(p.support i h).1
  norm_num at hh

variable [DecidableEq α]
variable (rayM : Ideal O)[NeZero rayM]
local instance affineErrorCompleteFiniteQuotient : Finite (O⧸rayM):=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ)(hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Explicit conditional callback: the uniform exact normalized-family estimate.
Constants and profiles precede every actual moving source and original character family. -/
def GeometryAffineErrorNormalizedSpec
    (Sbad : Finset (Ideal O))(W : ℝ→ℂ)(hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(mesh εaffine : ℝ)(T : Finset α)
    (degree windowDegree : ℕ)(Qfix : Ideal O)
    (S : Finset (ℕ×ℕ))(D : ℕ)(Cn Z : ℝ) : Prop :=
  ∀(hZ : 1 < Z)(θ : T→RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0 < X₁)(hX₂ : 0 < X₂),
      (∀i,0 ≤ w i) → (∀i,w i ≤ mesh) →
      (81/200:ℝ) ≤ length Z X₁ → (81/200:ℝ) ≤ length Z X₂ →
      length Z X₁ ≤ (45/100:ℝ) → length Z X₂ ≤ (45/100:ℝ) →
      (1/50:ℝ) ≤ ∑i,w i → (∑i,w i) ≤ (7/250:ℝ) →
      length Z X₁+length Z X₂+Sil.Uneven.AuxiliarySource.lambda*(∑i,w i) ≤ Sil.Uneven.AuxiliarySource.B →
      ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),0 ≤ height → (∀i,|freq i| ≤ height) →
      let s:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let μ:=geometryLossUnit 1 εaffine
      let N:=Fintype.card α
      let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
      let amp:=Sil.Uneven.AuxiliarySource.amp (Sil.Uneven.AuxiliarySource.widthCellUpper (∑i,w i))
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      let control:=(p.control S)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
      let exponent:=(2*δ+3*(3*((N:ℝ)+2))*δ)+(4*δ+δ-(7/60000000:ℝ))
      ∀(υ : GeometryLowFirstIndex (α:=T) reflected s (1:Ideal O) (1:Ideal O)
        (Z^(1:ℝ)) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
        elementPool P→Fin 3→RayCharacter→Character),
      (∀q p i ψ,(υ q p i ψ).modulus.absNorm ≤ radicalBound (childCharacter
        (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key q.1.val) ψ)
        fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
      letI : DecidableEq T:=Classical.decEq T;
      GeometryErrorNormalizedFamilyReceipt degree windowDegree reflected s Ψ Z amp (μ/64) (μ/8)
        firstHeight hZ key P υ (affine_error_complete_profile_zero p 0) (affine_error_complete_profile_zero p 1)
        Qfix fixedBadMask (Cn*control*Z^exponent)

/-- The original retained error paid by its prime average exactly once. -/
def GeometryAffineErrorPaidSpec
    (Sbad : Finset (Ideal O))(W : ℝ→ℂ)(hW : Continuous W)
    (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (Ψ : 𝓢(ℝ,ℂ))(ηseed η₀ : Character)(mesh εaffine : ℝ)(T : Finset α)
    (S : Finset (ℕ×ℕ))(D : ℕ)(Ce Z : ℝ) : Prop :=
  ∀(hZ : 1 < Z)(θ : T→RayQuotient.Characters rayM H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0 < X₁)(hX₂ : 0 < X₂),
      (∀i,0 ≤ w i) → (∀i,w i ≤ mesh) →
      (81/200:ℝ) ≤ length Z X₁ → (81/200:ℝ) ≤ length Z X₂ →
      length Z X₁ ≤ (45/100:ℝ) → length Z X₂ ≤ (45/100:ℝ) →
      (1/50:ℝ) ≤ ∑i,w i → (∑i,w i) ≤ (7/250:ℝ) →
      length Z X₁+length Z X₂+Sil.Uneven.AuxiliarySource.lambda*(∑i,w i) ≤ Sil.Uneven.AuxiliarySource.B →
      ∀(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),0 ≤ height → (∀i,|freq i| ≤ height) →
      let s:=affineInput rayM H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) 1 t X₁ X₂ hX₁ hX₂
      let μ:=geometryLossUnit 1 εaffine
      let N:=Fintype.card α
      let δ:=geometryFinalDictionaryRate μ 31 3 4 3 130 (3*((N:ℝ)+2)) N
      let amp:=Sil.Uneven.AuxiliarySource.amp (Sil.Uneven.AuxiliarySource.widthCellUpper (∑i,w i))
      let P:=CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^amp)
      let control:=(p.control S)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
      ∀(υ : GeometryLowFirstIndex (α:=T) reflected s (1:Ideal O) (1:Ideal O)
        (Z^(1:ℝ)) Z (μ/64) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key→
        elementPool P→Fin 3→RayCharacter→Character),
      (∀q p i ψ,(υ q p i ψ).modulus.absNorm ≤ radicalBound (childCharacter
        (geometryColumnCharacter reflected s 1 1 (Z^(1:ℝ)) Z (μ/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)) key q.1.val) ψ)
        fixedBadMask p.val (errorMovingExponent (errorIndex i))) →
      letI : DecidableEq T:=Classical.decEq T;
      (56/(P.card:ℝ))*‖geometryAffineErrorRetainedSum s Ψ Z amp (μ/64) (μ/8) firstHeight
        hZ reflected key P υ‖ ≤ Ce*control*Z^(-(7/120000000:ℝ))

end
end OAI.SevenEighths.AuxiliaryErrorReconstruction
