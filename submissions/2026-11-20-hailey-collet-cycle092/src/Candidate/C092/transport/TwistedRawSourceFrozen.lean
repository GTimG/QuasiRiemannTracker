/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Live colors at the full-primary frozen-row endpoint. -/
import Candidate.C092.transport.TwistedRawSourceCanonical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawSource
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceRectangle
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentFirstSectors
open QRH.SilDensitySplit.CubeFree.FP
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance (priority := 2000) sumFrozenDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _
local instance (priority := 2000) subtypeFrozenDecEq {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

def frozenLiveSum (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal)
    (pool : ι → Finset Id) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (B : Tuple ι) (hB : ∀ j, B j ≠ 0) (F R : Id)
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑ v ∈ liveBox (MixedLiteralAllocation.sourcePools pool d hd b X₁ X₂ Y₁ Y₂) B hB,
    MixedCommonCoefficient.tupleWeight (MixedCommonRestriction.punctureProduct S H) v *
      ordinaryColor ω₁ ω₂ v *
      liveProfile B F R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 v *
      idealCoeff χ (finiteTupleProduct v)

def frozenRow (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal)
    (pool : ι → Finset Id) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (B : Tuple ι) (hB : ∀ j, B j ≠ 0) (F R : Id)
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  MixedLiveNormalization.normalization (X₁*X₂) P *
    (frozenCoefficient B (finiteTupleProduct B) R ν Wslot P *
      frozenLiveSum ω₁ ω₂ χ S H pool d hd B hB F R ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂)

theorem frozen_live_eq_canonical (ω₁ ω₂ : Id →*₀ ℂ) (χ : Character)
    (S H : Finset QRH.Record1252270103KernelMass.PrimeIdeal)
    (pool : ι → Finset Id) (d : Id × Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (B : Tuple ι) (hB : ∀ j, B j ≠ 0) (F R : Id)
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ Y₁ Y₂ : ℝ) :
    frozenLiveSum ω₁ ω₂ χ S H pool d hd B hB F R ν Wslot P W₁ W₂ b X₁ X₂ Y₁ Y₂ =
      canonicalSource ω₁ ω₂ χ S H (R*F) (fun i : liveIndices B => pool i.val)
        (fun i => ν i.val) (fun i => Wslot i.val) (fun i => P i.val)
        W₁ W₂ b X₁ X₂ Y₁ Y₂ (d.1*B (Sum.inr 0),d.2*B (Sum.inr 1)) := by
  unfold frozenLiveSum canonicalSource MixedLiteralAllocation.sourcePools
  rw [MixedLiveRows.source_live_box pool d hd _ _ B hB,
    MixedCompletedRows.residual_plain_pool, MixedCompletedRows.residual_plain_pool]
  rfl

#print axioms frozen_live_eq_canonical
end
end QRH.Cycle092.TwistedRawSource
