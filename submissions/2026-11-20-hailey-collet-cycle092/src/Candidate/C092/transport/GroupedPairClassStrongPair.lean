/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Two-character row adaptation of Sil's common-profile separation.
The original one-column Fourier/profile lemmas and majorants are reused unchanged. -/
import Candidate.C092.transport.GroupedPairClassSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.GroupedPair
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff FourierTransform
open MeasureTheory OAI OAI.SevenEighths
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentFiniteProfileExceptional
open QRH.Cycle092.OrdinaryColumn
open QRH.SilDensitySplit.CubeFree.Packet
open ProfileSeparation (dilate commonPair commonProfile scale pairCoeff cellCoeff pairMajorant pairWeight
  scale_pos commonPair_profile_zero commonPair_profile_one rowTwistedBound)
local notation "O" => ActualEisensteinCubic.O

open ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice (ballProfile ballProfile_nonneg ballProfile_le_one ballProfile_one)
open QRH.SilDensitySplit.CubeFree.Packet.Grouped (dilate_log_mem rescale_factor_le
  ball_lt_of_ne_zero mem_rowNormBall_of_norm_sq_le ball_one_of_le)

/-- Weighted H16 frame transfer on the original sublattices, sourced directly
from the same finite StrongPair rows and original common mark subproduct. -/
theorem class_bound_strongPair {Λ : Type*} {Slot : Type} [Fintype Slot] (Tslots : Finset Slot) (η₁ η₂ : Character) (marks : Slot→O→ℂ) (t₁ t₂ : ℝ) (keep : O → Prop)
    (hkeep : ∀ y, keep y → y ≠ 0)
    (hfree : ∀z,keep z→∃u:HeckeInverseAmplification.FreeRow,u.val=z)
    (p₀ p₁ : 𝓢(ℝ, ℂ)) (hs₀ : Function.support (p₀ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (hs₁ : Function.support (p₁ : ℝ → ℂ) ⊆ Set.Icc (1/4) (9/4))
    (Y₁ Y₂ Kc : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hKc : 0 < Kc)
    (labels : Finset Λ) (weight : Λ → ℝ) (hweight : ∀ x, 0 ≤ weight x) (V : Λ → O) (K : Λ → ℝ)
    (hK : ∀ x ∈ labels, 0 < ((Ideal.span {V x}).absNorm : ℝ) * K x)
    (hscale : ∀ x ∈ labels, 2 * (((Ideal.span {V x}).absNorm : ℝ) * K x) ≤ Kc)
    (X₁ X₂ : Λ → ℝ)
    (hX : ∀ x ∈ labels, 0 < X₁ x ∧ Y₁ / 2 ≤ X₁ x ∧ X₁ x ≤ Y₁ ∧
      0 < X₂ x ∧ Y₂ / 2 ≤ X₂ x ∧ X₂ x ≤ Y₂)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ y : O, y ≠ 0 → ‖eisEmbedding y‖ ^ 2 ≤ Kc →
      ∑ x ∈ labels.filter (fun x => V x ∣ y), weight x ≤ D)
    (C T : ℝ) (J : ℕ) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hsource : ∀ (e:Fin 2×Fin 2) (τ:ℝ×ℝ) (s:Finset HeckeInverseAmplification.FreeRow),
      (∀u∈s,keep u.val ∧ ‖eisEmbedding u.val‖^2 ≤ Kc) →
      StrongPair.finiteEnergyOn Tslots s η₁ η₂ ((commonPair e τ).profile 0)
        ((commonPair e τ).profile 1) t₁ t₂ (scale e.1*Y₁) (scale e.2*Y₂)
        (fun i u=>marks i u.val) ≤ C*pairWeight J τ*T) :
    ∑ x ∈ labels, weight x * pairEnergy η₁ η₂ (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator 1) 1 1 (fun z=>∏i∈Tslots,marks i z) t₁ t₂ p₀ p₁ (X₁ x) (X₂ x)
        (fun y => V x ∣ y ∧ keep y) ballProfile (((Ideal.span {V x}).absNorm : ℝ) * K x) ≤
      (4 * D) * C * (∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ, 1 * pairMajorant p₀ p₁ hs₀ hs₁ e τ) *
        (∑ e : Fin 2 × Fin 2, ∫ τ : ℝ × ℝ,
          1 * pairMajorant p₀ p₁ hs₀ hs₁ e τ * pairWeight J τ) * T := by
  exact class_bound η₁ η₂ (CenteredMomentSecondHeightFamily.fixedBadMask*
    ConcretePrimeRowBridge.idealGenerator 1) 1 1 (fun z=>∏i∈Tslots,marks i z) t₁ t₂ keep hkeep
    p₀ p₁ hs₀ hs₁ Y₁ Y₂ Kc hY₁ hY₂ hKc labels weight hweight V K hK hscale X₁ X₂ hX
    D hD0 hD C T J hC hT
    (finite_clean_source Tslots η₁ η₂ marks keep hfree t₁ t₂ Y₁ Y₂ Kc C T hY₁ hY₂ J hsource)

#print axioms class_bound_strongPair
end
end QRH.Cycle092.GroupedPair
