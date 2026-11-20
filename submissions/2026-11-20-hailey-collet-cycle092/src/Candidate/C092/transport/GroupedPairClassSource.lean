/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Two-character row adaptation of Sil's common-profile separation.
The original one-column Fourier/profile lemmas and majorants are reused unchanged. -/
import Candidate.C092.transport.GroupedPairClassBound
import Candidate.C092.transport.GroupedPairProfileControls

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

/-- Every finite retained original-lattice sum is a finite sum of the actual
clean rows. The injective relabelling adds no multiplicity. -/
theorem finite_clean_source {Slot : Type} [Fintype Slot]
    (T : Finset Slot) (η₁ η₂ : Character) (marks : Slot→O→ℂ)
    (keep : O→Prop)
    (hfree : ∀ z,keep z→∃u:HeckeInverseAmplification.FreeRow,u.val=z)
    (t₁ t₂ Y₁ Y₂ Kc C R : ℝ) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (J : ℕ)
    (hsource : ∀ (e:Fin 2×Fin 2) (τ:ℝ×ℝ) (s:Finset HeckeInverseAmplification.FreeRow),
      (∀u∈s,keep u.val ∧ ‖eisEmbedding u.val‖^2 ≤ Kc) →
      StrongPair.finiteEnergyOn T s η₁ η₂ ((commonPair e τ).profile 0)
        ((commonPair e τ).profile 1) t₁ t₂ (scale e.1*Y₁) (scale e.2*Y₂)
        (fun i u=>marks i u.val) ≤ C*pairWeight J τ*R) :
    ∀ (e:Fin 2×Fin 2) (τ:ℝ×ℝ) (s:Finset O),
      (∀z∈s,keep z ∧ ‖eisEmbedding z‖^2 ≤ Kc) →
      (∑z∈s,‖commonRow η₁ η₂ (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator 1) 1 1 (fun z=>∏i∈T,marks i z)
        t₁ t₂ Y₁ Y₂ e τ z‖^2) ≤ C*pairWeight J τ*R := by
  classical
  intro e τ s hs
  let f : {z // z∈s}→HeckeInverseAmplification.FreeRow :=
    fun z=>Classical.choose (hfree z.val (hs z.val z.property).1)
  have hf (z:{z // z∈s}) : (f z).val=z.val:=Classical.choose_spec
    (hfree z.val (hs z.val z.property).1)
  have hinj : Function.Injective f:=by
    intro a b hab
    apply Subtype.ext
    exact (hf a).symm.trans ((congrArg Subtype.val hab).trans (hf b))
  let rows:=s.attach.image f
  have hrows : ∀u∈rows,keep u.val ∧ ‖eisEmbedding u.val‖^2 ≤ Kc:=by
    intro u hu
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hu
    rw [hf]
    exact hs z.val z.property
  have heq : (∑z∈s,‖commonRow η₁ η₂ (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator 1) 1 1 (fun z=>∏i∈T,marks i z)
        t₁ t₂ Y₁ Y₂ e τ z‖^2)=
      ∑u∈rows,‖commonRow η₁ η₂ (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator 1) 1 1 (fun z=>∏i∈T,marks i z)
        t₁ t₂ Y₁ Y₂ e τ u.val‖^2:=by
    dsimp [rows]
    rw [Finset.sum_image (fun a _ b _ hab=>hinj hab)]
    simp only [hf]
    exact (Finset.sum_attach s (fun z=>‖commonRow η₁ η₂ (CenteredMomentSecondHeightFamily.fixedBadMask*
      ConcretePrimeRowBridge.idealGenerator 1) 1 1 (fun z=>∏i∈T,marks i z)
      t₁ t₂ Y₁ Y₂ e τ z‖^2)).symm
  rw [heq,common_rows_eq_strongPair T rows η₁ η₂ marks t₁ t₂ Y₁ Y₂ hY₁ hY₂ e τ]
  exact hsource e τ rows hrows

#print axioms finite_clean_source
end
end QRH.Cycle092.GroupedPair
