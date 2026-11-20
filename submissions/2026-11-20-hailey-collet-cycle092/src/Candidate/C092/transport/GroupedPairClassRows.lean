/- Copyright (c) 2026 Sil and Hailey Collet. Apache-2.0.
Two-character row adaptation of Sil's common-profile separation.
The original one-column Fourier/profile lemmas and majorants are reused unchanged. -/
import Candidate.C092.transport.GroupedPairProfileSeparation

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

/-- Exact original lattice energy with two independent ordinary factors and
one frozen common mark product. -/
def pairEnergy (η₁ η₂ : Character) (m A₁ A₂ : O) (mark : O→ℂ) (t₁ t₂ : ℝ)
    (W₁ W₂ : ℝ→ℂ) (X₁ X₂ : ℝ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑' z:O,if keep z then ‖row η₁ η₂ m A₁ A₂ z W₁ W₂ t₁ t₂ X₁ X₂ mark‖^2*
    (Φ (‖eisEmbedding z‖^2/K)).re else 0

theorem row_rescale (η₁ η₂ : Character) (m A₁ A₂ z : O) (mark : O→ℂ)
    (W₁ W₂ : 𝓢(ℝ,ℂ)) (t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) :
    row η₁ η₂ m A₁ A₂ z W₁ W₂ t₁ t₂ X₁ X₂ mark=
      (Real.sqrt (Y₁*Y₂/(X₁*X₂)):ℂ)*
      row η₁ η₂ m A₁ A₂ z (dilate W₁ (Real.log (Y₁/X₁)))
        (dilate W₂ (Real.log (Y₂/X₂))) t₁ t₂ Y₁ Y₂ mark := by
  unfold row
  rw [←Grouped.rowTwistedSum_rescale η₁ m A₁ z W₁ t₁ X₁ Y₁ hX₁ hY₁,
    ←Grouped.rowTwistedSum_rescale η₂ m A₂ z W₂ t₂ X₂ Y₂ hX₂ hY₂]
  have hρ : 0<Real.sqrt (Y₁*Y₂/(X₁*X₂)):=Real.sqrt_pos.mpr
    (div_pos (mul_pos hY₁ hY₂) (mul_pos hX₁ hX₂))
  have hsplit : Real.sqrt (Y₁*Y₂)=Real.sqrt (Y₁*Y₂/(X₁*X₂))*Real.sqrt (X₁*X₂):=by
    rw [←Real.sqrt_mul (div_nonneg (mul_pos hY₁ hY₂).le (mul_pos hX₁ hX₂).le)]
    congr 1
    field_simp
  rw [hsplit,Complex.ofReal_mul,mul_inv]
  have hne : (Real.sqrt (Y₁*Y₂/(X₁*X₂)):ℂ)≠0:=by exact_mod_cast hρ.ne'
  field_simp

/-- The common-row source is literally StrongPair on the same finite clean
rows and the same original normalized mark subproduct. -/
theorem common_rows_eq_strongPair {Slot : Type} [Fintype Slot]
    (T : Finset Slot) (s : Finset HeckeInverseAmplification.FreeRow)
    (η₁ η₂ : Character) (marks : Slot→O→ℂ) (t₁ t₂ Y₁ Y₂ : ℝ)
    (hY₁ : 0<Y₁) (hY₂ : 0<Y₂) (e : Fin 2×Fin 2) (τ : ℝ×ℝ) :
    (∑ z∈s,‖commonRow η₁ η₂ (CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator 1) 1 1 (fun z=>∏i∈T,marks i z)
        t₁ t₂ Y₁ Y₂ e τ z.val‖^2)=
      QRH.Cycle092.StrongPair.finiteEnergyOn T s η₁ η₂ ((commonPair e τ).profile 0)
        ((commonPair e τ).profile 1) t₁ t₂ (scale e.1*Y₁) (scale e.2*Y₂)
        (fun i z=>marks i z.val) := by
  unfold StrongPair.finiteEnergyOn
  apply Finset.sum_congr rfl
  intro z hz
  rw [commonRow,row_eq_original η₁ η₂ _ 1 1 z.val _ _ t₁ t₂ _ _ _
    (mul_pos (scale_pos e.1) hY₁) (mul_pos (scale_pos e.2) hY₂)]
  simp only [norm_mul,norm_prod,mul_pow,Finset.prod_pow]

#print axioms row_rescale
#print axioms common_rows_eq_strongPair
end
end QRH.Cycle092.GroupedPair
