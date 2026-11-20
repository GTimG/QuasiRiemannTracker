/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The clean positive energy controls any subset of sixth-free cores in its ball,
with the original prime weights and the actual exceptional-row predicate. -/
import Candidate.C092.transport.CofactorKeep
import Candidate.C092.transport.MeasuredBall

namespace QRH.Cycle092.CofactorOrdinary
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ConcretePrimeRowBridge ActualEisensteinCubic
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ConcreteTraceCRT
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
open CenteredMomentPositiveSummability CenteredMomentDetectorPlainFiberSource
open Qrh.JointDetector WholeWordAmplification QRH.Cycle092.OrdinaryColumn
local notation "O" => ActualEisensteinCubic.O

theorem finite_clean_energy {ι : Type} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A : O) (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (t X₁ X₂ b₁ b₂ Y : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i) (hY : 0 < Y)
    (s : Finset FreeRow) (keep : O → Prop) (hk : ∀ u ∈ s, keep u.val)
    (hy : ∀ u ∈ s, rowNorm u ≤ Y) :
    (∑ u ∈ s, (∏ i, ‖normalizedSlot η m A u.val (S i) (β i) t (P i)‖^2) *
      ‖original η m A u.val W₁ t X₁ * original η m A u.val W₂ t X₂‖^2) ≤
      energy η m A t W₁ W₂ S β P X₁ X₂ keep radialMajorant Y := by
  let F := fun z => positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂
  let G := fun z : O => if keep z then ‖F z‖^2 * (radialMajorant (‖eisEmbedding z‖^2/Y)).re else 0
  obtain ⟨B,hB⟩ := product_bounded η m A t ((Real.sqrt (X₁*X₂*∏ i,P i):ℂ)⁻¹)
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  have hsum : Summable G := bounded_radial_summable F B hB keep radialMajorant Y hY
  have hnon (z : O) : 0 ≤ G z := by
    dsimp only [G]; split_ifs
    · exact mul_nonneg (sq_nonneg _) (radialMajorant_nonneg _)
    · exact le_rfl
  have hrow (u : FreeRow) (hu : u ∈ s) : G u.val = ‖F u.val‖^2 := by
    dsimp only [G]
    rw [if_pos (hk u hu),radialMajorant_one _ ⟨div_nonneg (sq_nonneg _) hY.le,(div_le_one hY).mpr ?_⟩,Complex.one_re,mul_one]
    rw [eisEmbedding_norm_sq_eq_absNorm_span]; exact hy u hu
  calc
    _ = ∑ u ∈ s, G u.val := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hrow u hu]
      dsimp only [F]
      rw [RefinedSupplier.positiveSlotRow_squared_factors η m A u.val W₁ W₂ S β P t X₁ X₂ hX₁ hX₂ hP]
      simp only [original,norm_mul,mul_pow]
      ring
    _ = ∑ z ∈ s.image Subtype.val, G z := (Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)).symm
    _ ≤ ∑' z : O, G z := hsum.sum_le_tsum _ (fun z _ => hnon z)
    _ = _ := rfl

#print axioms finite_clean_energy
end
end QRH.Cycle092.CofactorOrdinary
