/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Ordinary-factor orientation preserves the exact squarefree/hole and marked rows. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalInitialProjectedRows
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentHeckeExpansion
open QRH.Record1252270103Restoration
local notation "O"=>HeckeFamily.O

lemma ordinarySmallHole_swap (I J : Ideal O) : ordinarySmallHole I J↔ordinarySmallHole J I := by
  simp only [ordinarySmallHole,and_comm]

lemma squarefreePlainSum_swap (ψ : Ideal O →*₀ ℂ) (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) :
    squarefreePlainSum ψ W₂ W₁ b X₂ X₁=squarefreePlainSum ψ W₁ W₂ b X₁ X₂ := by
  unfold squarefreePlainSum plainPairPool
  simp only [Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [ordinarySmallHole_swap J I,mul_comm J I]
  split_ifs <;> ring

variable {ι : Type*} [Fintype ι]

theorem markedPositiveRow_swap (η : Character) (m A z : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) :
    markedPositiveRow η m A z W₂ W₁ b S β P t X₂ X₁=
      markedPositiveRow η m A z W₁ W₂ b S β P t X₁ X₂ := by
  unfold markedPositiveRow
  rw [squarefreePlainSum_swap,mul_comm X₂ X₁]

theorem squarefreeEnergy_swap (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    squarefreeEnergy η m A t W₂ W₁ b S β P X₂ X₁ keep Φ K=
      squarefreeEnergy η m A t W₁ W₂ b S β P X₁ X₂ keep Φ K := by
  unfold squarefreeEnergy squarefreePositiveSlotRow
  simp_rw [squarefreePlainSum_swap,mul_comm X₂ X₁]

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.markedPositiveRow_swap
#print axioms QRH.Record1252270103Low.squarefreeEnergy_swap
