/- Copyright (c) 2026 Hailey Collet. Apache-2.0. Finite expansion of the
original OAI sums, with Joseph Bebel's normalized sixth-root identity. -/
import Candidate.C092.transport.PairedColumn

namespace QRH.Cycle092.OrdinaryColumn
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification CenteredMomentHeckeHeight CenteredMomentHeckeExpansion
open CenteredMomentSourceMass CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open Qrh.JointDetector WholeWordAmplification
local notation "O" => ActualEisensteinCubic.O

/-- Exactly the finite coefficient on the free core arising from a natural
sixth root, including its original coprimality deletion and height. -/
def plain (η : Character) (m A : O) (root : NonzeroIdeal) (W : ℝ → ℂ) (t P : ℝ) :=
  normalizedSlotCoefficient η m A (fun I => (if IsCoprime I root.val then (1:ℂ) else 0)*W ((I.absNorm:ℝ)/P)) t P

def original (η : Character) (m A z : O) (W : ℝ → ℂ) (t P : ℝ) : ℂ :=
  (Real.sqrt P : ℂ)⁻¹ * rowTwistedSum η m A z W t P

theorem as_slot (η : Character) (m A z : O) (W : ℝ → ℂ) (t b P : ℝ)
    (hs : Function.support W ⊆ Set.Iic b) (hP : 0 < P) :
    original η m A z W t P = normalizedSlot η m A z (idealBall (b*P)) (fun I => W ((I.absNorm:ℝ)/P)) t P := by
  rw [original,normalizedSlot,rowTwistedSum_eq_weight,rowSlot_eq_weight,tsum_eq_sum (s:=idealBall (b*P)) ?_]
  · simp only [mul_comm (rowWeight _ _ _ _ _ _)];
  · intro I hI; by_cases h0 : I = 0
    · subst I; simp only [map_zero,zero_mul]
    · have hw : W ((I.absNorm:ℝ)/P) = 0 := by
        by_contra h; exact hI ((mem_idealBall _ _).mpr ⟨h0,(div_le_iff₀ hP).mp (hs h)⟩)
      rw [hw,mul_zero]

theorem on_root (η : Character) (m A : O) (hm₁ : goodLambda ∣ m) (hm₂ : (2:O) ∣ m)
    (root : NonzeroIdeal) (u : FreeRow) (W : ℝ → ℂ) (t b P : ℝ)
    (hs : Function.support W ⊆ Set.Iic b) (hP : 0 < P) :
    original η m A (rowMap (u,root)) W t P = ∑ I ∈ idealBall (b*P), plain η m A root W t P I * idealRowHom u.val I := by
  rw [as_slot η m A _ W t b P hs hP,rowMap,NaturalCount.normalizedSlot_sixth_root η m A u.val hm₁ hm₂,normalizedSlot_polynomial]; rfl

/-- The estimate includes subunit lengths; such an ideal ball can be empty.
The constant does not depend on the root, character, cofactor, height or P. -/
theorem square_mass (η : Character) (m A : O) (root : NonzeroIdeal) (W : ℝ → ℂ) (t b P B : ℝ)
    (hb : 0 ≤ b) (hP : 0 < P) (hW : ∀ I ∈ idealBall (b*P), ‖W ((I.absNorm:ℝ)/P)‖ ≤ B) :
    (∑ I ∈ idealBall (b*P), ‖plain η m A root W t P I‖^2) ≤ 128*b*B^2 := by
  calc
    _ ≤ ∑ _I ∈ idealBall (b*P), B^2/P := by
      apply Finset.sum_le_sum; intro I hi; apply normalizedSlotCoefficient_square _ _ _ _ _ _ _ _ ((mem_idealBall _ _).mp hi).1 hP
      rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (NaturalCount.sixth_root_mask_norm_le_one root I)).trans (hW I hi)
    _ = ((idealBall (b*P)).card:ℝ)*(B^2/P) := by simp
    _ ≤ (128*(b*P))*(B^2/P) := mul_le_mul_of_nonneg_right (idealBall_card _ (mul_nonneg hb hP.le)) (div_nonneg (sq_nonneg B) hP.le)
    _ = _ := by field_simp

#print axioms on_root
#print axioms square_mass
end
end QRH.Cycle092.OrdinaryColumn
