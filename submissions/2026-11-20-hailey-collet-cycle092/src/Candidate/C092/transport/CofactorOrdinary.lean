/- Copyright (c) 2026 Hailey Collet. Apache-2.0. Uses the original OAI
masked ideal sum, with the normalization of the actual source slot. -/
import Candidate.C092.transport.OrdinaryColumn
namespace QRH.Cycle092.CofactorOrdinary
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification CenteredMomentHeckeHeight CenteredMomentHeckeExpansion
open CenteredMomentSourceMass CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentMask IdealMobiusDivisorSum UniqueFactorizationMonoid
open Qrh.JointDetector WholeWordAmplification QRH.Cycle092.OrdinaryColumn
local notation "O" => ActualEisensteinCubic.O

def factor (η : Character) (m A z : O) (t : ℝ) (D : Ideal O) : ℂ :=
  ((moebius D : ℂ) * rowWeight η m A z t D) / (Real.sqrt (D.absNorm : ℝ) : ℂ)

theorem factor_norm (η : Character) (m A z : O) (t : ℝ) (D : Ideal O) :
    ‖factor η m A z t D‖ ≤ (Real.sqrt (D.absNorm : ℝ))⁻¹ := by
  rw [factor,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),←one_div]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact (mul_le_mul (QuadraticInitialBound.norm_ideal_moebius_le_one D)
    (CenteredMomentAbsoluteEnergy.rowWeight_norm_le_one_all η m A z t D)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Möbius removal for the original normalized ordinary row. Each divisor
shortens only this scale; the character and the full height are unchanged. -/
theorem exact_sum (η : Character) (m A : O) (hm₁ : goodLambda ∣ m) (hm₂ : (2:O) ∣ m)
    (root : NonzeroIdeal) (u : FreeRow) (W : ℝ → ℂ) (t b P : ℝ)
    (hs : Function.support W ⊆ Set.Iic b) (hP : 0 < P) :
    original η m A (rowMap (u,root)) W t P = ∑ D ∈ idealDivisors root.val,
      factor η m A u.val t D * original η m A u.val W t (P/(D.absNorm:ℝ)) := by
  let χ := rowWeight η m A u.val t
  let f (I : Ideal O) := (if IsCoprime I root.val then (1:ℂ) else 0) * (χ I * W ((I.absNorm:ℝ)/P))
  have ht : (∑' I, f I) = ∑ I ∈ idealBall (b*P), f I := by
    apply tsum_eq_sum; intro I hI
    by_cases h : I=0
    · subst I; simp only [f,map_zero,zero_mul,mul_zero]
    · have hw : W ((I.absNorm:ℝ)/P) = 0 := by
        by_contra hn; exact hI ((mem_idealBall _ _).mpr ⟨h,(div_le_iff₀ hP).mp (hs hn)⟩)
      simp [f,hw]
  have he : original η m A (rowMap (u,root)) W t P = (Real.sqrt P:ℂ)⁻¹ * ∑' I, f I := by
    rw [as_slot η m A _ W t b P hs hP,rowMap,NaturalCount.normalizedSlot_sixth_root η m A u.val hm₁ hm₂,
      normalizedSlot,rowSlot_eq_weight,ht]
    congr 1; apply Finset.sum_congr rfl; intro I _; dsimp only [f,χ]; ring
  have heq := masked_plain_ideal_sum root.val root.property χ.toMonoidHom W b P hP hs
  change (∑' I, f I) = ∑ D ∈ idealDivisors root.val, (moebius D : ℂ) * χ D * ∑' J : Ideal O, χ J * W ((J.absNorm:ℝ)/(P/(D.absNorm:ℝ))) at heq
  rw [he,heq,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro D hD
  have hD0 := ne_zero_of_dvd_ne_zero root.property ((mem_idealDivisors root.property).mp hD)
  have hn : 0 < (D.absNorm:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hD0)
  have hsn : (Real.sqrt (D.absNorm:ℝ):ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hn).ne'
  unfold factor original; rw [rowTwistedSum_eq_weight,Real.sqrt_div hP.le,Complex.ofReal_div]
  change _ = (↑(moebius D) * χ D / _) * (_ * ∑' J : Ideal O, χ J * W ((J.absNorm:ℝ)/(P/(D.absNorm:ℝ))))
  generalize (∑' J : Ideal O, χ J * W ((J.absNorm:ℝ)/(P/(D.absNorm:ℝ)))) = a
  simp only [inv_div]; field_simp <;> ring

#print axioms exact_sum
#print axioms factor_norm
end
end QRH.Cycle092.CofactorOrdinary
