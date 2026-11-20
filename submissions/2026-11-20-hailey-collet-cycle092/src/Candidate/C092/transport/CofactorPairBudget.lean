/- Copyright (c) 2026 Hailey Collet. Apache-2.0. The entire ordinary pair's
Möbius expansion costs an arbitrarily small fixed power under the cofactor cap. -/
import Candidate.C092.transport.CofactorPairEnergy
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

theorem pair_divisor_budget (ε L : ℝ) (hε : 0 < ε) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U → ∀ root : NonzeroIdeal,
      (root.val.absNorm : ℝ) ≤ U^L → ((idealDivisors root.val).card:ℝ)^4 ≤ C*U^ε := by
  obtain ⟨D,hD,h⟩ := polynomial_mask_divisor_bound (ε/4) L (by positivity) hL
  refine ⟨D^4,by positivity,?_⟩
  intro U hU root hb
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ((idealDivisors root.val).card:ℝ)) (h U hU root.val root.property hb) 4
  rw [mul_pow, ← Real.rpow_natCast (U^(ε/4)) 4, ← Real.rpow_mul (zero_le_one.trans hU)] at hh
  simpa only [Nat.cast_ofNat,div_mul_cancel₀ ε (by norm_num : (4:ℝ) ≠ 0)] using hh

/-- A uniform shortened-pair estimate on the actual retained rows lifts to
its masked cofactor fiber, paying at most epsilon in the exponent. -/
theorem pair_energy_subpower (ε L : ℝ) (hε : 0 < ε) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U → ∀ root : NonzeroIdeal, (root.val.absNorm:ℝ) ≤ U^L →
      ∀ (η₁ η₂ : Character) (m A₁ A₂ : O), goodLambda ∣ m → (2:O) ∣ m →
      ∀ (s : Finset FreeRow) (w : FreeRow → ℝ), (∀ u ∈ s, 0 ≤ w u) →
      ∀ (W₁ W₂ : ℝ → ℂ) (t₁ t₂ b₁ b₂ P Q K : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ → 0 < P → 0 < Q → 0 ≤ K →
      (∀ D ∈ idealDivisors root.val, ∀ E ∈ idealDivisors root.val,
       (∑ u ∈ s, w u * ‖original η₁ m A₁ u.val W₁ t₁ (P/(D.absNorm:ℝ)) *
         original η₂ m A₂ u.val W₂ t₂ (Q/(E.absNorm:ℝ))‖^2) ≤ K) →
      (∑ u ∈ s, w u * ‖original η₁ m A₁ (rowMap (u,root)) W₁ t₁ P *
        original η₂ m A₂ (rowMap (u,root)) W₂ t₂ Q‖^2) ≤ C*U^ε*K := by
  obtain ⟨C,hC,hh⟩ := pair_divisor_budget ε L hε hL
  refine ⟨C,hC,?_⟩; intro U hU root hroot η₁ η₂ m A₁ A₂ hm₁ hm₂ s w hw W₁ W₂ t₁ t₂ b₁ b₂ P Q K hs₁ hs₂ hP hQ hK hs
  exact (pair_energy η₁ η₂ m A₁ A₂ hm₁ hm₂ root s w hw W₁ W₂ t₁ t₂ b₁ b₂ P Q K hs₁ hs₂ hP hQ hs).trans (mul_le_mul_of_nonneg_right (hh U hU root hroot) hK)

#print axioms pair_energy_subpower
end
end QRH.Cycle092.CofactorOrdinary
