/- Copyright (c) 2026 Hailey Collet. Apache-2.0. Positive energy transport
for the two independently shortened ordinary factors in Appendix K.3. -/
import Candidate.C092.transport.CofactorOrdinary
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

theorem factor_unit (η : Character) (m A z : O) (t : ℝ) (D : Ideal O) (hD : D ≠ 0) :
    ‖factor η m A z t D‖ ≤ 1 := by
  apply (factor_norm ..).trans
  have hN : (1:ℝ) ≤ D.absNorm := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hD)
  have hS : 1 ≤ Real.sqrt (D.absNorm:ℝ) := by simpa using Real.sqrt_le_sqrt hN
  exact inv_le_one_of_one_le₀ hS

private theorem finite_transfer {ι κ : Type*} (s : Finset ι) (l : Finset κ)
    (g : ι → ℂ) (a f : ι → κ → ℂ) (w : ι → ℝ) (K : ℝ)
    (hg : ∀ u ∈ s, g u = ∑ p ∈ l, a u p * f u p)
    (ha : ∀ u ∈ s, ∀ p ∈ l, ‖a u p‖ ≤ 1) (hw : ∀ u ∈ s, 0 ≤ w u)
    (hf : ∀ p ∈ l, (∑ u ∈ s, w u * ‖f u p‖^2) ≤ K) :
    (∑ u ∈ s, w u * ‖g u‖^2) ≤ (l.card:ℝ)^2 * K := by
  have hterm (u) (hu : u ∈ s) : w u*‖g u‖^2 ≤ (l.card:ℝ) * ∑ p ∈ l, w u*‖f u p‖^2 := by
    rw [hg u hu,Finset.mul_sum]; rw [← Finset.mul_sum]
    calc
      _ ≤ w u*((l.card:ℝ)*∑ p ∈ l, ‖a u p * f u p‖^2) := mul_le_mul_of_nonneg_left (CubicEisenstein.norm_sum_sq_le_card l _) (hw u hu)
      _ ≤ w u*((l.card:ℝ)*∑ p ∈ l, ‖f u p‖^2) := by
        apply mul_le_mul_of_nonneg_left _ (hw u hu); apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum; intro p hp; apply pow_le_pow_left₀ (norm_nonneg _)
        rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (ha u hu p hp)
      _ = _ := by rw [← Finset.mul_sum]; ring
  calc
    _ ≤ ∑ u ∈ s, (l.card:ℝ) * ∑ p ∈ l, w u * ‖f u p‖^2 := Finset.sum_le_sum hterm
    _ = (l.card:ℝ) * ∑ p ∈ l, ∑ u ∈ s, w u * ‖f u p‖^2 := by rw [← Finset.mul_sum,Finset.sum_comm]
    _ ≤ (l.card:ℝ) * ∑ _p ∈ l, K := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hf) (by positivity)
    _ = _ := by simp [pow_two,mul_assoc]

/-- The weight can retain the actual selected rows, all products of marks,
and the radial weight. Neither length is replaced by the other's length. -/
theorem pair_energy (η₁ η₂ : Character) (m A₁ A₂ : O) (hm₁ : goodLambda ∣ m) (hm₂ : (2:O) ∣ m)
    (root : NonzeroIdeal) (s : Finset FreeRow) (w : FreeRow → ℝ) (hw : ∀ u ∈ s, 0 ≤ w u)
    (W₁ W₂ : ℝ → ℂ) (t₁ t₂ b₁ b₂ P Q K : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hP : 0 < P) (hQ : 0 < Q)
    (hshort : ∀ D ∈ idealDivisors root.val, ∀ E ∈ idealDivisors root.val,
      (∑ u ∈ s, w u * ‖original η₁ m A₁ u.val W₁ t₁ (P/(D.absNorm:ℝ)) *
        original η₂ m A₂ u.val W₂ t₂ (Q/(E.absNorm:ℝ))‖^2) ≤ K) :
    (∑ u ∈ s, w u * ‖original η₁ m A₁ (rowMap (u,root)) W₁ t₁ P *
      original η₂ m A₂ (rowMap (u,root)) W₂ t₂ Q‖^2) ≤ ((idealDivisors root.val).card:ℝ)^4 * K := by
  let S := idealDivisors root.val
  let aa (u : FreeRow) (d : Ideal O × Ideal O) := factor η₁ m A₁ u.val t₁ d.1 * factor η₂ m A₂ u.val t₂ d.2
  let ff (u : FreeRow) (d : Ideal O × Ideal O) := original η₁ m A₁ u.val W₁ t₁ (P/(d.1.absNorm:ℝ)) * original η₂ m A₂ u.val W₂ t₂ (Q/(d.2.absNorm:ℝ))
  have hne (D) (hD : D ∈ S) := ne_zero_of_dvd_ne_zero root.property ((mem_idealDivisors root.property).mp hD)
  have h := finite_transfer s (S ×ˢ S) (fun u => original η₁ m A₁ (rowMap (u,root)) W₁ t₁ P * original η₂ m A₂ (rowMap (u,root)) W₂ t₂ Q) aa ff w K (by
    intro u _; rw [exact_sum η₁ m A₁ hm₁ hm₂ root u W₁ t₁ b₁ P hs₁ hP, exact_sum η₂ m A₂ hm₁ hm₂ root u W₂ t₂ b₂ Q hs₂ hQ, Finset.sum_mul_sum, Finset.sum_product]
    apply Finset.sum_congr rfl; intro D _; apply Finset.sum_congr rfl; intro E _; dsimp [aa,ff]; ring) (by
    intro u _ d hd; obtain ⟨hD,hE⟩ := Finset.mem_product.mp hd; dsimp only [aa]; rw [norm_mul]
    exact (mul_le_mul (factor_unit _ _ _ _ _ _ (hne _ hD)) (factor_unit _ _ _ _ _ _ (hne _ hE)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)) hw (by
    intro d hd; obtain ⟨hD,hE⟩ := Finset.mem_product.mp hd; exact hshort _ hD _ hE)
  convert h using 1 <;> simp only [Finset.card_product,Nat.cast_mul,S] <;> ring

#print axioms pair_energy
end
end QRH.Cycle092.CofactorOrdinary
