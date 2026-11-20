/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Finite genuine marked fourth supplier for the independent ordinary bridge. -/
import Candidate.C092.transport.CofactorIndependentPair
import Candidate.C092.transport.TinyCoreBridgeRetained

namespace QRH.Cycle092.CofactorOrdinary
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource CenteredMomentEnergyBands
open QRH.Cycle092.OrdinaryColumn QRH.Cycle092.TinyCore QRH.Cycle092.WholeSlot
open QRH.Cycle092.NativeStrip
local notation "O" => ActualEisensteinCubic.O

theorem finite_selected_energy {Slot : Type} (F : Finset Slot)
    (η : Character) (m A : O) (W₁ W₂ : ℝ → ℂ)
    (S : Slot → Finset (Ideal O)) (β : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (t X₁ X₂ b₁ b₂ Y : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀ i, 0 < P i) (hY : 0 < Y)
    (s : Finset FreeRow) (keep : O → Prop) (hk : ∀ u ∈ s, keep u.val)
    (hy : ∀ u ∈ s, rowNorm u ≤ Y) :
    (∑ u ∈ s, (∏ i ∈ F, ‖normalizedSlot η m A u.val (S i) (β i) t (P i)‖^2)*
      ‖original η m A u.val W₁ t X₁*original η m A u.val W₂ t X₂‖^2) ≤
      subsetEnergy F η m A t W₁ W₂ S β P X₁ X₂ keep radialMajorant Y := by
  have h := finite_clean_energy η m A W₁ W₂ (fun i : F => S i.val)
    (fun i : F => β i.val) (fun i : F => P i.val) t X₁ X₂ b₁ b₂ Y hs₁ hs₂
    hX₁ hX₂ (fun i => hP i.val) hY s keep hk hy
  refine le_trans ?_ h
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.prod_coe_sort F (fun i => ‖normalizedSlot η m A u.val (S i) (β i) t (P i)‖^2)]

/-- Cauchy on actual finite subrows, with the genuine duplicated short
marks. Characters and heights on the two ordinary factors are independent. -/
theorem finite_independent_marked_cauchy {Slot : Type} (F : Finset Slot)
    (η₁ η₂ : Character) (m A : O) (W₁ W₂ : ℝ → ℂ)
    (S : Slot → Finset (Ideal O)) (β : Slot → Ideal O → ℂ) (P : Slot → ℝ)
    (t₁ t₂ X₁ X₂ b₂ Y : ℝ)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) (hX₂ : 0 < X₂)
    (hP : ∀ i, 0 < P i) (hY : 0 < Y)
    (s : Finset FreeRow) (keep : O → Prop) (hk : ∀ u ∈ s, keep u.val)
    (hy : ∀ u ∈ s, rowNorm u ≤ Y) :
    (∑ u ∈ s, ‖original η₁ m A u.val W₁ t₁ X₁‖^2*
      ‖original η₂ m A u.val W₂ t₂ X₂‖^2*
      (∏ i ∈ F, ‖normalizedSlot η₂ m A u.val (S i) (β i) t₂ (P i)‖^2)) ≤
      Real.sqrt (∑ u ∈ s, ‖original η₁ m A u.val W₁ t₁ X₁‖^4)*
      Real.sqrt (subsetEnergy (duplicated F) η₂ m A t₂ W₂ W₂
        (fun j => S j.2) (fun j => β j.2) (fun j => P j.2) X₂ X₂ keep radialMajorant Y) := by
  have hshort := finite_selected_energy (duplicated F) η₂ m A W₂ W₂
    (fun j => S j.2) (fun j => β j.2) (fun j => P j.2) t₂ X₂ X₂ b₂ b₂ Y
    hs₂ hs₂ hX₂ hX₂ (fun j => hP j.2) hY s keep hk hy
  have he : (∑ u ∈ s,
      (‖original η₂ m A u.val W₂ t₂ X₂‖^2*
       (∏ i ∈ F, ‖normalizedSlot η₂ m A u.val (S i) (β i) t₂ (P i)‖^2))^2) ≤
      subsetEnergy (duplicated F) η₂ m A t₂ W₂ W₂
        (fun j => S j.2) (fun j => β j.2) (fun j => P j.2) X₂ X₂ keep radialMajorant Y := by
    apply le_trans (le_of_eq ?_) hshort
    apply Finset.sum_congr rfl
    intro u hu
    simp only [duplicated,Finset.prod_product,Fin.prod_univ_two,norm_mul]
    ring
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun u => ‖original η₁ m A u.val W₁ t₁ X₁‖^2)
    (fun u => ‖original η₂ m A u.val W₂ t₂ X₂‖^2*
      (∏ i ∈ F, ‖normalizedSlot η₂ m A u.val (S i) (β i) t₂ (P i)‖^2))
  simp only [←pow_mul] at hcs
  have h := hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (Real.sqrt_nonneg _))
  simpa only [mul_assoc] using h

#print axioms finite_selected_energy
#print axioms finite_independent_marked_cauchy
end
end QRH.Cycle092.CofactorOrdinary
