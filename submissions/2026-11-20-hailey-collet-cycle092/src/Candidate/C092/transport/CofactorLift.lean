/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The original punctured product and ordinary pair are controlled by complete
clean energies evaluated at their own divisor-shortened lengths. -/
import Candidate.C092.transport.CofactorMarkedEnergy

namespace QRH.Cycle092.CofactorOrdinary
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentWholeSlotDeletion CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource IdealMobiusDivisorSum
open QRH.Cycle092.WholeSlot QRH.Cycle092.OrdinaryColumn
local notation "O" => ActualEisensteinCubic.O

/-- Clean positive estimates are only needed on subsets of the given slots.
Each such estimate may keep precisely the rows used by its source. -/
theorem marked_cofactor_from_clean {ι : Type} [Fintype ι] [DecidableEq ι]
    (η : Character) (m A : O) (hm₁ : goodLambda ∣ m) (hm₂ : (2:O) ∣ m)
    (B : NonzeroIdeal) (s : Finset FreeRow) (S : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (P : ι → ℝ) (hP : ∀ i, 0 < P i) (W₁ W₂ : ℝ → ℂ)
    (t X₁ X₂ b₁ b₂ Y E K : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY : 0 < Y) (hE : 1 ≤ E)
    (hy : ∀ u ∈ s, rowNorm u ≤ Y) (keep : Finset ι → O → Prop)
    (hk : ∀ T u, u ∈ s → keep T u.val)
    (herr : ∀ u ∈ s, ∀ i, ‖normalizedSlot η m A (rowMap (u,B)) (S i) (β i) t (P i) -
      normalizedSlot η m A u.val (S i) (β i) t (P i)‖ ≤ E)
    (hsrc : ∀ D ∈ idealDivisors B.val, ∀ L ∈ idealDivisors B.val, ∀ T : Finset ι,
      subsetEnergy T η m A t W₁ W₂ S β P (X₁/(D.absNorm:ℝ)) (X₂/(L.absNorm:ℝ))
        (keep T) radialMajorant Y ≤ K) :
    (∑ u ∈ s, (∏ i, ‖normalizedSlot η m A (rowMap (u,B)) (S i) (β i) t (P i)‖^2) *
      ‖original η m A (rowMap (u,B)) W₁ t X₁ * original η m A (rowMap (u,B)) W₂ t X₂‖^2)
        ≤ ((idealDivisors B.val).card:ℝ)^4 * ((2*E^2)^Fintype.card ι * 2^Fintype.card ι * K) := by
  apply pair_energy η η m A A hm₁ hm₂ B s _ (fun u _ => Finset.prod_nonneg (fun _ _ => sq_nonneg _))
    W₁ W₂ t t b₁ b₂ X₁ X₂ _ hs₁ hs₂ hX₁ hX₂
  intro D hD L hL
  have hn (J) (hJ : J ∈ idealDivisors B.val) : 0 < (J.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (ne_zero_of_dvd_ne_zero B.property ((mem_idealDivisors B.property).mp hJ)))
  apply weighted_marked_subsets s _ (fun u i => normalizedSlot η m A u.val (S i) (β i) t (P i))
    _ E K hE (fun _ _ => sq_nonneg _) herr
  intro T
  have h := finite_clean_energy η m A W₁ W₂ (fun i : T => S i.val)
    (fun i : T => β i.val) (fun i : T => P i.val) t _ _ b₁ b₂ Y hs₁ hs₂
    (div_pos hX₁ (hn D hD)) (div_pos hX₂ (hn L hL)) (fun i => hP i.val) hY s (keep T) (hk T) hy
  refine le_trans ?_ (h.trans (hsrc D hD L hL T))
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.prod_coe_sort T (fun i => ‖normalizedSlot η m A u.val (S i) (β i) t (P i)‖^2)]

#print axioms marked_cofactor_from_clean
end
end QRH.Cycle092.CofactorOrdinary
