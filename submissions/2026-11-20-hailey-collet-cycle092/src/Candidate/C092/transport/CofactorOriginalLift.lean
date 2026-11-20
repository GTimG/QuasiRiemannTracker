/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
An original cofactor fiber inherits the clean subset sources with a single
prescribed exponent loss, uniformly in the moving cofactor and all scales. -/
import Candidate.C092.transport.CofactorTotalBudget

namespace QRH.Cycle092.CofactorOrdinary
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily CenteredMomentWholeSlotDeletion
open CenteredMomentDetectorPlainFiberSource IdealMobiusDivisorSum
open QRH.Cycle092.WholeSlot QRH.Cycle092.OrdinaryColumn
local notation "O" => ActualEisensteinCubic.O
local instance c092LocalInst_Candidate_C092_transport_CofactorOriginalLift_517a355d89914ead_001 (rayM : Ideal O) [NeZero rayM] : Finite (O ⧸ rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

theorem original_marked_cofactor {ι : Type} [Fintype ι] [DecidableEq ι]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O ⧸ rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (W : ℝ → ℂ) (hW : Continuous W)
    (hs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (ε L : ℝ) (hε : 0 < ε) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : ℝ), 1 ≤ U → ∀ (B : NonzeroIdeal), (B.val.absNorm:ℝ) ≤ U^L →
    ∀ (η η₀ : Character) (θ : ι → RayQuotient.Characters rayM H) (w σ v : ι → ℝ)
      (m A : O) (W₁ W₂ : ℝ → ℂ) (t X₁ X₂ b₁ b₂ Y K : ℝ)
      (s : Finset FreeRow) (keep : Finset ι → O → Prop),
      goodLambda ∣ m → (2:O) ∣ m → (∀ i, 0 ≤ w i) → (∀ i, 0 ≤ σ i) →
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y → 0 ≤ K → (∀ u ∈ s, rowNorm u ≤ Y) →
      (∀ T u, u ∈ s → keep T u.val) →
      let S := originalPools rayM H 2 U w
      let β := originalCoefficients rayM H hH η₀ θ W U w σ v
      (∀ D ∈ idealDivisors B.val, ∀ F ∈ idealDivisors B.val, ∀ T : Finset ι,
        subsetEnergy T η m A t W₁ W₂ S β (fun i => U^(w i)) (X₁/(D.absNorm:ℝ))
          (X₂/(F.absNorm:ℝ)) (keep T) radialMajorant Y ≤ K) →
      (∑ u ∈ s, (∏ i, ‖normalizedSlot η m A (rowMap (u,B)) (S i) (β i) t (U^(w i))‖^2) *
        ‖original η m A (rowMap (u,B)) W₁ t X₁ * original η m A (rowMap (u,B)) W₂ t X₂‖^2)
        ≤ C*U^ε*K := by
  obtain ⟨δ,hδ,ht⟩ := total_budget (Fintype.card ι) L ε hL hε
  obtain ⟨J,hJ,hdel⟩ := CofactorPrime.original_cofactor_subpower (Slot:=ι) rayM H hH W hW hs δ L hδ hL
  obtain ⟨C,hC,hbudget⟩ := ht (max 1 J) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro U hU B hB η η₀ θ w σ v m A W₁ W₂ t X₁ X₂ b₁ b₂ Y K s keep hm₁ hm₂ hw hσ hs₁ hs₂ hX₁ hX₂ hY hK hy hk
  dsimp only
  intro hsrc
  let E := max 1 J * U^δ
  have hE : 1 ≤ E := one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hU hδ.le)
  have hslot (u : FreeRow) (_hu : u ∈ s) (i : ι) := hdel U hU η η₀ θ w σ v m A
    (idealGenerator B.val) u.val t hw hσ hm₁ hm₂ (idealGenerator_ne_zero _ B.property)
    (by simpa only [span_idealGenerator] using hB) i
  have h := marked_cofactor_from_clean η m A hm₁ hm₂ B s _ _ _ (fun i => Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) (w i))
    W₁ W₂ t X₁ X₂ b₁ b₂ Y E K hs₁ hs₂ hX₁ hX₂ hY hE hy keep hk (by
      intro u hu i
      rw [norm_sub_rev]
      unfold rowMap
      rw [mul_comm u.val]
      exact (hslot u hu i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) δ).le)) hsrc
  exact h.trans (by
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (hbudget U hU B hB) hK)

#print axioms original_marked_cofactor
end
end QRH.Cycle092.CofactorOrdinary
