/- Copyright (c) 2026 Hailey Collet. Apache-2.0. Actual P.1 ordinary pair
and marked product on a sixth-root fibre. -/
import Candidate.C092.transport.OrdinaryColumn
namespace QRH.Cycle092.ActualColumn
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths CanonicalRowCompletion ConcretePrimeRowBridge
open HeckeFamily HeckeInverseAmplification CenteredMomentSourceMass CenteredMomentNaturalRowSource
open CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open Qrh.JointDetector WholeWordAmplification SlotWordProducer
open QRH.Cycle092.OrdinaryColumn
local notation "O" => ActualEisensteinCubic.O
local instance c092LocalInst_Candidate_C092_transport_ActualColumn_b325ac5a773df12c_001 (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- This coefficient matches the two independently pitched compact profiles, their
original sixth-root/cofactor row, and every genuine (unmodified) marked slot. -/
theorem pair_at (α : Type) [Fintype α] [DecidableEq α] (rayM : Ideal O) [NeZero rayM]
    (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)
    {Z bΦ : ℝ} (st : NaturalState Z 0 bΦ) (η₀ : Character) (W : ℝ → ℂ) (T : Finset α)
    (θ : T → RayQuotient.Characters rayM H) (w σ v : T → ℝ) (t : ℝ) (root : NonzeroIdeal)
    (mesh B : ℝ) (hd : (ActualSlotData.data rayM H hH st η₀ W T θ w σ v (fun _ => 0) t root).Bounded Z mesh B)
    (cores : Finset FreeRow) (η₁ η₂ : Character) (m A₁ A₂ : O) (hm₁ : goodLambda ∣ m) (hm₂ : (2:O) ∣ m)
    (W₁ W₂ : ℝ → ℂ) (t₁ t₂ b₁ b₂ P Q B₁ B₂ K X ε : ℝ) (hZ : 0 < Z)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hP : 0 < P) (hQ : 0 < Q)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hW₁ : ∀ I ∈ idealBall (b₁*P), ‖W₁ ((I.absNorm:ℝ)/P)‖ ≤ B₁)
    (hW₂ : ∀ I ∈ idealBall (b₂*Q), ‖W₂ ((I.absNorm:ℝ)/Q)‖ ≤ B₂)
    (hK : 0 ≤ K) (hX : 1 ≤ X) (hε : 0 < ε)
    (hcap : (b₁*P)*((b₂*Q)*((2:ℝ)^(Fintype.card α)*Z^(∑ i, w i))) ≤ X)
    (hsource : ∀ (S : Finset (Ideal O)) (a : S → ℂ), (∀ I ∈ S, (I.absNorm:ℝ) ≤ X) →
      ∑ z : cores.image Subtype.val, ‖FineDetectorWords.ordinaryPolynomial S a z.val‖^2 ≤ K * ∑ I, ‖a I‖^2) :
    (∑ u ∈ cores, (‖original η₁ m A₁ (rowMap (u,root)) W₁ t₁ P‖^2 * ‖original η₂ m A₂ (rowMap (u,root)) W₂ t₂ Q‖^2)*
        RefinedSupplier.slotMass rayM H hH st η₀ W θ w σ v t (rowMap (u,root))) ≤
      K * ((wordDivisorConstant (Fintype.card α+2) ε hε * X^ε) * ((128*b₁*B₁^2)*((128*b₂*B₂^2)*B^(Fintype.card α)))) := by
  let d := ActualSlotData.data rayM H hH st η₀ W T θ w σ v (fun _ => 0) t root
  have hcaps : (∏ i, (2*Z^(d.width i))) = (2:ℝ)^(Fintype.card α)*Z^(∑ i,w i) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin, ← Real.rpow_sum_of_pos hZ,ActualSlotData.data_width]
  have hp := PairedColumn.paired_energy (cores.image Subtype.val) d hd (idealBall (b₁*P)) (idealBall (b₂*Q))
    (plain η₁ m A₁ root W₁ t₁ P) (plain η₂ m A₂ root W₂ t₂ Q) (128*b₁*B₁^2) (128*b₂*B₂^2) (b₁*P) (b₂*Q) K X ε hK hX hε
    (fun I h => ((mem_idealBall _ I).mp h).1) (fun I h => ((mem_idealBall _ I).mp h).1)
    (fun I h => ((mem_idealBall _ I).mp h).2) (fun I h => ((mem_idealBall _ I).mp h).2)
    (square_mass _ _ _ _ _ _ _ _ _ hb₁ hP hW₁) (square_mass _ _ _ _ _ _ _ _ _ hb₂ hQ hW₂) (hcaps ▸ hcap) hsource
  let F (z : O) : ℝ := ‖(∑ I ∈ idealBall (b₁*P), plain η₁ m A₁ root W₁ t₁ P I * idealRowHom z I) *
    ((∑ I ∈ idealBall (b₂*Q), plain η₂ m A₂ root W₂ t₂ Q I * idealRowHom z I) * ∏ i, d.polynomial i z)‖^2
  change (∑ z : cores.image Subtype.val, F z.val) ≤ _ at hp
  rw [Finset.sum_coe_sort (cores.image Subtype.val) F,Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)] at hp
  apply le_trans (le_of_eq (Finset.sum_congr rfl (fun u _ => ?_))) hp
  dsimp only [F]
  rw [on_root η₁ m A₁ hm₁ hm₂ root u W₁ t₁ b₁ P hs₁ hP,on_root η₂ m A₂ hm₁ hm₂ root u W₂ t₂ b₂ Q hs₂ hQ,
    ← ActualSlotData.data_product rayM H hH st η₀ W T θ w σ v (fun _ => 0) t root u]
  simp only [norm_mul,mul_pow,d]; ring

#print axioms pair_at
end
end QRH.Cycle092.ActualColumn
