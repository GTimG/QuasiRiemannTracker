/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Arbitrary row-kernel transport through the true colored common allocation. -/
import Candidate.C092.transport.TwistedRawBallCoefficient
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawBall
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile CenteredMomentFirstSectors
open CenteredMomentCommonAllocationSum CenteredMomentLiveDomain CenteredMomentSourceRectangle
open QRH.SilDensitySplit.CubeFree.FP
open QRH.Cycle092.TwistedRawSource
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance (priority := 2000) sumDictionaryDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _

theorem common_masked_column_sum (ω₁ ω₂ : Id →*₀ ℂ) (H : Id)
    (S : (ι ⊕ Fin 2) → Finset Id) (hS : ∀ j, ∀ I ∈ S j, I ≠ 0)
    (hp : ∀ i, ∀ I ∈ S (Sum.inl i), Prime I)
    (G R seed D : Id) (hG : G ≠ 0) (hseed : seed ∣ G)
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Id) (f : Id → ℂ) :
    (∑ I ∈ residualPool G hG (finiteColumns (Fintype.piFinset S)),
      (if IsCoprime G I ∧ D ∣ I then
        coloredColumn (Fintype.piFinset S) H ω₁ ω₂
          (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed) (G*I) else 0) * f I) =
      ∑ B : actualAllocations S G,
        (MixedCommonCoefficient.frozenWeight H B.val * ordinaryColor ω₁ ω₂ B.val *
          frozenCoefficient B.val G R ν Wslot P) *
        ∑ v ∈ liveBox S B.val (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1,
          if D ∣ finiteTupleProduct v then
            coloredTuple H ω₁ ω₂
              (liveProfile B.val G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) v * f (finiteTupleProduct v)
          else 0 := by
  let Q := residualPool G hG (finiteColumns (Fintype.piFinset S))
  let β := coloredColumn (Fintype.piFinset S) H ω₁ ω₂
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed)
  let c (B : actualAllocations S G) : ℂ :=
    MixedCommonCoefficient.frozenWeight H B.val * ordinaryColor ω₁ ω₂ B.val *
      frozenCoefficient B.val G R ν Wslot P
  let d (B : actualAllocations S G) (I : Id) : ℂ :=
    coloredColumn (liveBox S B.val (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1)
      H ω₁ ω₂ (liveProfile B.val G R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I
  let g (I : Id) : ℂ := if D ∣ I then f I else 0
  have hQ (I : Id) (hI : I ∈ Q) : I ≠ 0 := by
    have hm := (mem_residualPool G hG _ I).mp hI
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hm
    have hz : finiteTupleProduct v ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun j _ => hS j _ (Fintype.mem_piFinset.mp hv j))
    exact right_ne_zero_of_mul (he ▸ hz)
  have hsupp (B : actualAllocations S G) (I : Id) (hne : d B I ≠ 0) :
      G*I ∈ finiteColumns (Fintype.piFinset S) ∧ I ≠ 0 ∧ IsCoprime G I := by
    exact MixedCommonEnergy.masked_live_support S hS hp B.val
      (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1 G R I
      (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
      ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
      (fun v => MixedCommonCoefficient.tupleWeight H v * ordinaryColor ω₁ ω₂ v) hne
  have hexpand (I : Id) (hI : I ∈ Q) :
      (if IsCoprime G I then β (G*I) else 0) = ∑ B, c B*d B I := by
    by_cases hc : IsCoprime G I
    · rw [ite_eq_left hc]
      exact colored_column_allocations H S hS hp G R seed I hG (hQ I hI) hc hseed
        ω₁ ω₂ ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂
    · rw [ite_eq_right hc]
      symm
      apply Finset.sum_eq_zero
      intro B hB
      have hz : d B I = 0 := by
        by_contra hn
        exact hc (hsupp B I hn).2.2
      rw [hz, mul_zero]
  calc
    _ = ∑ I ∈ Q, (if IsCoprime G I then β (G*I) else 0)*g I := by
      apply Finset.sum_congr rfl
      intro I hI
      dsimp only [β, g]
      by_cases hc : IsCoprime G I <;> by_cases hd : D ∣ I <;> simp [hc, hd]
    _ = ∑ B : actualAllocations S G, c B * ∑ I ∈ Q, d B I*g I := by
      simp_rw [Finset.sum_congr rfl (fun I hI => congrArg (fun z : ℂ => z*g I) (hexpand I hI)), Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro B hB
      dsimp only [c]
      congr 1
      have he := sum_same_support Q
        (finiteColumns (liveBox S B.val (allocation_data S G B.val (Finset.mem_filter.mp B.property).1).1))
        (d B) g (fun I _ hn => finite_column_mem _ _ I hn) (by
          intro I _ hn
          exact (mem_residualPool G hG _ I).mpr (hsupp B I hn).1)
      rw [he]
      unfold d coloredColumn
      rw [finite_column_regroup]
      apply Finset.sum_congr rfl
      intro v hv
      dsimp only [g]
      split_ifs <;> ring

#print axioms common_masked_column_sum
end
end QRH.Cycle092.TwistedRawBall
