/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Sum the sharp exceptional child payment over the full original allocation set.
The actual ordinary norm moment is retained before the common-norm relaxation. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Coefficient.CorrectedExceptionalSharpCost
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Source
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentAddedZeroUniform CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentCommonProfile
open CenteredMomentCanonicalFirst
open QRH.Record1252270103Source.ForcedCost
open Record1252270103Second
local notation "O"=>ActualEisensteinCubic.O
local notation "frozenCost"=>CenteredMomentCommonExceptionalCost.frozenProfile
variable {ι : Type*} [Fintype ι]
local instance correctedExceptionalSharpAllocationDecidable : DecidableEq ι := Classical.decEq _

theorem corrected_allocation_budget_sharp (s : Input ι) (X R : Ideal O) (hX : X≠0)
    (S : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q C D seed : Ideal O)
    (U : Finset (CommonIndex C D)) (Z ε εL α Lraw Cr Mrow C₀ K₀ : ℝ)
    (hα : 0≤α) (hZ : 0≤Z) (hCr : 0≤Cr) (hK₀ : 0≤K₀) :
    allocationBudget s X R (fun B=>correctedAllocatedBudget s X R B S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀)≤
      ((actualAllocations s.pools X).card:ℝ)*
        (∑B : actualAllocations s.pools X,(ordinaryNorm B.val)^(2*α))*
          ((frozenCost s)^2/(X.absNorm:ℝ)^2)*
            correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀ := by
  let E:=correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀
  unfold allocationBudget
  calc
    _≤((actualAllocations s.pools X).card:ℝ)*∑B : actualAllocations s.pools X,
      ((frozenCost s)^2*(ordinaryNorm B.val)^(2*α)/(X.absNorm:ℝ)^2)*E := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun B _=>corrected_allocated_weighted_budget_sharp s X R hX B
        S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀ hα hZ hCr hK₀)
    _=_ := by
      have he : (∑B : actualAllocations s.pools X,
          ((frozenCost s)^2*(ordinaryNorm B.val)^(2*α)/(X.absNorm:ℝ)^2)*E)=
          (∑B : actualAllocations s.pools X,(ordinaryNorm B.val)^(2*α))*
            ((frozenCost s)^2/(X.absNorm:ℝ)^2)*E := by
        rw [Finset.sum_mul,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro B hB
        ring
      rw [he]
      dsimp only [E]
      ring

lemma ordinaryNorm_le_common (s : Input ι) (X : Ideal O) (hX : X≠0)
    (B : actualAllocations s.pools X) : ordinaryNorm B.val≤(X.absNorm:ℝ) := by
  have hprod : finiteTupleProduct B.val=X := (Finset.mem_filter.mp B.property).2
  have hd:=plain_product_dvd_tuple B.val
  rw [hprod] at hd
  exact corrected_norm_mono_of_dvd _ X hX hd

theorem corrected_allocation_budget_sharp_norm (s : Input ι) (X R : Ideal O) (hX : X≠0)
    (S : Finset (ℕ×ℕ)) (W₁ W₂ Φ : 𝓢(ℝ,ℂ)) (Q C D seed : Ideal O)
    (U : Finset (CommonIndex C D)) (Z ε εL α Lraw Cr Mrow C₀ K₀ : ℝ)
    (hα : 0≤α) (hZ : 0≤Z) (hCr : 0≤Cr) (hK₀ : 0≤K₀) :
    allocationBudget s X R (fun B=>correctedAllocatedBudget s X R B S W₁ W₂ Φ Q C D seed U
      Z ε εL α Lraw Cr Mrow C₀ K₀)≤
      ((actualAllocations s.pools X).card:ℝ)^2*(X.absNorm:ℝ)^(2*α)*
        ((frozenCost s)^2/(X.absNorm:ℝ)^2)*
          correctedExceptionalBudget s S W₁ W₂ Φ Q C D seed U Z ε εL α Lraw Cr Mrow C₀ K₀ := by
  have heach (B : actualAllocations s.pools X) : (ordinaryNorm B.val)^(2*α)≤(X.absNorm:ℝ)^(2*α) :=
    Real.rpow_le_rpow (zero_le_one.trans (ordinaryNorm_ge_one s X B))
      (ordinaryNorm_le_common s X hX B) (by positivity)
  have hsum : (∑B : actualAllocations s.pools X,(ordinaryNorm B.val)^(2*α))≤
      ((actualAllocations s.pools X).card:ℝ)*(X.absNorm:ℝ)^(2*α) := by
    have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun B _=>heach B)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] using hh
  have hE:=correctedExceptionalBudget_nonneg s S W₁ W₂ Φ Q C D seed U
    Z ε εL α Lraw Cr Mrow C₀ K₀ hZ hCr hK₀
  have hh:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (actualAllocations s.pools X).card))
      (div_nonneg (sq_nonneg (frozenCost s)) (sq_nonneg (X.absNorm:ℝ)))) hE
  apply (corrected_allocation_budget_sharp s X R hX S W₁ W₂ Φ Q C D seed U
    Z ε εL α Lraw Cr Mrow C₀ K₀ hα hZ hCr hK₀).trans
  convert hh using 1 <;> ring
end
end OAI.SevenEighths.Record1252270103Source
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_allocation_budget_sharp
#print axioms OAI.SevenEighths.Record1252270103Source.corrected_allocation_budget_sharp_norm
