/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Restoration.HoleMobius

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace QRH.Record1252270103Restoration
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CenteredMomentHeckeExpansion CenteredMomentHeckeSlots
open CenteredMomentSourceMass CenteredMomentRetainedEnergy
open Record1252270103KernelMass
local notation "O" => HeckeFamily.O

def mobiusPool : Finset (Finset PrimeIdeal×Finset PrimeIdeal) := smallPrimes.powerset×ˢsmallPrimes.powerset
def mobiusPair (D : Finset PrimeIdeal×Finset PrimeIdeal) : IdealPair := (subsetProduct D.1,subsetProduct D.2)
def mobiusSign (D : Finset PrimeIdeal×Finset PrimeIdeal) : ℂ := (-1)^(D.1.card+D.2.card)

theorem divisible_plain_sum_shift (d : IdealPair) (hd : d.1≠0 ∧ d.2≠0)
    (b X₁ X₂ : ℝ) (F : IdealPair→ℂ) :
    (∑n∈(plainPairPool b X₁ X₂).filter (fun n=>d.1∣n.1 ∧ d.2∣n.2),F n) =
      ∑a∈plainPairPool b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2),F (multiplyPair d a) := by
  have hi : (plainPairPool b (X₁/Ideal.absNorm d.1) (X₂/Ideal.absNorm d.2)).image (multiplyPair d) =
      (plainPairPool b X₁ X₂).filter (fun n=>d.1∣n.1 ∧ d.2∣n.2) := by
    ext n
    constructor
    · rintro hn
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_filter.mpr ⟨(plainPairPool_multiply_iff hd).mpr ha,dvd_mul_right _ _,dvd_mul_right _ _⟩
    · intro hn
      obtain ⟨hn,hdi,hdj⟩ := Finset.mem_filter.mp hn
      have he : multiplyPair d (cofactorPair n.1 n.2 d)=n := Prod.ext (idealCofactor_mul hdi) (idealCofactor_mul hdj)
      exact Finset.mem_image.mpr ⟨cofactorPair n.1 n.2 d,
        (plainPairPool_multiply_iff hd).mp (he.symm ▸ hn),he⟩
  rw [←hi,Finset.sum_image]
  intro a ha c hc he
  exact Prod.ext (mul_left_cancel₀ hd.1 (congrArg Prod.fst he)) (mul_left_cancel₀ hd.2 (congrArg Prod.snd he))

theorem hole_plain_mobius (ψ : Ideal O →*₀ ℂ) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ) :
    ordinaryHolePlainSum ψ W₁ W₂ b X₁ X₂ =
      ∑D∈mobiusPool,mobiusSign D*ψ ((mobiusPair D).1*(mobiusPair D).2)*
        (∑a∈plainPairPool b (X₁/Ideal.absNorm (mobiusPair D).1) (X₂/Ideal.absNorm (mobiusPair D).2),
          ψ (a.1*a.2)*pairProfile W₁ W₂ (X₁/Ideal.absNorm (mobiusPair D).1) (X₂/Ideal.absNorm (mobiusPair D).2) a) := by
  unfold ordinaryHolePlainSum holePairPool
  rw [Finset.sum_filter]
  calc
    _ = ∑n∈plainPairPool b X₁ X₂,∑D₁∈smallPrimes.powerset,∑D₂∈smallPrimes.powerset,
        (if subsetProduct D₁∣n.1 ∧ subsetProduct D₂∣n.2 then (-1:ℂ)^(D₁.card+D₂.card) else 0)*
          (ψ (n.1*n.2)*pairProfile W₁ W₂ X₁ X₂ n) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnz := plainPairPool_nonzero hn
      simp_rw [←Finset.sum_mul]
      rw [←pair_hole_indicator hnz.1 hnz.2]
      split_ifs <;> simp
    _ = ∑D∈mobiusPool,∑n∈plainPairPool b X₁ X₂,
        (if (mobiusPair D).1∣n.1 ∧ (mobiusPair D).2∣n.2 then mobiusSign D else 0)*
          (ψ (n.1*n.2)*pairProfile W₁ W₂ X₁ X₂ n) := by
      rw [Finset.sum_comm]
      simp only [mobiusPool,Finset.sum_product,mobiusPair,mobiusSign]
      apply Finset.sum_congr rfl
      intro D₁ hD₁
      rw [Finset.sum_comm]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      have hdz : (mobiusPair D).1≠0 ∧ (mobiusPair D).2≠0 := ⟨subsetProduct_nonzero _,subsetProduct_nonzero _⟩
      have hh : (∑n∈plainPairPool b X₁ X₂,
          (if (mobiusPair D).1∣n.1 ∧ (mobiusPair D).2∣n.2 then mobiusSign D else 0)*
            (ψ (n.1*n.2)*pairProfile W₁ W₂ X₁ X₂ n)) =
          mobiusSign D*∑n∈(plainPairPool b X₁ X₂).filter
            (fun n=>(mobiusPair D).1∣n.1 ∧ (mobiusPair D).2∣n.2),ψ (n.1*n.2)*pairProfile W₁ W₂ X₁ X₂ n := by
        rw [Finset.mul_sum,Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        split_ifs <;> simp
      rw [hh,divisible_plain_sum_shift (mobiusPair D) hdz,Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [pairProfile_multiply]
      have he : (multiplyPair (mobiusPair D) a).1*(multiplyPair (mobiusPair D) a).2=
          ((mobiusPair D).1*(mobiusPair D).2)*(a.1*a.2) := by unfold multiplyPair;dsimp;ring
      rw [he,map_mul]
      ring

end
end QRH.Record1252270103Restoration
#print axioms QRH.Record1252270103Restoration.hole_plain_mobius
