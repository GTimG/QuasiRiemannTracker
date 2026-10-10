import Cycle25.Numerator.FiniteCollect
import Cycle25.Numerator.PhysicalFront

/-! Literal physical error-mask contributions and their canonical prime fronts. -/
noncomputable section
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths Cycle25ProbeFinalAssembly ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

def sourceMaskContribution {D : MomentData} (F : WeightedSourceData D)
    (η : Character) (rows : Finset FreeRow) (J : Finset (Fin D.N))
    (Z : ℝ) (x z : ℂ) (Y : ℝ) : ℂ :=
  ∑u∈rows,(frequencyWeight z ⟨u.val,u.property.1⟩*numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z)*
    (errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun j=>source_prime_pool_outside F Z j) (fun _=>F.W) (fun j=>Z^(D.ell j)) x z F.W Y*
      (∏j:{i:Fin D.N//i∉J},∑P:sourcePrimePool F Z j.val,
        physicalSlotWeight P.val F.W (Z^(D.ell j.val)) z*(-star (idealRowHom u.val P.val.val))))

theorem source_reconstructed_sum_masks {D : MomentData} (F : WeightedSourceData D)
    (η : Character) (rows : Finset FreeRow) (Z : ℝ) (x z : ℂ) (Y : ℝ) :
    reconstructedDyadValue F.S F.exclusions F.maximal η rows (sourcePrimePool F Z)
      (fun j=>source_prime_pool_outside F Z j) (fun _=>F.W) (fun j=>Z^(D.ell j)) x z F.W Y =
      ∑J∈Finset.univ.powerset,sourceMaskContribution F η rows J Z x z Y := by
  unfold reconstructedDyadValue sourceMaskContribution
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem complement_prime_product {D : MomentData} (F : WeightedSourceData D)
    (u : FreeRow) (J : Finset (Fin D.N)) (Z : ℝ) (z : ℂ) :
    (∏j:{i:Fin D.N//i∉J},HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j.val)) z) =
      ∏j∈Finset.univ\J,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z :=
  (Finset.prod_subtype (Finset.univ\J) (by simp)
    (fun j=>HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z)).symm

theorem source_mask_physical_front {D : MomentData} (F : WeightedSourceData D)
    (η : Character) (rows : Finset FreeRow) (J : Finset (Fin D.N))
    (Z : ℝ) (hZ : 0 < Z) (x z : ℂ) (hz : z.re=17/50) (Y : ℝ)
    (hS : ∀j,∀P∈F.S,(P.absNorm:ℝ)≤Z^(D.ell j))
    (A B : ℝ) (hA : 0≤A)
    (ha : ∀u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩*
      numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z‖≤A)
    (hB : (∑u∈rows,‖errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
      (fun j=>source_prime_pool_outside F Z j) (fun _=>F.W) (fun j=>Z^(D.ell j)) x z F.W Y*
      (∏j∈Finset.univ\J,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z)‖)≤B) :
    ‖sourceMaskContribution F η rows J Z x z Y‖ ≤
      A*Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val))*B := by
  let En (u : FreeRow) := errorLabelNumerator F.S F.exclusions η u J (sourcePrimePool F Z)
    (fun j=>source_prime_pool_outside F Z j) (fun _=>F.W) (fun j=>Z^(D.ell j)) x z F.W Y
  let Main (u : FreeRow) := ∏j∈Finset.univ\J,
    HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (Z^(D.ell j)) z
  let MainRaw (u : FreeRow) := ∏j:{i:Fin D.N//i∉J},∑P:sourcePrimePool F Z j.val,
    physicalSlotWeight P.val F.W (Z^(D.ell j.val)) z*(-star (idealRowHom u.val P.val.val))
  let front : ℝ := Z^(-(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val))
  have hfront : 0 ≤ front := Real.rpow_nonneg hZ.le _
  have he (u : FreeRow) : ‖En u*MainRaw u‖=front*‖En u*Main u‖ := by
    rw [norm_mul,source_main_product_norm F Z hZ hS u J z,hz,complement_prime_product]
    rw [show (∑j:{i:Fin D.N//i∉J},D.ell j.val)*((17/50:ℝ)-1/2) =
      -(4/25:ℝ)*(∑j:{i:Fin D.N//i∉J},D.ell j.val) by ring]
    dsimp only [front]
    rw [norm_mul]
    ring
  change ‖∑u∈rows,(frequencyWeight z ⟨u.val,u.property.1⟩*
    numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z)*(En u*MainRaw u)‖ ≤ A*front*B
  calc
    _ ≤ ∑u∈rows,‖(frequencyWeight z ⟨u.val,u.property.1⟩*
        numeratorFreeRowScalar F.S F.exclusions F.maximal η u x z)*(En u*MainRaw u)‖ := norm_sum_le _ _
    _ ≤ ∑u∈rows,(A*front)*‖En u*Main u‖ := by
      apply Finset.sum_le_sum
      intro u hu
      rw [norm_mul,he]
      exact (mul_le_mul_of_nonneg_right (ha u hu) (mul_nonneg hfront (norm_nonneg _))).trans_eq (by ring)
    _ = (A*front)*(∑u∈rows,‖En u*Main u‖) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (mul_nonneg hA hfront)

end Cycle25.Numerator

/- Adapted from weighted-numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d; Apache-2.0. -/
