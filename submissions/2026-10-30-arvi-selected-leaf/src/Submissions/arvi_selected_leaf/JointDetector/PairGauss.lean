/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.IdealPairPoisson
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.GaussSum.CubicTrace
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.QuadraticSieve.CrossSeparation

/-! Unary Gauss blocks for the selected pair. The finite product bookkeeping
below is adapted from the private helpers in OAI's `CrossSeparation` proof.
The fifth-power Gauss factor is retained literally, with its original sign. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge GaussGeneratorTransport FiniteGaussPhase
open MixedCrossSeparation MixedGaussConversion
local notation "O" => ActualEisensteinCubic.O

private theorem ordered_cross_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (A B : Finset ι)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    (∏ i, ((∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then 5 else 1)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ 5) * l i) *
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k) * l i) *
      (∏ i ∈ A, ∏ k ∈ B, x i k ^ 5 * x k i) := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then 5 else 1)) =
        (∏ k ∈ A.erase i, x i k ^ 5) * (∏ k ∈ B, x i k ^ 5) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : Finset.univ.erase i = A.erase i ∪ B := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, ite_eq_left hi, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then 5 else 1)) =
        (∏ k ∈ B.erase i, x i k) * (∏ k ∈ A, x i k) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : Finset.univ.erase i = B.erase i ∪ A := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, ite_eq_right hn, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
    simp only [pow_one]
  have hpA : (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then 5 else 1)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ 5) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ 5) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then 5 else 1)) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  calc
    _ = (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then 5 else 1)) * l i)) *
        (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then 5 else 1)) * l i)) := by
      rw [← Finset.prod_union hd, hu]
    _ = _ := by
      rw [hpA, hpB]
      rw [Finset.prod_comm (s := B) (t := A)]
      simp only [Finset.prod_mul_distrib]
      ring

private theorem prod_subtype_erase {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (A : Finset ι) (i : A) (f : ι → M) :
    (∏ k ∈ (Finset.univ : Finset A).erase i, f k.val) = ∏ k ∈ A.erase i.val, f k := by
  apply Finset.prod_bij (fun k _ => k.val)
  · intro k hk
    apply Finset.mem_erase.mpr
    refine ⟨?_, k.property⟩
    exact fun h => (Finset.mem_erase.mp hk).1 (Subtype.ext h)
  · intro a ha b hb h
    exact Subtype.ext h
  · intro k hk
    refine ⟨⟨k, (Finset.mem_erase.mp hk).2⟩, ?_, rfl⟩
    apply Finset.mem_erase.mpr
    exact ⟨fun h => (Finset.mem_erase.mp hk).1 (congrArg Subtype.val h), Finset.mem_univ _⟩
  · intro a ha
    rfl

private theorem restricted_prime_coprime {ι : Type*} (p : ι → O)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (A : Finset ι) :
    Pairwise (Function.onFun IsCoprime (fun i : A => Ideal.span {p i.val})) := by
  intro i k hik
  exact hcop (fun h => hik (Subtype.ext h))

/-- A unary row block, including its internal CRT cross factors. -/
def unaryPairGauss {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A : Finset ι) (j : ℕ) : ℂ :=
  ∏ i ∈ A, (∏ k ∈ A.erase i, crossSymbol p hg i k ^ j) *
    localGauss (p i) (hp i) (hg i) j

theorem unaryPairGauss_eq_product {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A : Finset ι) (j : ℕ) (hj : j ≠ 0) :
    unaryPairGauss p hp hg A j =
      canonicalProductGauss (fun i : A => p i.val) (fun i => hp i.val)
        (restricted_prime_coprime p hcop A) (fun i => hg i.val) (fun _ => j) := by
  rw [canonicalProductGauss_cross_factors, ← Finset.prod_mul_distrib]
  unfold unaryPairGauss
  rw [← Finset.prod_coe_sort A]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  rw [← prod_subtype_erase A i (fun k => crossSymbol p hg i.val k ^ j)]
  apply Finset.prod_congr
  · ext k; simp
  · intro k hk
    exact (MulChar.pow_apply' _ hj _).symm

theorem unaryPairGauss_norm {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A : Finset ι) (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) :
    ‖unaryPairGauss p hp hg A j‖ = 1 := by
  rw [unaryPairGauss_eq_product p hp hcop hg A j hj0]
  exact norm_canonicalProductGauss (fun i : A => p i.val) (fun i => hp i.val)
    (restricted_prime_coprime p hcop A) (fun i => hg i.val) (fun i => hchar i.val)
    (fun _ => j) (fun _ => hj0) (fun _ => hj6)

theorem product_pair_gauss_separated {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (A B : Finset ι) (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    canonicalProductGauss p hp hcop hg (fun i => if i ∈ A then 5 else 1) =
      unaryPairGauss p hp hg A 5 * unaryPairGauss p hp hg B 1 *
        quadraticRayPair (residue (∏ i ∈ A, p i)) (residue (∏ i ∈ B, p i)) := by
  rw [canonicalProductGauss_cross_factors]
  have hpow (i k : ι) :
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ (if i ∈ A then 5 else 1))
        (Ideal.Quotient.mk (Ideal.span {p i}) (p k)) =
      crossSymbol p hg i k ^ (if i ∈ A then 5 else 1) := by
    exact MulChar.pow_apply' _ (by split_ifs <;> decide) _
  simp_rw [hpow]
  change _ * (∏ i, localGauss (p i) (hp i) (hg i) (if i ∈ A then 5 else 1)) = _
  rw [← Finset.prod_mul_distrib]
  erw [ordered_cross_partition (crossSymbol p hg)
      (fun i => localGauss (p i) (hp i) (hg i) (if i ∈ A then 5 else 1)) A B hd hu]
  have hA : (∏ i ∈ A, (∏ k ∈ A.erase i, crossSymbol p hg i k ^ 5) *
      localGauss (p i) (hp i) (hg i) (if i ∈ A then 5 else 1)) =
      unaryPairGauss p hp hg A 5 := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [ite_eq_left hi]
  have hB : (∏ i ∈ B, (∏ k ∈ B.erase i, crossSymbol p hg i k) *
      localGauss (p i) (hp i) (hg i) (if i ∈ A then 5 else 1)) =
      unaryPairGauss p hp hg B 1 := by
    unfold unaryPairGauss
    simp only [pow_one]
    apply Finset.prod_congr rfl
    intro i hi
    rw [ite_eq_right (fun ha => Finset.disjoint_left.mp hd ha hi)]
  have hx : (∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg i k ^ 5 * crossSymbol p hg k i) =
      quadraticCrossPhase p hg A B := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    exact mixed_cross_eq_quadratic p hg i k (hprimary i) (hprimary k)
  rw [hA, hB, hx, quadraticCrossPhase_eq_rayPair p hp hcop hg hchar A B hd]

theorem finite_pair_row_actual {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A : Finset ι) (n : O) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun i => if i ∈ A then 5 else 1) n =
      primitivePair (Ideal.span {∏ i ∈ Finset.univ \ A, p i})
        (Ideal.span {∏ i ∈ A, p i}) n := by
  unfold primitivePair
  rw [span_finset_prod, span_finset_prod]
  simp_rw [idealRow_prime_product (fun i => Ideal.span {p i}) hg]
  have hh := finiteSexticRow_disjoint_pair (fun i => Ideal.span {p i}) hcop hg
    (Finset.univ \ A) n
  have hAA : Finset.univ \ (Finset.univ \ A) = A := by ext i; simp
  erw [hAA] at hh
  simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, ite_not] using hh

/-- The unit correction in the canonical modulus is discharged by actual
modulo-36 compatibility of the two rows. The sign of gamma_5 is untouched. -/
theorem canonical_pair_gauss_separated {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (A : Finset ι)
    (hA : Supported (Ideal.span {∏ i ∈ A, p i}))
    (hB : Supported (Ideal.span {∏ i ∈ Finset.univ \ A, p i}))
    (hmod : (∏ i ∈ Finset.univ \ A, p i) - (∏ i ∈ A, p i) ∈
      (Ideal.span {(36 : O)} : Ideal O)) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg
      (fun i => if i ∈ A then 5 else 1) =
      unaryPairGauss p hp hg A 5 * unaryPairGauss p hp hg (Finset.univ \ A) 1 *
        quadraticRayPair (residue (∏ i ∈ A, p i))
          (residue (∏ i ∈ Finset.univ \ A, p i)) := by
  rw [canonicalNormalizedGauss_eq_product p hp hcop hg,
    finite_pair_row_actual p hcop hg A,
    primitivePair_unit_of_congruent_mod36 _ _ hB hA hmod, one_mul]
  apply product_pair_gauss_separated p hp hcop hg hchar hprimary A (Finset.univ \ A)
  · exact Finset.disjoint_left.mpr (fun i hi hnot => (Finset.mem_sdiff.mp hnot).2 hi)
  · exact Finset.union_sdiff_of_subset (Finset.subset_univ A)

theorem fixed_pair_phase_norm (r : EisensteinEPrimaryPhase.Coord)
    (hr : EisensteinEPrimaryPhase.odd r) : ‖quadraticRayPair r r‖ = 1 := by
  rw [QuadraticAllOddCRT.quadraticRayPair_eq_sign r r hr hr]
  have hs : (QuadraticAllOddCRT.quadraticRaySign r r : ℂ) ^ 2 = 1 := by
    exact_mod_cast QuadraticAllOddCRT.quadraticRaySign_sq r r hr hr
  exact Complex.norm_eq_one_of_pow_eq_one hs (by decide : (2 : ℕ) ≠ 0)

/-- On one fixed row ray, the remaining factor is independent of both rows. -/
theorem canonical_pair_gauss_fixed_ray {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (A : Finset ι)
    (hA : Supported (Ideal.span {∏ i ∈ A, p i}))
    (hB : Supported (Ideal.span {∏ i ∈ Finset.univ \ A, p i}))
    (hmod : (∏ i ∈ Finset.univ \ A, p i) - (∏ i ∈ A, p i) ∈
      (Ideal.span {(36 : O)} : Ideal O))
    (r : EisensteinEPrimaryPhase.Coord) (hr : residue (∏ i ∈ A, p i) = r) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg
      (fun i => if i ∈ A then 5 else 1) =
      quadraticRayPair r r * unaryPairGauss p hp hg (Finset.univ \ A) 1 *
        unaryPairGauss p hp hg A 5 := by
  have hfour : (4 : O) ∣ (∏ i ∈ Finset.univ \ A, p i) - (∏ i ∈ A, p i) :=
    (show (4 : O) ∣ (36 : O) from ⟨9, by norm_num⟩).trans
      (Ideal.mem_span_singleton.mp hmod)
  have hsame := QuadraticGaussRay.residue_eq_of_four_dvd_sub _ _ hfour
  rw [canonical_pair_gauss_separated p hp hcop hg hchar hprimary A hA hB hmod,
    hsame, hr]
  ring

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.product_pair_gauss_separated
#print axioms Qrh.JointDetector.unaryPairGauss_norm
#print axioms Qrh.JointDetector.canonical_pair_gauss_separated
#print axioms Qrh.JointDetector.canonical_pair_gauss_fixed_ray
#print axioms Qrh.JointDetector.fixed_pair_phase_norm
