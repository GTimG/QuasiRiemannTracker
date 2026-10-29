/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.AdmissiblePairPoisson

/-! Squarefree power colours needed by the natural five-colour argument.
The local cross factor at power j is the j-th power of the established
quadratic ray phase. Unary Gauss blocks keep their actual j/6-j values.
This adds no natural-row arbitrary-power norm assertion and incurs no loss.
-/

namespace Qrh.JointDetector.PowerPairGauss
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge GaussGeneratorTransport FiniteGaussPhase
open MixedCrossSeparation MixedGaussConversion EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local instance (F : Finset (Ideal O)) : DecidableEq (primePool F) := Classical.decEq _

theorem sixth_root_cross (x y : ℂ) (j : ℕ) (hj : j < 6) (hx : x ^ 6 = 1) :
    x ^ (6-j) * y ^ j = (x ^ 5 * y) ^ j := by
  have he : Nat.ModEq 6 (6-j) (5*j) := by
    change (6-j) % 6 = (5*j) % 6
    omega
  rw [mul_pow, ← pow_mul, pow_eq_pow_of_modEq he hx]

private theorem ordered_cross_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (A B : Finset ι)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) (r t : ℕ) :
    (∏ i, ((∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then r else t)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ r) * l i) *
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ t) * l i) *
      (∏ i ∈ A, ∏ k ∈ B, x i k ^ r * x k i ^ t) := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then r else t)) =
        (∏ k ∈ A.erase i, x i k ^ r) * (∏ k ∈ B, x i k ^ r) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : Finset.univ.erase i = A.erase i ∪ B := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, ite_eq_left hi, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then r else t)) =
        (∏ k ∈ B.erase i, x i k ^ t) * (∏ k ∈ A, x i k ^ t) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : Finset.univ.erase i = B.erase i ∪ A := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, ite_eq_right hn, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then r else t)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ r) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ r) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then r else t)) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ t) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k ^ t) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  calc
    _ = (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then r else t)) * l i)) *
        (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then r else t)) * l i)) := by
      rw [← Finset.prod_union hd, hu]
    _ = _ := by
      rw [hpA, hpB, Finset.prod_comm (s := B) (t := A)]
      simp only [Finset.prod_mul_distrib]
      ring

/-- Exact CRT Gauss separation for every nonzero squarefree colour. -/
theorem product_pair_gauss_separated {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (A B : Finset ι) (hd : Disjoint A B) (hu : A ∪ B = Finset.univ)
    (j : ℕ) (hj0 : 0 < j) (hj6 : j < 6) :
    canonicalProductGauss p hp hcop hg (fun i => if i ∈ A then 6-j else j) =
      unaryPairGauss p hp hg A (6-j) * unaryPairGauss p hp hg B j *
        quadraticRayPair (residue (∏ i ∈ A, p i)) (residue (∏ i ∈ B, p i)) ^ j := by
  rw [canonicalProductGauss_cross_factors]
  have hpow (i k : ι) :
      (canonicalSextic (Ideal.span {p i}) (hg i) ^ (if i ∈ A then 6-j else j))
        (Ideal.Quotient.mk (Ideal.span {p i}) (p k)) =
      crossSymbol p hg i k ^ (if i ∈ A then 6-j else j) := by
    exact MulChar.pow_apply' _ (by split_ifs <;> omega) _
  simp_rw [hpow]
  change _ * (∏ i, localGauss (p i) (hp i) (hg i) (if i ∈ A then 6-j else j)) = _
  rw [← Finset.prod_mul_distrib]
  erw [ordered_cross_partition (crossSymbol p hg)
    (fun i => localGauss (p i) (hp i) (hg i) (if i ∈ A then 6-j else j)) A B hd hu (6-j) j]
  have hA : (∏ i ∈ A, (∏ k ∈ A.erase i, crossSymbol p hg i k ^ (6-j)) *
      localGauss (p i) (hp i) (hg i) (if i ∈ A then 6-j else j)) =
      unaryPairGauss p hp hg A (6-j) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [ite_eq_left hi]
  have hB : (∏ i ∈ B, (∏ k ∈ B.erase i, crossSymbol p hg i k ^ j) *
      localGauss (p i) (hp i) (hg i) (if i ∈ A then 6-j else j)) =
      unaryPairGauss p hp hg B j := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [ite_eq_right (fun ha => Finset.disjoint_left.mp hd ha hi)]
  rw [hA, hB]
  have hcross : (∏ i ∈ A, ∏ k ∈ B,
      crossSymbol p hg i k ^ (6-j) * crossSymbol p hg k i ^ j) =
      quadraticCrossPhase p hg A B ^ j := by
    unfold quadraticCrossPhase
    simp only [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    have hik : i ≠ k := fun he => Finset.disjoint_left.mp hd hi (he ▸ hk)
    have hsix : crossSymbol p hg i k ^ 6 = 1 := by
      simpa only [crossSymbol, map_pow,
        ite_eq_right (prime_generator_not_mem_other p hcop i k hik)] using
        canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)
    rw [sixth_root_cross _ _ j hj6 hsix,
      mixed_cross_eq_quadratic p hg i k (hprimary i) (hprimary k)]
  rw [hcross, quadraticCrossPhase_eq_rayPair p hp hcop hg hchar A B hd]

theorem zero_or_sixth_root_power (z : ℂ) (hz : z = 0 ∨ z ^ 6 = 1)
    (j : ℕ) (hj0 : 0 < j) (hj6 : j < 6) :
    z ^ (6-j) = (z ^ 5) ^ j := by
  rcases hz with hz | hz
  · simp [hz, Nat.ne_of_gt hj0, show 6-j ≠ 0 by omega]
  · rw [← pow_mul]
    apply pow_eq_pow_of_modEq _ hz
    change (6-j) % 6 = (5*j) % 6
    omega

/-- The power is applied to the actual primitive pair, including its zeros. -/
theorem finite_pair_row_power {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (A : Finset ι) (j : ℕ)
    (hj0 : 0 < j) (hj6 : j < 6) (n : O) :
    finiteSexticRow P hg (fun i => if i ∈ A then 6-j else j) n =
      (finiteSexticRow P hg (fun i => if i ∈ A then 5 else 1) n) ^ j := by
  unfold finiteSexticRow
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ A
  · simp only [ite_eq_left hi]
    rw [MulChar.pow_apply' _ (show 6-j ≠ 0 by omega),
      MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0)]
    have hsix : (canonicalSextic (P i) (hg i) (Ideal.Quotient.mk (P i) n)) ^ 6 =
        if n ∈ P i then 0 else 1 := by
      simpa only [map_pow] using canonicalSextic_sixth_power_mask (P i) (hg i) n
    apply zero_or_sixth_root_power _ _ j hj0 hj6
    by_cases hn : n ∈ P i
    · left
      exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp (by simpa only [ite_eq_left hn] using hsix)
    · right
      simpa only [ite_eq_right hn] using hsix
  · simp only [ite_eq_right hi]
    rw [MulChar.pow_apply' _ hj0.ne', MulChar.pow_apply' _ (by decide : (1 : ℕ) ≠ 0), pow_one]

theorem finite_pair_row_actual {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A : Finset ι)
    (j : ℕ) (hj0 : 0 < j) (hj6 : j < 6) (n : O) :
    finiteSexticRow (fun i => Ideal.span {p i}) hg (fun i => if i ∈ A then 6-j else j) n =
      (primitivePair (Ideal.span {∏ i ∈ Finset.univ \ A, p i})
        (Ideal.span {∏ i ∈ A, p i}) n) ^ j := by
  rw [finite_pair_row_power _ hg A j hj0 hj6,
    Qrh.JointDetector.finite_pair_row_actual p hcop hg A n]

/-- The canonical conductor unit disappears by the original full mod36
condition before taking powers. This is a squarefree-pair identity. -/
theorem canonical_pair_gauss_separated {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (A : Finset ι)
    (hA : Supported (Ideal.span {∏ i ∈ A, p i}))
    (hB : Supported (Ideal.span {∏ i ∈ Finset.univ \ A, p i}))
    (hmod : (∏ i ∈ Finset.univ \ A, p i) - (∏ i ∈ A, p i) ∈
      (Ideal.span {(36 : O)} : Ideal O))
    (j : ℕ) (hj0 : 0 < j) (hj6 : j < 6) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg
      (fun i => if i ∈ A then 6-j else j) =
      unaryPairGauss p hp hg A (6-j) * unaryPairGauss p hp hg (Finset.univ \ A) j *
        quadraticRayPair (residue (∏ i ∈ A, p i))
          (residue (∏ i ∈ Finset.univ \ A, p i)) ^ j := by
  rw [canonicalNormalizedGauss_eq_product p hp hcop hg,
    finite_pair_row_actual p hcop hg A j hj0 hj6,
    primitivePair_unit_of_congruent_mod36 _ _ hB hA hmod, one_pow, one_mul]
  apply product_pair_gauss_separated p hp hcop hg hchar hprimary
    A (Finset.univ \ A) _ _ j hj0 hj6
  · exact Finset.disjoint_left.mpr (fun i hi hnot => (Finset.mem_sdiff.mp hnot).2 hi)
  · exact Finset.union_sdiff_of_subset (Finset.subset_univ A)

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
    (r : EisensteinEPrimaryPhase.Coord) (hr : residue (∏ i ∈ A, p i) = r)
    (j : ℕ) (hj0 : 0 < j) (hj6 : j < 6) :
    canonicalNormalizedGauss (fun i => Ideal.span {p i}) hcop hg
      (fun i => if i ∈ A then 6-j else j) =
      quadraticRayPair r r ^ j * unaryPairGauss p hp hg (Finset.univ \ A) j *
        unaryPairGauss p hp hg A (6-j) := by
  have hfour : (4 : O) ∣ (∏ i ∈ Finset.univ \ A, p i) - (∏ i ∈ A, p i) :=
    (show (4 : O) ∣ (36 : O) from ⟨9, by norm_num⟩).trans (Ideal.mem_span_singleton.mp hmod)
  have hsame := QuadraticGaussRay.residue_eq_of_four_dvd_sub _ _ hfour
  rw [canonical_pair_gauss_separated p hp hcop hg hchar hprimary A hA hB hmod j hj0 hj6,
    hsame, hr]
  ring

/-- The active prime set remains the union of the two original squarefree
supports. Taking a colour power does not enlarge the conductor. -/
def selectedPairGauss {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (j : ℕ) : ℂ :=
  canonicalNormalizedGauss (fun i : (S ∪ T : Finset ι) => Ideal.span {p i.val})
    (selectedPrimeCoprime p hcop (S ∪ T)) (fun i => hg i.val)
    (fun i => if i.val ∈ T then 6-j else j)

theorem selectedPairRow_actual {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (hd : Disjoint S T) (j : ℕ)
    (hj0 : 0 < j) (hj6 : j < 6) (n : O) :
    finiteSexticRow (fun i : (S ∪ T : Finset ι) => Ideal.span {p i.val})
      (fun i => hg i.val) (fun i => if i.val ∈ T then 6-j else j) n =
      (primitivePair (Ideal.span {∏ i ∈ S, p i})
        (Ideal.span {∏ i ∈ T, p i}) n) ^ j := by
  let : DecidableEq (S ∪ T : Finset ι) := fun a b => Classical.propDecidable (a = b)
  have he : Finset.univ \ supportIn (S ∪ T) T = supportIn (S ∪ T) S := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, mem_supportIn, true_and]
    constructor
    · intro hn; exact (Finset.mem_union.mp i.property).resolve_right hn
    · intro hi ht; exact Finset.disjoint_left.mp hd hi ht
  have hh := finite_pair_row_actual (fun i : (S ∪ T : Finset ι) => p i.val)
    (selectedPrimeCoprime p hcop (S ∪ T)) (fun i => hg i.val)
    (supportIn (S ∪ T) T) j hj0 hj6 n
  rw [he, prod_supportIn (S ∪ T) S Finset.subset_union_left,
    prod_supportIn (S ∪ T) T Finset.subset_union_right] at hh
  simpa only [mem_supportIn] using hh

theorem selectedPairGauss_fixed_ray {ι : Type*}
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1)
    (S T : Finset ι) (hd : Disjoint S T)
    (hS : Supported (Ideal.span {∏ i ∈ S, p i}))
    (hT : Supported (Ideal.span {∏ i ∈ T, p i}))
    (hmod : (∏ i ∈ S, p i) - (∏ i ∈ T, p i) ∈
      (Ideal.span {(36 : O)} : Ideal O))
    (r : EisensteinEPrimaryPhase.Coord) (hr : residue (∏ i ∈ T, p i) = r)
    (j : ℕ) (hj0 : 0 < j) (hj6 : j < 6) :
    selectedPairGauss p hcop hg S T j = quadraticRayPair r r ^ j *
      unaryPairGauss p hp hg S j * unaryPairGauss p hp hg T (6-j) := by
  let : DecidableEq (S ∪ T : Finset ι) := fun a b => Classical.propDecidable (a = b)
  have hSc : S ⊆ S ∪ T := Finset.subset_union_left
  have hTc : T ⊆ S ∪ T := Finset.subset_union_right
  have he : Finset.univ \ supportIn (S ∪ T) T = supportIn (S ∪ T) S := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, mem_supportIn, true_and]
    constructor
    · intro hn; exact (Finset.mem_union.mp i.property).resolve_right hn
    · intro hi ht; exact Finset.disjoint_left.mp hd hi ht
  have hprodT := prod_supportIn (S ∪ T) T hTc p
  have hprodS : (∏ i ∈ Finset.univ \ supportIn (S ∪ T) T, p i.val) =
      ∏ i ∈ S, p i := by rw [he]; exact prod_supportIn _ _ hSc p
  have hh := canonical_pair_gauss_fixed_ray (fun i : (S ∪ T : Finset ι) => p i.val)
    (fun i => hp i.val) (selectedPrimeCoprime p hcop (S ∪ T))
    (fun i => hg i.val) (fun i => hchar i.val) (fun i => hprimary i.val)
    (supportIn (S ∪ T) T) (by simpa only [hprodT] using hT)
    (by simpa only [hprodS] using hS) (by simpa only [hprodT, hprodS] using hmod)
    r (by simpa only [hprodT] using hr) j hj0 hj6
  rw [he, unaryPairGauss_supportIn p hp hg (S ∪ T) S hSc,
    unaryPairGauss_supportIn p hp hg (S ∪ T) T hTc] at hh
  simpa only [selectedPairGauss, mem_supportIn] using hh

def admissiblePairGauss (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (I J : Ideal O) (j : ℕ) : ℂ :=
  let := admissiblePoolMaximal F hF
  selectedPairGauss (poolPrimary F) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) (idealSupport F I) (idealSupport F J) j

theorem admissiblePairGauss_fixed_ray (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (I J : Ideal O) (hIF : I ∈ F) (hJF : J ∈ F)
    (hIJ : IsCoprime I J)
    (hmod : primaryGenerator I - primaryGenerator J ∈ (Ideal.span {(36 : O)} : Ideal O))
    (r : EisensteinEPrimaryPhase.Coord) (hr : residue (primaryGenerator J) = r)
    (j : ℕ) (hj0 : 0 < j) (hj6 : j < 6) :
    admissiblePairGauss F hF I J j = quadraticRayPair r r ^ j *
      admissibleUnaryGauss F hF I j * admissibleUnaryGauss F hF J (6-j) := by
  let := admissiblePoolMaximal F hF
  unfold admissiblePairGauss Qrh.JointDetector.admissibleUnaryGauss
  change selectedPairGauss (poolPrimary F) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) (idealSupport F I) (idealSupport F J) j =
      quadraticRayPair r r ^ j *
        unaryPairGauss (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_good F hF) (idealSupport F I) j *
        unaryPairGauss (poolPrimary F) (poolPrimary_ne_zero F hF)
          (poolPrimary_good F hF) (idealSupport F J) (6-j)
  apply selectedPairGauss_fixed_ray (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) (poolPrimary_odd F hF)
  · intro i
    exact (primaryPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2
  · exact idealSupport_disjoint_of_coprime F I J hIJ
  · rw [admissiblePoolProduct_span F hF I hIF]
    exact admissible_supported (hF I hIF)
  · rw [admissiblePoolProduct_span F hF J hJF]
    exact admissible_supported (hF J hJF)
  · simpa only [← primaryGenerator_eq_poolProduct F hF I hIF,
      ← primaryGenerator_eq_poolProduct F hF J hJF] using hmod
  · simpa only [← primaryGenerator_eq_poolProduct F hF J hJF] using hr
  · exact hj0
  · exact hj6

/-- Poisson for the five squarefree colour fibres. The row feature is the
literal j-th power, with its zero values retained. No power is taken of the
Gauss coefficient: its actual unary factors have exponents j and 6-j. -/
theorem admissible_pair_poisson (F : Finset (Ideal O))
    (hF : ∀ I ∈ F, Admissible I) (I J : Ideal O) (hIF : I ∈ F) (hJF : J ∈ F)
    (hIJ : IsCoprime I J)
    (hmod : primaryGenerator I - primaryGenerator J ∈ (Ideal.span {(36 : O)} : Ideal O))
    (r : EisensteinEPrimaryPhase.Coord) (hr : residue (primaryGenerator J) = r)
    (j : ℕ) (hj0 : 0 < j) (hj6 : j < 6)
    (W : SchwartzMap ℝ ℂ) (L : ℝ) (hL : 0 < L) :
    (∑' z : O, (idealRowHom z I * star (idealRowHom z J)) ^ j *
      W (‖eisEmbedding z‖ ^ 2 / L)) =
    ((L : ℂ) / (Real.sqrt ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ)) : ℂ) *
      quadraticRayPair r r ^ j * admissibleUnaryGauss F hF I j *
        admissibleUnaryGauss F hF J (6-j)) *
      ∑' h : O, star ((idealRowHom h I * star (idealRowHom h J)) ^ j) *
        paperRadialFourier W
          (L * ‖eisEmbedding h‖ ^ 2 / ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ))) := by
  let := admissiblePoolMaximal F hF
  let S := idealSupport F I
  let T := idealSupport F J
  let P := fun i : (S ∪ T : Finset (primePool F)) => Ideal.span {poolPrimary F i.val}
  have hcop := selectedPrimeCoprime (poolPrimary F) (poolPrimary_coprime F hF) (S ∪ T)
  have hrow (n : O) : finiteSexticRow P (fun i => poolPrimary_good F hF i.val)
      (fun i => if i.val ∈ T then 6-j else j) n =
      (idealRowHom n I * star (idealRowHom n J)) ^ j := by
    have hh := selectedPairRow_actual (poolPrimary F) (poolPrimary_coprime F hF)
      (poolPrimary_good F hF) S T (idealSupport_disjoint_of_coprime F I J hIJ) j hj0 hj6 n
    rw [show S = idealSupport F I from rfl, show T = idealSupport F J from rfl,
      admissiblePoolProduct_span F hF I hIF, admissiblePoolProduct_span F hF J hJF] at hh
    simpa only [primitivePair] using hh
  have hh := canonical_radial_poisson_normalized P hcop
    (fun i => poolPrimary_good F hF i.val) (fun i => poolPrimary_odd F hF i.val)
    (fun i => if i.val ∈ T then 6-j else j)
    (fun i => by split_ifs <;> omega) (fun i => by split_ifs <;> omega) W L hL
  change (∑' z : O, finiteSexticRow P _ _ z * _) =
    ((L : ℂ) * admissiblePairGauss F hF I J j /
      (‖eisEmbedding (admissiblePairConductor F I J)‖ : ℂ)) *
      ∑' h : O, star (finiteSexticRow P _ _ h) *
        paperRadialFourier W (L * ‖eisEmbedding h‖ ^ 2 /
          ‖eisEmbedding (admissiblePairConductor F I J)‖ ^ 2) at hh
  simp_rw [hrow] at hh
  rw [admissiblePairConductor_norm_sq F hF I J hIF hJF hIJ,
    admissiblePairConductor_norm F hF I J hIF hJF hIJ,
    admissiblePairGauss_fixed_ray F hF I J hIF hJF hIJ hmod r hr j hj0 hj6] at hh
  rw [hh]
  ring

end
end Qrh.JointDetector.PowerPairGauss

#print axioms Qrh.JointDetector.PowerPairGauss.canonical_pair_gauss_fixed_ray
#print axioms Qrh.JointDetector.PowerPairGauss.finite_pair_row_actual
#print axioms Qrh.JointDetector.PowerPairGauss.selectedPairGauss_fixed_ray
#print axioms Qrh.JointDetector.PowerPairGauss.admissible_pair_poisson
