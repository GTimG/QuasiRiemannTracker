/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.FiveColourNorm
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol

/-!
# Actual mixed-colour Gauss packets

The prime exponent is allowed to vary arbitrarily in {1,...,5}. The free left
and right colour-one pivots are separated from all remaining prime states.
The canonical modulus-unit correction is retained literally until its actual
whole-row ray condition is used. No packet identity or norm is postulated.
-/
namespace Qrh.JointDetector.FiveColourPoisson
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge GaussGeneratorTransport FiniteGaussPhase
open MixedCrossSeparation MixedGaussConversion EisensteinSchwartzPoisson
open QuadraticAllOddCRT
local notation "O" => ActualEisensteinCubic.O

section ProductBookkeeping
variable {ι : Type*} [DecidableEq ι]

def orderedBlock (x : ι → ι → ℂ) (localValue : ι → ℂ) (e : ι → ℕ) (A : Finset ι) : ℂ :=
  ∏ i ∈ A, (∏ k ∈ A.erase i, x i k^(e i))*localValue i

def crossBlock (x : ι → ι → ℂ) (e : ι → ℕ) (A B : Finset ι) : ℂ :=
  ∏ i ∈ A, ∏ k ∈ B, x i k^(e i)*x k i^(e k)

/-- Exact CRT product bookkeeping with VARYING prime exponents. -/
theorem orderedBlock_union (x : ι → ι → ℂ) (localValue : ι → ℂ) (e : ι → ℕ)
    (A B : Finset ι) (hd : Disjoint A B) :
    orderedBlock x localValue e (A ∪ B) =
      orderedBlock x localValue e A*orderedBlock x localValue e B*crossBlock x e A B := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ (A ∪ B).erase i, x i k^(e i)) =
        (∏ k ∈ A.erase i, x i k^(e i))*(∏ k ∈ B, x i k^(e i)) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : (A ∪ B).erase i = A.erase i ∪ B := by
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he,Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ (A ∪ B).erase i, x i k^(e i)) =
        (∏ k ∈ B.erase i, x i k^(e i))*(∏ k ∈ A, x i k^(e i)) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : (A ∪ B).erase i = B.erase i ∪ A := by
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk,or_comm]
    rw [he,Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, (∏ k ∈ (A ∪ B).erase i, x i k^(e i))*localValue i) =
      orderedBlock x localValue e A*(∏ i ∈ A, ∏ k ∈ B, x i k^(e i)) := by
    rw [orderedBlock,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, (∏ k ∈ (A ∪ B).erase i, x i k^(e i))*localValue i) =
      orderedBlock x localValue e B*(∏ i ∈ B, ∏ k ∈ A, x i k^(e i)) := by
    rw [orderedBlock,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  unfold orderedBlock at ⊢
  rw [Finset.prod_union hd,hpA,hpB]
  rw [Finset.prod_comm (s := B) (t := A)]
  simp only [orderedBlock,crossBlock,Finset.prod_mul_distrib]
  ring

theorem crossBlock_union_right (x : ι → ι → ℂ) (e : ι → ℕ) (A B C : Finset ι)
    (hBC : Disjoint B C) :
    crossBlock x e A (B ∪ C) = crossBlock x e A B*crossBlock x e A C := by
  unfold crossBlock
  simp_rw [Finset.prod_union hBC]
  rw [Finset.prod_mul_distrib]

theorem orderedBlock_three (x : ι → ι → ℂ) (localValue : ι → ℂ) (e : ι → ℕ)
    (A B C : Finset ι) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) :
    orderedBlock x localValue e (A ∪ (B ∪ C)) =
      orderedBlock x localValue e A*orderedBlock x localValue e B*orderedBlock x localValue e C*
        crossBlock x e A B*crossBlock x e A C*crossBlock x e B C := by
  rw [orderedBlock_union x localValue e A (B ∪ C) (Finset.disjoint_union_right.mpr ⟨hAB,hAC⟩),
    orderedBlock_union x localValue e B C hBC,crossBlock_union_right x e A B C hBC]
  ring
end ProductBookkeeping

/-- A variable-exponent unary block. Shared off-diagonal table primes may
have any of the five primitive exponents, including three. -/
def varyingUnaryGauss {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (e : ι → ℕ) (A : Finset ι) : ℂ :=
  orderedBlock (crossSymbol p hg) (fun i => localGauss (p i) (hp i) (hg i) (e i)) e A

/-- The actual canonical product Gauss coefficient, separated into the two
free pivot blocks and all remaining primitive prime states. -/
theorem canonicalProductGauss_three {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (e : ι → ℕ) (he : ∀ i, e i ≠ 0)
    (A B C : Finset ι) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : A ∪ (B ∪ C) = Finset.univ) :
    canonicalProductGauss p hp hcop hg e =
      varyingUnaryGauss p hp hg e A*varyingUnaryGauss p hp hg e B*varyingUnaryGauss p hp hg e C*
        crossBlock (crossSymbol p hg) e A B*crossBlock (crossSymbol p hg) e A C*
        crossBlock (crossSymbol p hg) e B C := by
  rw [canonicalProductGauss_cross_factors]
  have hpow (i k : ι) :
      (canonicalSextic (Ideal.span {p i}) (hg i)^e i) (Ideal.Quotient.mk (Ideal.span {p i}) (p k)) =
        crossSymbol p hg i k^(e i) := MulChar.pow_apply' _ (he i) _
  simp_rw [hpow]
  change (∏ i, ∏ k ∈ Finset.univ.erase i, crossSymbol p hg i k^(e i))*
    (∏ i, localGauss (p i) (hp i) (hg i) (e i)) = _
  rw [← Finset.prod_mul_distrib]
  change orderedBlock (crossSymbol p hg) (fun i => localGauss (p i) (hp i) (hg i) (e i)) e Finset.univ = _
  rw [← hcover,orderedBlock_three _ _ _ A B C hAB hAC hBC]
  rfl

/-- Literal mixed-colour Poisson, still retaining the canonical unit factor.
Every ordinary frequency and the full pair-dependent radial kernel remain.
The only exponent restrictions are pointwise 1≤e(p)≤5. -/
theorem mixed_radial_poisson_three {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O⧸Ideal.span {p i}) ≠ 2)
    (e : ι → ℕ) (he0 : ∀ i, e i ≠ 0) (he6 : ∀ i, e i < 6)
    (A B C : Finset ι) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : A ∪ (B ∪ C) = Finset.univ)
    (W : 𝓢(ℝ,ℂ)) (L : ℝ) (hL : 0 < L) :
    (∑' z : O, finiteSexticRow (fun i => Ideal.span {p i}) hg e z*W (‖eisEmbedding z‖^2/L)) =
      ((L : ℂ)*
        (finiteSexticRow (fun i => Ideal.span {p i}) hg e (modulusUnit p : O)*
          (varyingUnaryGauss p hp hg e A*varyingUnaryGauss p hp hg e B*varyingUnaryGauss p hp hg e C*
            crossBlock (crossSymbol p hg) e A B*crossBlock (crossSymbol p hg) e A C*
            crossBlock (crossSymbol p hg) e B C))/
        (‖eisEmbedding (finitePrimeModulus (fun i => Ideal.span {p i}))‖ : ℂ))*
      ∑' h : O, star (finiteSexticRow (fun i => Ideal.span {p i}) hg e h)*
        paperRadialFourier W (L*‖eisEmbedding h‖^2/
          ‖eisEmbedding (finitePrimeModulus (fun i => Ideal.span {p i}))‖^2) := by
  rw [canonical_radial_poisson_normalized (fun i => Ideal.span {p i}) hcop hg hchar e he0 he6 W L hL,
    canonicalNormalizedGauss_eq_product p hp hcop hg e,
    canonicalProductGauss_three p hp hcop hg e he0 A B C hAB hAC hBC hcover]

/-- All local differences are modulo SIX, with the exponent-three case
retained and same-colour cancellation keeping its original zero mask. -/
def quotientExponent (j k : ℕ) : ℕ := (j+6-k)%6

theorem quotientExponent_range {j k : ℕ} (hj : j < 6) (hk : k < 6) (hne : j ≠ k) :
    0 < quotientExponent j k ∧ quotientExponent j k < 6 := by
  unfold quotientExponent
  omega

theorem sixth_root_star (q : ℂ) (hq : q^6 = 1) : star q = q^5 := by
  have hq0 : q ≠ 0 := by intro he; simpa [he] using hq
  have hn : ‖q‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hq (by decide)
  have hs : q*star q = 1 := by simpa only [Complex.star_def,Complex.mul_conj',hn,Complex.ofReal_one,one_pow] using Complex.mul_conj' q
  apply mul_left_cancel₀ hq0
  rw [hs,← pow_succ']
  exact hq.symm

theorem zero_or_sixth_quotient (q : ℂ) (hq : q = 0 ∨ q^6 = 1)
    (j k : ℕ) (hj : j < 6) (hk : k < 6) (hactive : 0 < j+k) :
    q^j*star (q^k) =
      if j=k then (if q=0 then 0 else 1) else q^(quotientExponent j k) := by
  rcases hq with hq | hq
  · subst q
    by_cases hjk : j=k
    · have hk0 : k ≠ 0 := by omega
      simp [hjk,hk0]
    · have he0 := (quotientExponent_range hj hk hjk).1.ne'
      by_cases hj0 : j=0
      · have hk0 : k ≠ 0 := by omega
        subst j
        simp [hk0,he0]
      · simp [hjk,hj0,he0]
  · have hq0 : q ≠ 0 := by intro he; simpa [he] using hq
    rw [star_pow,sixth_root_star q hq,← pow_mul,← pow_add]
    by_cases hjk : j=k
    · rw [if_pos hjk,if_neg hq0]
      subst j
      rw [show k+5*k = 6*k by omega,pow_mul,hq,one_pow]
    · rw [if_neg hjk]
      apply pow_eq_pow_of_modEq _ hq
      unfold quotientExponent
      change (j+5*k)%6 = ((j+6-k)%6)%6
      omega

/-- The literal prime-row quotient. A cancelled prime remains a principal
Euler-hole mask, not an unconditionally deleted local factor. -/
theorem local_natural_quotient (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (j k : ℕ) (hj : j < 6) (hk : k < 6) (hactive : 0 < j+k) (n : O) :
    (canonicalSextic P hg (Ideal.Quotient.mk P n))^j*
      star ((canonicalSextic P hg (Ideal.Quotient.mk P n))^k) =
      if j=k then (if n ∈ P then 0 else 1) else
        (canonicalSextic P hg (Ideal.Quotient.mk P n))^(quotientExponent j k) := by
  let q := canonicalSextic P hg (Ideal.Quotient.mk P n)
  have hsix : q^6 = if n ∈ P then 0 else 1 := by
    simpa only [q,map_pow] using canonicalSextic_sixth_power_mask P hg n
  have hzero : q=0 ↔ n ∈ P := by
    constructor
    · intro hz
      by_contra hn
      have hbad : (0 : ℂ) = 1 := by
        simpa only [hz,zero_pow (by decide : (6 : ℕ) ≠ 0),ite_eq_right hn] using hsix
      exact zero_ne_one hbad
    · intro hn
      exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp (by simpa only [ite_eq_left hn] using hsix)
  have hroot : q=0 ∨ q^6=1 := by
    by_cases hn : n ∈ P
    · exact Or.inl (hzero.mpr hn)
    · exact Or.inr (by simpa only [ite_eq_right hn] using hsix)
  simpa only [hzero] using zero_or_sixth_quotient q hroot j k hj hk hactive

/-- Actual natural pair over a fixed finite prime pool. Zero means absence
of that prime on that side; positive exponents are the five natural colours. -/
def naturalColourPairRow {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i)
    (left right : ι → ℕ) (n : O) : ℂ :=
  ∏ i, (canonicalSextic (P i) (hg i) (Ideal.Quotient.mk (P i) n))^(left i)*
    star ((canonicalSextic (P i) (hg i) (Ideal.Quotient.mk (P i) n))^(right i))

/-- Full finite primitive quotient and puncture identity, including all
25 shared-colour states and unshared primes on either side. -/
theorem naturalColourPairRow_primitive_puncture {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i)
    (left right : ι → ℕ) (hl : ∀ i, left i < 6) (hr : ∀ i, right i < 6)
    (hactive : ∀ i, 0 < left i+right i) (n : O) :
    naturalColourPairRow P hg left right n =
      (∏ i ∈ Finset.univ.filter (fun i => left i ≠ right i),
        (canonicalSextic (P i) (hg i) (Ideal.Quotient.mk (P i) n))^
          (quotientExponent (left i) (right i)))*
      (∏ i ∈ Finset.univ.filter (fun i => left i = right i), if n ∈ P i then (0 : ℂ) else 1) := by
  unfold naturalColourPairRow
  simp_rw [local_natural_quotient _ _ _ _ (hl _) (hr _) (hactive _)]
  rw [← Finset.prod_filter_mul_prod_filter_not (s := Finset.univ) (p := fun i => left i = right i)]
  simp only [Finset.prod_filter]
  rw [mul_comm]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> simp_all
  · apply Finset.prod_congr rfl
    intro i hi
    split_ifs <;> simp_all

def primitiveSupport {ι : Type*} [Fintype ι] (left right : ι → ℕ) : Finset ι :=
  Finset.univ.filter (fun i => left i ≠ right i)

def punctureSupport {ι : Type*} [Fintype ι] (left right : ι → ℕ) : Finset ι :=
  Finset.univ.filter (fun i => left i = right i)

theorem prod_puncture_mask {ι : Type*} (P : ι → Ideal O) (S : Finset ι) (n : O) :
    (∏ i ∈ S, if n ∈ P i then (0 : ℂ) else 1) = rowCoprimeMask P S n := by
  unfold rowCoprimeMask
  split_ifs with h
  · obtain ⟨i,hi,hn⟩ := h
    exact Finset.prod_eq_zero hi (by rw [ite_eq_left hn])
  · apply Finset.prod_eq_one
    intro i hi
    exact ite_eq_right (fun hn => h ⟨i,hi,hn⟩)

/-- The original natural pair is its primitive quotient times the cancelled
same-colour principal mask. This identity includes every shared state. -/
theorem naturalColourPairRow_eq_mask_primitive {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i)
    (left right : ι → ℕ) (hl : ∀ i, left i < 6) (hr : ∀ i, right i < 6)
    (hactive : ∀ i, 0 < left i+right i) (n : O) :
    naturalColourPairRow P hg left right n =
      rowCoprimeMask P (punctureSupport left right) n*
        finiteSexticRow (fun i : primitiveSupport left right => P i.val) (fun i => hg i.val)
          (fun i => quotientExponent (left i.val) (right i.val)) n := by
  rw [naturalColourPairRow_primitive_puncture P hg left right hl hr hactive n,prod_puncture_mask,mul_comm]
  congr 1
  unfold finiteSexticRow
  have hp (i : primitiveSupport left right) :
      (canonicalSextic (P i.val) (hg i.val)^quotientExponent (left i.val) (right i.val))
        (Ideal.Quotient.mk (P i.val) n) =
      (canonicalSextic (P i.val) (hg i.val) (Ideal.Quotient.mk (P i.val) n))^
        quotientExponent (left i.val) (right i.val) :=
    MulChar.pow_apply' _ (quotientExponent_range (hl i.val) (hr i.val) (Finset.mem_filter.mp i.property).2).1.ne' _
  simp_rw [hp]
  exact (Finset.prod_coe_sort (primitiveSupport left right) _).symm

/-- Exact actual Poisson identity for the ENTIRE mixed-colour natural pair.
The twenty-five shared states are represented by the literal pair
(left(p),right(p)); equal colours produce the retained divisor-labelled
puncture, unequal colours produce their true exponent modulo six.

The canonical modulus unit is removed by the existing exact WHOLE-frequency
radial transport, not by assuming a ray factor is one. -/
theorem natural_colour_pair_poisson {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => (Ideal.span {p i} : Ideal O)))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O⧸Ideal.span {p i}) ≠ 2)
    (left right : ι → ℕ) (hl : ∀ i, left i < 6) (hr : ∀ i, right i < 6)
    (hactive : ∀ i, 0 < left i+right i)
    (W : 𝓢(ℝ,ℂ)) (L : ℝ) (hL : 0 < L) :
    let S := primitiveSupport left right
    let P := fun i : S => (Ideal.span {p i.val} : Ideal O)
    let e := fun i : S => quotientExponent (left i.val) (right i.val)
    let hS := fun i : S => hg i.val
    let hcopS : Pairwise (Function.onFun IsCoprime P) :=
      fun i j hij => hcop (fun he => hij (Subtype.ext he))
    (∑' z : O, naturalColourPairRow (fun i => Ideal.span {p i}) hg left right z*
      W (‖eisEmbedding z‖^2/L)) =
      ((L : ℂ)*canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val) hcopS hS e/
        (‖eisEmbedding (∏ i : S, p i.val)‖ : ℂ))*
      ∑ E ∈ (punctureSupport left right).powerset,
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ)*
          finiteSexticRow P hS e d/(‖eisEmbedding d‖^2 : ℝ))*
        ∑' h : O, star (finiteSexticRow P hS e h)*
          paperRadialFourier W (L*‖eisEmbedding h‖^2/
            (‖eisEmbedding d‖^2*‖eisEmbedding (∏ i : S, p i.val)‖^2)) := by
  dsimp only
  simp_rw [naturalColourPairRow_eq_mask_primitive (fun i => Ideal.span {p i}) hg left right hl hr hactive]
  exact canonical_masked_radial_poisson_product (fun i => Ideal.span {p i}) hinj (punctureSupport left right)
    (fun i : primitiveSupport left right => p i.val) (fun i => hp i.val)
    (fun i j hij => hcop (fun he => hij (Subtype.ext he)))
    (fun i => hg i.val) (fun i => hchar i.val)
    (fun i => quotientExponent (left i.val) (right i.val))
    (fun i => (quotientExponent_range (hl i.val) (hr i.val) (Finset.mem_filter.mp i.property).2).1.ne')
    (fun i => (quotientExponent_range (hl i.val) (hr i.val) (Finset.mem_filter.mp i.property).2).2) W L hL

/-- Binding to the ORIGINAL ideal-row quotient, with all repeated prime
powers and all natural zeros retained. -/
theorem naturalColourPairRow_eq_idealRowHom {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i)
    (left right : ι → ℕ) (n : O) :
    naturalColourPairRow P hg left right n =
      idealRowHom n (∏ i, (P i)^(left i))*star (idealRowHom n (∏ i, (P i)^(right i))) := by
  rw [map_prod,map_prod,star_prod,← Finset.prod_mul_distrib]
  unfold naturalColourPairRow
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_pow,map_pow,idealRowHom_prime n (P i) (hg i)]

/-- Exact local free-left pivot identity, including zero values off the
original coprime domain. -/
theorem free_left_cross (x y : ℂ) (hy : y=0 ∨ y^6=1)
    (k : ℕ) (hk : 2 ≤ k) (hk6 : k < 6) :
    x*y^(6-k) = star (y^(k-1))*(x*y^5) := by
  rcases hy with hy | hy
  · subst y
    simp [show 6-k ≠ 0 by omega,show k-1 ≠ 0 by omega]
  · calc
      _ = x*y^(5*(k-1)+5) := by
        congr 1
        apply pow_eq_pow_of_modEq _ hy
        change (6-k)%6 = (5*(k-1)+5)%6
        omega
      _ = (y^5)^(k-1)*(x*y^5) := by rw [pow_add,pow_mul]; ring
      _ = _ := by rw [star_pow,sixth_root_star y hy]

/-- Right-pivot power five uses the same actual higher-row orientation. -/
theorem free_right_cross (x y : ℂ) (j : ℕ) (hj : 1 ≤ j) :
    x^5*y^j = y^(j-1)*(x^5*y) := by
  conv_lhs => rw [show j = (j-1)+1 by omega,pow_add,pow_one]
  ring

theorem pivot_left_cross_actual {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι)
    (hpi : lambda^2 ∣ p i-1) (hpk : lambda^2 ∣ p k-1)
    (colour : ℕ) (hc : 2 ≤ colour) (hc6 : colour < 6) :
    crossSymbol p hg i k*crossSymbol p hg k i^(6-colour) =
      star (crossSymbol p hg k i^(colour-1))*
        (crossSymbol p hg i k^3*crossSymbol p hg k i^3) := by
  have hsix : crossSymbol p hg k i^6 = if p i ∈ Ideal.span {p k} then 0 else 1 := by
    simpa only [crossSymbol,map_pow] using canonicalSextic_sixth_power_mask (Ideal.span {p k}) (hg k) (p i)
  have hy : crossSymbol p hg k i=0 ∨ crossSymbol p hg k i^6=1 := by
    by_cases h : p i ∈ Ideal.span {p k}
    · left
      exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp (by simpa only [ite_eq_left h] using hsix)
    · right
      simpa only [ite_eq_right h] using hsix
  rw [free_left_cross _ _ hy colour hc hc6]
  congr 1
  simpa only [mul_comm] using mixed_cross_eq_quadratic p hg k i hpk hpi

theorem pivot_right_cross_actual {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι)
    (hpi : lambda^2 ∣ p i-1) (hpk : lambda^2 ∣ p k-1)
    (colour : ℕ) (hc : 1 ≤ colour) :
    crossSymbol p hg i k^5*crossSymbol p hg k i^colour =
      crossSymbol p hg k i^(colour-1)*(crossSymbol p hg i k^3*crossSymbol p hg k i^3) := by
  rw [free_right_cross _ _ colour hc,mixed_cross_eq_quadratic p hg i k hpi hpk]

/-- The exact higher-character value appearing in the pivot dual vector. -/
def oppositeCrossSymbol {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) : ℂ :=
  ∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg k i

/-- The actual Gauss cross-block for free colour one against an opposite
higher colour. Its only extra factor is the original quadratic ray pair. -/
theorem pivot_left_crossBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hprimary : ∀ i, lambda^2 ∣ p i-1)
    (e : ι → ℕ) (A B : Finset ι) (colour : ℕ) (hc : 2 ≤ colour) (hc6 : colour < 6)
    (heA : ∀ i ∈ A, e i=1) (heB : ∀ k ∈ B, e k=6-colour) :
    crossBlock (crossSymbol p hg) e A B =
      star ((oppositeCrossSymbol p hg A B)^(colour-1))*quadraticCrossPhase p hg A B := by
  simp only [crossBlock,oppositeCrossSymbol,quadraticCrossPhase,star_prod,star_pow]
  rw [← Finset.prod_pow]
  simp_rw [← Finset.prod_pow]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  rw [heA i hi,heB k hk,pow_one]
  simpa only [star_pow] using pivot_left_cross_actual p hg i k (hprimary i) (hprimary k) colour hc hc6

theorem oppositeCrossSymbol_eq_idealRowHom {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) :
    oppositeCrossSymbol p hg A B = idealRowHom (∏ i ∈ A, p i) (∏ k ∈ B, Ideal.span {p k}) := by
  unfold oppositeCrossSymbol
  rw [map_prod,Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro k hk
  rw [idealRowHom_prime _ _ (hg k)]
  simp only [map_prod,crossSymbol]

/-- The left-pivot Gauss interaction is the ORIGINAL phase entering the
arbitrary dual vector in FiveColourNorm, times one fixed ray factor. -/
theorem pivot_left_crossBlock_fixed_ray {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O⧸Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda^2 ∣ p i-1)
    (e : ι → ℕ) (A B : Finset ι) (hd : Disjoint A B)
    (colour : ℕ) (hc : 2 ≤ colour) (hc6 : colour < 6)
    (heA : ∀ i ∈ A, e i=1) (heB : ∀ k ∈ B, e k=6-colour)
    (rA rB : EisensteinEPrimaryPhase.Coord)
    (hrA : residue (∏ i ∈ A, p i)=rA) (hrB : residue (∏ k ∈ B, p k)=rB) :
    crossBlock (crossSymbol p hg) e A B =
      star ((idealRowHom (∏ i ∈ A, p i) (∏ k ∈ B, Ideal.span {p k}))^(colour-1))*
        quadraticRayPair rA rB := by
  rw [pivot_left_crossBlock p hg hprimary e A B colour hc hc6 heA heB,
    oppositeCrossSymbol_eq_idealRowHom,
    quadraticCrossPhase_eq_rayPair p hp hcop hg hchar A B hd,hrA,hrB]

theorem pivot_right_crossBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hprimary : ∀ i, lambda^2 ∣ p i-1)
    (e : ι → ℕ) (A B : Finset ι) (colour : ℕ) (hc : 1 ≤ colour)
    (heA : ∀ i ∈ A, e i=5) (heB : ∀ k ∈ B, e k=colour) :
    crossBlock (crossSymbol p hg) e A B =
      (oppositeCrossSymbol p hg A B)^(colour-1)*quadraticCrossPhase p hg A B := by
  simp only [crossBlock,oppositeCrossSymbol,quadraticCrossPhase]
  rw [← Finset.prod_pow]
  simp_rw [← Finset.prod_pow]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  rw [heA i hi,heB k hk]
  exact pivot_right_cross_actual p hg i k (hprimary i) (hprimary k) colour hc

theorem pivot_right_crossBlock_fixed_ray {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O⧸Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda^2 ∣ p i-1)
    (e : ι → ℕ) (A B : Finset ι) (hd : Disjoint A B)
    (colour : ℕ) (hc : 1 ≤ colour)
    (heA : ∀ i ∈ A, e i=5) (heB : ∀ k ∈ B, e k=colour)
    (rA rB : EisensteinEPrimaryPhase.Coord)
    (hrA : residue (∏ i ∈ A, p i)=rA) (hrB : residue (∏ k ∈ B, p k)=rB) :
    crossBlock (crossSymbol p hg) e A B =
      (idealRowHom (∏ i ∈ A, p i) (∏ k ∈ B, Ideal.span {p k}))^(colour-1)*quadraticRayPair rA rB := by
  rw [pivot_right_crossBlock p hg hprimary e A B colour hc heA heB,
    oppositeCrossSymbol_eq_idealRowHom,
    quadraticCrossPhase_eq_rayPair p hp hcop hg hchar A B hd,hrA,hrB]

def higherCrossPhase {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (colour : ι → ℕ) : ℂ :=
  ∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg k i^(colour k-1)

/-- Simultaneous four-colour interaction, without replacing any colour by
a uniform exponent or deleting its exponent-three natural zeros. -/
theorem pivot_left_all_higher {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hprimary : ∀ i, lambda^2 ∣ p i-1)
    (e colour : ι → ℕ) (A B : Finset ι)
    (hc : ∀ k ∈ B, 2 ≤ colour k ∧ colour k < 6)
    (heA : ∀ i ∈ A, e i=1) (heB : ∀ k ∈ B, e k=6-colour k) :
    crossBlock (crossSymbol p hg) e A B =
      star (higherCrossPhase p hg A B colour)*quadraticCrossPhase p hg A B := by
  simp only [crossBlock,higherCrossPhase,quadraticCrossPhase,star_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  rw [heA i hi,heB k hk,pow_one]
  exact pivot_left_cross_actual p hg i k (hprimary i) (hprimary k) (colour k) (hc k hk).1 (hc k hk).2

theorem pivot_right_all_higher {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hprimary : ∀ i, lambda^2 ∣ p i-1)
    (e colour : ι → ℕ) (A B : Finset ι)
    (hc : ∀ k ∈ B, 1 ≤ colour k)
    (heA : ∀ i ∈ A, e i=5) (heB : ∀ k ∈ B, e k=colour k) :
    crossBlock (crossSymbol p hg) e A B =
      higherCrossPhase p hg A B colour*quadraticCrossPhase p hg A B := by
  simp only [crossBlock,higherCrossPhase,quadraticCrossPhase]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  rw [heA i hi,heB k hk]
  exact pivot_right_cross_actual p hg i k (hprimary i) (hprimary k) (colour k) (hc k hk)

theorem crossSymbol_norm_le {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) : ‖crossSymbol p hg i k‖ ≤ 1 := by
  change ‖canonicalSextic (Ideal.span {p i}) (hg i) (Ideal.Quotient.mk (Ideal.span {p i}) (p k))‖ ≤ 1
  rw [← idealRowHom_prime (p k) (Ideal.span {p i}) (hg i)]
  exact idealRowHom_norm _ _

theorem crossBlock_norm_le {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (e : ι → ℕ) (A B : Finset ι) :
    ‖crossBlock (crossSymbol p hg) e A B‖ ≤ 1 := by
  simp only [crossBlock,norm_prod,norm_mul,norm_pow]
  apply Finset.prod_le_one₀ (by intro i hi; positivity)
  intro i hi
  apply Finset.prod_le_one₀ (by intro k hk; positivity)
  intro k hk
  exact (mul_le_mul (pow_le_one₀ (norm_nonneg _) (crossSymbol_norm_le p hg i k))
    (pow_le_one₀ (norm_nonneg _) (crossSymbol_norm_le p hg k i)) (by positivity) zero_le_one).trans_eq (one_mul 1)

theorem varyingUnaryGauss_norm_le {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O⧸Ideal.span {p i}) ≠ 2)
    (e : ι → ℕ) (he0 : ∀ i, e i ≠ 0) (he6 : ∀ i, e i < 6) (A : Finset ι) :
    ‖varyingUnaryGauss p hp hg e A‖ ≤ 1 := by
  simp only [varyingUnaryGauss,orderedBlock,norm_prod,norm_mul]
  apply Finset.prod_le_one₀ (by intro i hi; positivity)
  intro i hi
  rw [norm_localGauss (p i) (hp i) (hg i) (hchar i) (e i) (he0 i) (he6 i),mul_one]
  apply Finset.prod_le_one₀ (by intro k hk; positivity)
  intro k hk
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (crossSymbol_norm_le p hg i k)

/-- Whole mixed Gauss separation after fixing one shared table. `T` contains
all fixed shared-prime states; its arbitrary nonzero exponents stay literal.
The factors before the final two cross phases are unary left, unary right,
and a higher-tuple kernel. Their dependence is exactly that needed by swap.
-/
theorem canonicalProductGauss_pivot_swap {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hprimary : ∀ i, lambda^2 ∣ p i-1)
    (e cL cR : ι → ℕ) (he0 : ∀ i, e i ≠ 0)
    (A B CL CR T : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A (CL ∪ (CR ∪ T)))
    (hBC : Disjoint B (CL ∪ (CR ∪ T))) (hcover : A ∪ (B ∪ (CL ∪ (CR ∪ T)))=Finset.univ)
    (hLR : Disjoint CL CR) (hLT : Disjoint CL T) (hRT : Disjoint CR T)
    (hA : ∀ i ∈ A, e i=1) (hB : ∀ i ∈ B, e i=5)
    (hCL : ∀ i ∈ CL, e i=cL i) (hCR : ∀ i ∈ CR, e i=6-cR i)
    (hcL : ∀ i ∈ CL, 1 ≤ cL i) (hcR : ∀ i ∈ CR, 2 ≤ cR i ∧ cR i < 6) :
    canonicalProductGauss p hp hcop hg e =
      (varyingUnaryGauss p hp hg e A*crossBlock (crossSymbol p hg) e A CL*crossBlock (crossSymbol p hg) e A T)*
      (varyingUnaryGauss p hp hg e B*crossBlock (crossSymbol p hg) e B CR*crossBlock (crossSymbol p hg) e B T)*
      (varyingUnaryGauss p hp hg e (CL ∪ (CR ∪ T))*crossBlock (crossSymbol p hg) e A B*
        quadraticCrossPhase p hg A CR*quadraticCrossPhase p hg B CL)*
      star (higherCrossPhase p hg A CR cR)*higherCrossPhase p hg B CL cL := by
  rw [canonicalProductGauss_three p hp hcop hg e he0 A B (CL ∪ (CR ∪ T)) hAB hAC hBC hcover]
  rw [crossBlock_union_right _ _ A CL (CR ∪ T) (Finset.disjoint_union_right.mpr ⟨hLR,hLT⟩),
    crossBlock_union_right _ _ A CR T hRT,
    crossBlock_union_right _ _ B CL (CR ∪ T) (Finset.disjoint_union_right.mpr ⟨hLR,hLT⟩),
    crossBlock_union_right _ _ B CR T hRT,
    pivot_left_all_higher p hg hprimary e cR A CR hcR hA hCR,
    pivot_right_all_higher p hg hprimary e cL B CL hcL hB hCL]
  ring

theorem pivot_pivot_crossBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (hprimary : ∀ i, lambda^2 ∣ p i-1)
    (e : ι → ℕ) (A B : Finset ι) (heA : ∀ i ∈ A, e i=1) (heB : ∀ k ∈ B, e k=5) :
    crossBlock (crossSymbol p hg) e A B = quadraticCrossPhase p hg A B := by
  unfold crossBlock quadraticCrossPhase
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k hk
  rw [heA i hi,heB k hk,pow_one]
  simpa only [mul_comm] using mixed_cross_eq_quadratic p hg k i (hprimary k) (hprimary i)

theorem quadraticCrossPhase_norm_le {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) :
    ‖quadraticCrossPhase p hg A B‖ ≤ 1 :=
  crossBlock_norm_le p hg (fun _ => 3) A B

/-- Complete fixed-ray separation of the ACTUAL mixed Gauss coefficient.
The middle factor depends only on higher tuples and the fixed shared table;
the first two factors enter arbitrary left/right vectors. No norm premise.
-/
theorem canonicalProductGauss_pivot_swap_fixed_ray {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O⧸Ideal.span {p i}) ≠ 2)
    (hprimary : ∀ i, lambda^2 ∣ p i-1)
    (e cL cR : ι → ℕ) (he0 : ∀ i, e i ≠ 0)
    (A B CL CR T : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A (CL ∪ (CR ∪ T)))
    (hBC : Disjoint B (CL ∪ (CR ∪ T))) (hcover : A ∪ (B ∪ (CL ∪ (CR ∪ T)))=Finset.univ)
    (hLR : Disjoint CL CR) (hLT : Disjoint CL T) (hRT : Disjoint CR T)
    (hA : ∀ i ∈ A, e i=1) (hB : ∀ i ∈ B, e i=5)
    (hCL : ∀ i ∈ CL, e i=cL i) (hCR : ∀ i ∈ CR, e i=6-cR i)
    (hcL : ∀ i ∈ CL, 1 ≤ cL i) (hcR : ∀ i ∈ CR, 2 ≤ cR i ∧ cR i < 6)
    (rA rB rCL rCR : EisensteinEPrimaryPhase.Coord)
    (hrA : residue (∏ i ∈ A, p i)=rA) (hrB : residue (∏ i ∈ B, p i)=rB)
    (hrCL : residue (∏ i ∈ CL, p i)=rCL) (hrCR : residue (∏ i ∈ CR, p i)=rCR) :
    canonicalProductGauss p hp hcop hg e =
      (varyingUnaryGauss p hp hg e A*crossBlock (crossSymbol p hg) e A CL*crossBlock (crossSymbol p hg) e A T)*
      (varyingUnaryGauss p hp hg e B*crossBlock (crossSymbol p hg) e B CR*crossBlock (crossSymbol p hg) e B T)*
      (varyingUnaryGauss p hp hg e (CL ∪ (CR ∪ T))*quadraticRayPair rA rB*
        quadraticRayPair rA rCR*quadraticRayPair rB rCL)*
      star (higherCrossPhase p hg A CR cR)*higherCrossPhase p hg B CL cL := by
  have hACR : Disjoint A CR := hAC.mono_right (by
    intro i hi; exact Finset.mem_union_right _ (Finset.mem_union_left _ hi))
  have hBCL : Disjoint B CL := hBC.mono_right Finset.subset_union_left
  rw [canonicalProductGauss_pivot_swap p hp hcop hg hprimary e cL cR he0 A B CL CR T
    hAB hAC hBC hcover hLR hLT hRT hA hB hCL hCR hcL hcR,
    pivot_pivot_crossBlock p hg hprimary e A B hA hB,
    quadraticCrossPhase_eq_rayPair p hp hcop hg hchar A B hAB,
    quadraticCrossPhase_eq_rayPair p hp hcop hg hchar A CR hACR,
    quadraticCrossPhase_eq_rayPair p hp hcop hg hchar B CL hBCL,hrA,hrB,hrCL,hrCR]

/-- Residual pivot rays need not agree after a shared-table quotient. Their
reciprocity phase is a COMMON bounded source weight, not an equality of rays. -/
def frozenReciprocityWeight (rL rR : EisensteinEPrimaryPhase.Coord) (H : Ideal O) : ℂ :=
  star ((quadraticRaySign rL (residue (primaryGenerator H)) : ℤ) : ℂ)*
    ((quadraticRaySign rR (residue (primaryGenerator H)) : ℤ) : ℂ)

theorem frozenReciprocityWeight_norm_le (rL rR : EisensteinEPrimaryPhase.Coord) (H : Ideal O) :
    ‖frozenReciprocityWeight rL rR H‖ ≤ 1 := by
  unfold frozenReciprocityWeight quadraticRaySign
  split_ifs <;> norm_num

/-- Actual ordinary-ideal reciprocity for possibly UNEQUAL frozen pivot rays.
The bad output multiplier b is never inserted into the ordinary source ideal. -/
theorem primitivePair_frozen_frequency_fixed_rays (I J H : Ideal O)
    (hI : Supported I) (hJ : Supported J) (hH : Supported H)
    (rL rR : EisensteinEPrimaryPhase.Coord)
    (hrL : residue (primaryGenerator I)=rL) (hrR : residue (primaryGenerator J)=rR) (b : O) :
    star (primitivePair I J (b*primaryGenerator H)) =
      star (idealRowHom b I)*idealRowHom b J*frozenReciprocityWeight rL rR H*
        star (idealRowHom (primaryGenerator I) H)*idealRowHom (primaryGenerator J) H := by
  rw [primitivePair_argument_mul,star_mul]
  unfold primitivePair
  rw [idealRow_orientation H I hH hI,idealRow_orientation H J hH hJ]
  simp only [star_mul,star_star,sexticReciprocityPhase,hrL,hrR,frozenReciprocityWeight]
  ring

def featureBlock {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i)
    (e : ι → ℕ) (A : Finset ι) (n : O) : ℂ :=
  ∏ i ∈ A, (canonicalSextic (P i) (hg i) (Ideal.Quotient.mk (P i) n))^(e i)

theorem featureBlock_eq_idealRowHom {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i)
    (e : ι → ℕ) (A : Finset ι) (n : O) :
    featureBlock P hg e A n = idealRowHom n (∏ i ∈ A, (P i)^(e i)) := by
  rw [map_prod]
  unfold featureBlock
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_pow,idealRowHom_prime n (P i) (hg i)]

theorem featureBlock_norm_le {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i)
    (e : ι → ℕ) (A : Finset ι) (n : O) : ‖featureBlock P hg e A n‖ ≤ 1 := by
  rw [featureBlock_eq_idealRowHom]
  exact idealRowHom_norm _ _

/-- Exact dual-feature separation: only the two free pivots enter the
squarefree operator. The higher primitive feature is one common source
weight after freezing the two higher tuples and the shared table. -/
theorem finiteSexticRow_pivot_factor {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i)
    (e : ι → ℕ) (he0 : ∀ i, e i ≠ 0) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : A ∪ (B ∪ C)=Finset.univ)
    (hA : ∀ i ∈ A, e i=1) (hB : ∀ i ∈ B, e i=5) (n : O) :
    finiteSexticRow P hg e n =
      primitivePair (∏ i ∈ A, P i) (∏ i ∈ B, P i) n*featureBlock P hg e C n := by
  have hleft : featureBlock P hg e A n = idealRowHom n (∏ i ∈ A, P i) := by
    rw [map_prod]
    unfold featureBlock
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi,pow_one,idealRowHom_prime n (P i) (hg i)]
  have hright : featureBlock P hg e B n = star (idealRowHom n (∏ i ∈ B, P i)) := by
    rw [map_prod,star_prod]
    unfold featureBlock
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi,idealRowHom_prime n (P i) (hg i)]
    simpa [quotientExponent] using
      (local_natural_quotient (P i) (hg i) 0 1 (by decide) (by decide) (by decide) n).symm
  have hfull : finiteSexticRow P hg e n = featureBlock P hg e A n*featureBlock P hg e B n*featureBlock P hg e C n := by
    unfold finiteSexticRow
    have hp (i : ι) : (canonicalSextic (P i) (hg i)^e i) (Ideal.Quotient.mk (P i) n) =
      (canonicalSextic (P i) (hg i) (Ideal.Quotient.mk (P i) n))^(e i) := MulChar.pow_apply' _ (he0 i) _
    simp_rw [hp]
    change (∏ i ∈ Finset.univ, (canonicalSextic (P i) (hg i) (Ideal.Quotient.mk (P i) n))^(e i)) = _
    rw [← hcover,Finset.prod_union (Finset.disjoint_union_right.mpr ⟨hAB,hAC⟩),Finset.prod_union hBC]
    change featureBlock P hg e A n*(featureBlock P hg e B n*featureBlock P hg e C n) = _
    ring
  rw [hfull,hleft,hright]
  rfl

/-- Both retained d and bad output b are kept in the literal higher weight.
Zeros at a shared prime contract this common weight; they are not deleted
from the pivot matrix by entrywise monotonicity. -/
def higherSourceWeight {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i)
    (e : ι → ℕ) (C : Finset ι) (d b : O) (H : Ideal O) : ℂ :=
  featureBlock P hg e C d*star (featureBlock P hg e C (b*primaryGenerator H))

theorem higherSourceWeight_norm_le {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i)
    (e : ι → ℕ) (C : Finset ι) (d b : O) (H : Ideal O) :
    ‖higherSourceWeight P hg e C d b H‖ ≤ 1 := by
  rw [higherSourceWeight,norm_mul,norm_star]
  exact (mul_le_mul (featureBlock_norm_le P hg e C d) (featureBlock_norm_le P hg e C _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- The ACTUAL mixed primitive dual term, in the exact separated operator
orientation for possibly unequal residual rays. All other colours, the source
puncture d and bad frequency multiplier b remain in displayed factors. -/
theorem mixed_dual_frequency_factor {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, lambda ∉ P i)
    (e : ι → ℕ) (he0 : ∀ i, e i ≠ 0) (A B C : Finset ι)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : A ∪ (B ∪ C)=Finset.univ) (hA : ∀ i ∈ A, e i=1) (hB : ∀ i ∈ B, e i=5)
    (hI : Supported (∏ i ∈ A, P i)) (hJ : Supported (∏ i ∈ B, P i))
    (H : Ideal O) (hH : Supported H) (rL rR : EisensteinEPrimaryPhase.Coord)
    (hrL : residue (primaryGenerator (∏ i ∈ A, P i))=rL)
    (hrR : residue (primaryGenerator (∏ i ∈ B, P i))=rR) (d b : O) :
    finiteSexticRow P hg e d*star (finiteSexticRow P hg e (b*primaryGenerator H)) =
      (idealRowHom d (∏ i ∈ A, P i)*star (idealRowHom b (∏ i ∈ A, P i)))*
      (star (idealRowHom d (∏ i ∈ B, P i))*idealRowHom b (∏ i ∈ B, P i))*
      (higherSourceWeight P hg e C d b H*frozenReciprocityWeight rL rR H)*
      star (idealRowHom (primaryGenerator (∏ i ∈ A, P i)) H)*
        idealRowHom (primaryGenerator (∏ i ∈ B, P i)) H := by
  rw [finiteSexticRow_pivot_factor P hg e he0 A B C hAB hAC hBC hcover hA hB,
    finiteSexticRow_pivot_factor P hg e he0 A B C hAB hAC hBC hcover hA hB,
    star_mul,primitivePair_frozen_frequency_fixed_rays _ _ H hI hJ hH rL rR hrL hrR b]
  unfold primitivePair higherSourceWeight
  ring

/-- The higher cross phase depends on the free pivot ONLY through its actual
row element. Its fixed higher-word ideal may be nonsquarefree and unbounded:
it is an arbitrary dual-vector multiplier, not a new operator source. -/
theorem higherCrossPhase_eq_idealRowHom {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (colour : ι → ℕ) :
    higherCrossPhase p hg A B colour =
      idealRowHom (∏ i ∈ A, p i) (∏ k ∈ B, (Ideal.span {p k})^(colour k-1)) := by
  unfold higherCrossPhase
  rw [map_prod,Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro k hk
  rw [map_pow,idealRowHom_prime _ _ (hg k)]
  simp only [map_prod]
  rw [Finset.prod_pow]
  rfl

theorem higherCrossPhase_norm_le {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (colour : ι → ℕ) :
    ‖higherCrossPhase p hg A B colour‖ ≤ 1 := by
  rw [higherCrossPhase_eq_idealRowHom]
  exact idealRowHom_norm _ _

end
end Qrh.JointDetector.FiveColourPoisson

#print axioms Qrh.JointDetector.FiveColourPoisson.canonicalProductGauss_three
#print axioms Qrh.JointDetector.FiveColourPoisson.mixed_radial_poisson_three

#print axioms Qrh.JointDetector.FiveColourPoisson.local_natural_quotient
#print axioms Qrh.JointDetector.FiveColourPoisson.naturalColourPairRow_primitive_puncture

#print axioms Qrh.JointDetector.FiveColourPoisson.natural_colour_pair_poisson

#print axioms Qrh.JointDetector.FiveColourPoisson.naturalColourPairRow_eq_idealRowHom
#print axioms Qrh.JointDetector.FiveColourPoisson.pivot_left_crossBlock

#print axioms Qrh.JointDetector.FiveColourPoisson.pivot_left_crossBlock_fixed_ray
#print axioms Qrh.JointDetector.FiveColourPoisson.pivot_right_crossBlock_fixed_ray

#print axioms Qrh.JointDetector.FiveColourPoisson.canonicalProductGauss_pivot_swap

#print axioms Qrh.JointDetector.FiveColourPoisson.canonicalProductGauss_pivot_swap_fixed_ray

#print axioms Qrh.JointDetector.FiveColourPoisson.primitivePair_frozen_frequency_fixed_rays

#print axioms Qrh.JointDetector.FiveColourPoisson.mixed_dual_frequency_factor

#print axioms Qrh.JointDetector.FiveColourPoisson.higherCrossPhase_eq_idealRowHom
