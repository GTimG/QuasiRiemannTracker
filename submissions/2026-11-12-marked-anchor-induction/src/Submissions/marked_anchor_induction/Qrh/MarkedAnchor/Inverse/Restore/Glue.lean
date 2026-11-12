/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Datum
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Orient
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.InjMark

/-!
# Inverse.Restore.Glue — from the `imageAdm` datum to the child data

* `mobiusChildSumInj_negative`: the negative injective child moment is the positive one of
  `(conjHom ψ, star a, star Φ)` (injective version of `Orient`).
* Pools: `coprime_of_norm_lt` (the deletion gate makes slot primes coprime to `mod δ`),
  `coprime_ray_of_mem`, `mem_pool_of_coprime`, `coprime_childRay_iff`, **`childLists_eq`**
  (the pool-index lists, mapped to ideals, are the child canonical pools).
* `norm_coeff_eq_one`, **`norm_child_coeff_le`** (child slot coefficients are bounded by `1`).
* **`childClass_congr`**: the child class depends on `δ`, `η'` only through their moduli.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.SevenEighths.HeckeFamily (Character idealCoeff)
open OAI.ConcretePrimeRowBridge (primePool)
open OAI.CanonicalQuadraticSieve (poolPrimary)
open OAI.CanonicalCoefficientClass (FactorsModulo fixedBaseConductor)
open OAI.FirstCauchyArithmetic (supportMobius)
open Qrh.MarkedAnchor.Interface.Contract

local notation "O" => ActualEisensteinCubic.O

/-! ## Orientation (injective marks) -/

theorem primeMarkInj_star {ι σ : Type} [DecidableEq ι] (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    star (primeMarkInj I L (fun i j => star (a i j)) A) = primeMarkInj I L a A := by
  unfold primeMarkInj
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

theorem mobiusChildSumInj_negative {ι σ : Type} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (Xc Z Hc : ℝ) :
    mobiusChildSumInj p hg pool ψ m slots lists a Φ Xc true Z Hc =
      mobiusChildSumInj p hg pool (conjHom ψ) m slots lists (fun i j => star (a i j))
        (fun x => star (Φ x)) Xc false Z Hc := by
  unfold mobiusChildSumInj
  apply Finset.sum_congr rfl
  intro y _
  have hrow : mobiusChildRowInj p hg pool ψ m slots lists a Φ Xc true y =
      star (mobiusChildRowInj p hg pool (conjHom ψ) m slots lists (fun i j => star (a i j))
        (fun x => star (Φ x)) Xc false y) := by
    unfold mobiusChildRowInj
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro A _
    simp only [if_true, Bool.false_eq_true, if_false, star_mul', conjHom_apply, star_star,
      supportMobius_star, rowCoprimeMask_star, primeMarkInj_star, ofReal_star']
  rw [hrow, norm_star]

theorem star_childLogTest (Φ : ℝ → ℂ) (s : ℝ) :
    (fun x => star (childLogTest Φ s x)) = childLogTest (fun x => star (Φ x)) (-s) := by
  funext x
  unfold childLogTest
  rw [star_mul', logPhase_star]

/-! ## Pools -/

theorem coprime_of_norm_lt (P M : Ideal O) [hP : P.IsMaximal] (hM : M ≠ ⊥)
    (h : (M.absNorm : ℝ) < P.absNorm) : IsCoprime P M := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  have heq : P = P ⊔ M := hP.eq_of_le hne le_sup_left
  have hle : M ≤ P := by rw [heq]; exact le_sup_right
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  have hM0 : Ideal.absNorm M ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact fun h0 => hM (h0.trans Ideal.zero_eq_bot)
  have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hd
  have h2 : (P.absNorm : ℝ) ≤ M.absNorm := by exact_mod_cast h1
  linarith

theorem coprime_ray_of_mem (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O ⧸ rayM)ˣ) (X : ℝ)
    (P : Ideal O) (hP : P ∈ canonicalPool rayM H X) : IsCoprime P rayM := by
  unfold canonicalPool CenteredMomentPrimeSlot.primePool at hP
  simp only [Finset.mem_filter] at hP
  obtain ⟨⟨_, _, hc⟩, _⟩ := hP
  obtain ⟨_, a, ha, u, hua, _⟩ := hc
  rw [← ha, ← IdealCharacter.isUnit_mk_iff_isCoprime, ← hua]
  exact u.isUnit

theorem canonicalPool_norm (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O ⧸ rayM)ˣ) (X : ℝ)
    (hX : 0 < X) (P : Ideal O) (hP : P ∈ canonicalPool rayM H X) :
    X ≤ (P.absNorm : ℝ) ∧ (P.absNorm : ℝ) ≤ 2 * X ∧ Prime P := by
  unfold canonicalPool CenteredMomentPrimeSlot.primePool at hP
  simp only [Finset.mem_filter] at hP
  obtain ⟨⟨_, hp, _⟩, hr⟩ := hP
  rw [Set.mem_Icc, le_div_iff₀ hX, div_le_iff₀ hX, one_mul] at hr
  exact ⟨hr.1, by linarith [hr.2], hp⟩

theorem mem_pool_of_coprime (q D : ℕ) (P : Ideal O) (hP : Prime P) (hND : (P.absNorm : ℝ) ≤ D)
    (hc : IsCoprime P (childModulus q)) : P ∈ primePool (childF q D) := by
  have hPmax : P.IsMaximal :=
    (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  rw [ConcretePrimeRowBridge.mem_primePool_iff]
  refine ⟨P, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨ConcretePrimeRowBridge.mem_outsideIdealsUpTo.mpr ⟨?_, ?_, ?_⟩,
      hP.irreducible.squarefree⟩
    · have : Ideal.absNorm P ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hP.ne_zero
      omega
    · exact_mod_cast hND
    · intro P' hP' hdvd
      have hP'max : P'.IsMaximal := CanonicalQuadraticSieve.gcdMaskPrimes_maximal _ ⟨P', hP'⟩
      have hle : P ≤ P' := Ideal.le_of_dvd hdvd
      have heq : P = P' := hPmax.eq_of_le hP'max.ne_top hle
      have hcm : childModulus q ≤ P := heq ▸ excluded_le q P' hP'
      rw [Ideal.isCoprime_iff_sup_eq, sup_eq_left.mpr hcm] at hc
      exact hPmax.ne_top hc
  · rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hP.irreducible, normalize_eq]
    exact Multiset.mem_singleton_self P

section Child
variable (q D : ℕ) (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
  (hH : RayOrthogonality.globalUnits rayM ≤ G.twist)

theorem coprime_childRay_iff (hq : q ≠ 0) (δ η' : Character) (hη' : η'.modulus = childModulus q)
    (hδ0 : δ.modulus ≠ ⊥) (X : ℝ) (P : Ideal O) (hPL : P ∈ canonicalPool rayM G.pool X)
    (hδ : (δ.modulus.absNorm : ℝ) < P.absNorm) (hND : (P.absNorm : ℝ) ≤ D) :
    P ∈ primePool (childF q D) ↔ IsCoprime P (childRay rayM δ η') := by
  have hX : 0 < X ∨ X ≤ 0 := lt_or_ge 0 X
  have hprime : Prime P := by
    unfold canonicalPool CenteredMomentPrimeSlot.primePool at hPL
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hPL).1).2.1
  have hPmax : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  unfold childRay
  rw [IsCoprime.mul_right_iff, IsCoprime.mul_right_iff, hη']
  constructor
  · intro hmem
    refine ⟨⟨coprime_ray_of_mem rayM G.pool X P hPL, coprime_of_norm_lt P _ hδ0 hδ⟩, ?_⟩
    exact pool_coprime q D hq ⟨P, hmem⟩
  · rintro ⟨_, hc⟩
    exact mem_pool_of_coprime q D P hprime hND hc

/-- **The pool-index lists are the child canonical pools.** -/
theorem childLists_eq (hq : q ≠ 0) (δ η' : Character) (hη' : η'.modulus = childModulus q)
    (hδ0 : δ.modulus ≠ ⊥) (X : ℝ) (lists : Finset (primePool (childF q D)))
    (L : Finset (Ideal O)) (hL : L = canonicalPool rayM G.pool X)
    (hlists : ∀ P : primePool (childF q D), P ∈ lists ↔ P.val ∈ L)
    (hX : (δ.modulus.absNorm : ℝ) < X) (hXD : 2 * X ≤ D) :
    lists.map (Function.Embedding.subtype _) =
      canonicalPool (childRay rayM δ η') (childSlotTwist rayM G hH δ η').pool X := by
  have hX0 : 0 < X := lt_of_le_of_lt (Nat.cast_nonneg _) hX
  ext P
  rw [Finset.mem_map, mem_canonicalPool_child]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    have hQL : Q.val ∈ L := (hlists Q).mp hQ
    rw [hL] at hQL
    obtain ⟨hN1, hN2, _⟩ := canonicalPool_norm rayM G.pool X hX0 Q.val hQL
    refine ⟨hQL, (coprime_childRay_iff q D rayM G hq δ η' hη' hδ0 X Q.val hQL
      (lt_of_lt_of_le hX hN1) (hN2.trans hXD)).mp Q.property⟩
  · rintro ⟨hPL, hc⟩
    obtain ⟨hN1, hN2, _⟩ := canonicalPool_norm rayM G.pool X hX0 P hPL
    have hmem := (coprime_childRay_iff q D rayM G hq δ η' hη' hδ0 X P hPL
      (lt_of_lt_of_le hX hN1) (hN2.trans hXD)).mpr hc
    refine ⟨⟨P, hmem⟩, (hlists _).mpr (hL ▸ hPL), rfl⟩

/-- **The child class depends on `δ`, `η'` only through their moduli.** -/
theorem childClass_congr (W' : ℝ → ℂ) (σ : ℝ) (δ₁ δ₂ η₁ η₂ : Character)
    (h1 : δ₁.modulus = δ₂.modulus) (h2 : η₁.modulus = η₂.modulus) :
    canonicalSlotsRay W' σ (childRay rayM δ₁ η₁) (childSlotTwist rayM G hH δ₁ η₁)
        (childSlotTwist_hH rayM G hH δ₁ η₁) =
      canonicalSlotsRay W' σ (childRay rayM δ₂ η₂) (childSlotTwist rayM G hH δ₂ η₂)
        (childSlotTwist_hH rayM G hH δ₂ η₂) := by
  cases δ₁; cases δ₂; cases η₁; cases η₂
  simp only at h1 h2
  subst h1 h2
  rfl

end Child

/-! ## Coefficient bounds -/

theorem norm_coeff_eq_one (χ : Character) (P : Ideal O) (h : idealCoeff χ P ≠ 0) :
    ‖idealCoeff χ P‖ = 1 := by
  have h1 := congrArg norm (star_coeff_eq_inv χ P)
  rw [norm_star, norm_inv] at h1
  have hpos : 0 < ‖idealCoeff χ P‖ := norm_pos_iff.mpr h
  have h2 : ‖idealCoeff χ P‖ * ‖idealCoeff χ P‖ = 1 := by
    calc ‖idealCoeff χ P‖ * ‖idealCoeff χ P‖ = ‖idealCoeff χ P‖ * ‖idealCoeff χ P‖⁻¹ := by
          rw [← h1]
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  nlinarith

theorem norm_sqrt_div_le (X N : ℝ) (hX : 0 ≤ X) (hXN : X ≤ N) :
    ‖((Real.sqrt (X / N) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Real.sqrt_le_one]
  rcases eq_or_lt_of_le (hX.trans hXN) with h | h
  · rw [← h]; simp
  · exact div_le_one_of_le₀ hXN h.le

section CoeffBound
variable (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
  (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ) (σ : ℝ)
  (data : HeckeInverseAmplification.RowData) (θ : RayQuotient.Characters rayM G.twist)
  (q : ℕ) (hq : q ≠ 0) (ψ : O →* ℂ)
  (hψ : FactorsModulo (fixedBaseConductor q * Ideal.span {(4 : O)}) ψ)

/-- **The child slot coefficients are bounded by `1`.** -/
theorem norm_child_coeff_le (neg : Bool) (v t τ X : ℝ) (hX : 0 < X) (P : Ideal O) [P.IsMaximal]
    (hP0 : P ≠ ⊥) (hN : X ≤ (P.absNorm : ℝ))
    (hcop : IsCoprime P (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
      (childCharacter q hq ψ hψ)))
    (hβ : ‖rayCoeff rayM G hH W σ data θ X v P‖ ≤ 1) (hψn : ∀ x, ‖ψ x‖ ≤ 1) :
    ‖rayCoeff (childRay rayM (DetectorDictionaryInverseRawInitialGates.deletedBase data)
          (childCharacter q hq ψ hψ))
        (childSlotTwist rayM G hH (DetectorDictionaryInverseRawInitialGates.deletedBase data)
          (childCharacter q hq ψ hψ)) (childSlotTwist_hH rayM G hH _ _)
        (if neg then childBumpN W else childBump W) σ (childData q hq ψ hψ)
        (childTheta rayM neg G hH θ (DetectorDictionaryInverseRawInitialGates.deletedBase data)
          (childCharacter q hq ψ hψ)) X
        (if neg then v + 2 * Real.pi * t + 2 * Real.pi * τ
          else -v - 2 * Real.pi * t + 2 * Real.pi * τ) P‖ ≤ 1 := by
  have hN0 : 0 < (P.absNorm : ℝ) := lt_of_lt_of_le hX hN
  obtain ⟨hδ, _, _, _⟩ := slot_prime_facts rayM data q hq ψ hψ P hP0 hcop
  have hδn := norm_coeff_eq_one _ P hδ
  have hs := norm_sqrt_div_le X (P.absNorm : ℝ) hX.le hN
  have hψP := hψn (CompletedGauss.primaryPrime P)
  cases neg
  · have h := child_coeff_pos rayM G hH W σ data θ q hq ψ hψ v t τ X hX P hP0 hN0 hcop
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h2 := congrArg norm h
    rw [norm_mul (FourierBridge.logPhase τ (Real.log X)), FourierBridge.logPhase_norm, one_mul] at h2
    rw [← h2]
    simp only [norm_mul, norm_neg, norm_star, norm_div, FourierBridge.logPhase_norm, hδn, div_one,
      mul_one]
    calc ‖rayCoeff rayM G hH W σ data θ X v P‖ * ‖ψ (CompletedGauss.primaryPrime P)‖ *
          ‖((Real.sqrt (X / (P.absNorm : ℝ)) : ℝ) : ℂ)‖ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring
  · have h := child_coeff_neg rayM G hH W σ data θ q hq ψ hψ v t τ X hX P hP0 hN0 hcop
    simp only [↓reduceIte]
    have h2 := congrArg norm h
    rw [norm_mul (FourierBridge.logPhase τ (Real.log X)), FourierBridge.logPhase_norm, one_mul] at h2
    rw [← h2]
    simp only [norm_mul, norm_neg, norm_star, norm_div, FourierBridge.logPhase_norm, hδn, div_one,
      mul_one]
    calc ‖rayCoeff rayM G hH W σ data θ X v P‖ * ‖ψ (CompletedGauss.primaryPrime P)‖ *
          ‖((Real.sqrt (X / (P.absNorm : ℝ)) : ℝ) : ℂ)‖ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by ring

end CoeffBound

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.mobiusChildSumInj_negative
#print axioms Qrh.MarkedAnchor.Inverse.Restore.childLists_eq
#print axioms Qrh.MarkedAnchor.Inverse.Restore.childClass_congr
#print axioms Qrh.MarkedAnchor.Inverse.Restore.norm_child_coeff_le
