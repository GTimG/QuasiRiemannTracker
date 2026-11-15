/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Restore.Child
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.Dyadic

/-!
# Inverse.Restore.Poly — the full child column is an actual inverse polynomial

Generic identification: if a character `χ` has value `idealCoeff χ (p i) = -c i·‖p i‖` on the pool
primes (so `c i = -χ(p i)/√N p i`, the child weight with the Möbius sign) and every squarefree
ideal of the support of `μ χ Φ(N·/Y)` is a product of pool primes, then the profiled squarefree
column over the whole pool is the baseline inverse polynomial at scale `Y`:

`col c (primeN p) Φ univ Y = polynomial χ true (fun x => Φ x · x^{-1/2}) Y 0 0`
(**`col_eq_polynomial`**). The normalization `Y^{-1/2}·(N/Y)^{-1/2} = N^{-1/2}` is exact.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.ConcreteTraceCRT (eisEmbedding)
open OAI.SevenEighths.HeckeDyadic (polynomial summand coefficient shift NonzeroIdeal)
open OAI.SevenEighths.HeckeFamily (Character idealCoeff)

local notation "O" => ActualEisensteinCubic.O

/-- Products of distinct pool primes determine the subset. -/
theorem prod_span_injective {ι : Type} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {A B : Finset ι} (h : ∏ i ∈ A, Ideal.span {p i} = ∏ i ∈ B, Ideal.span {p i}) : A = B := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp i) inferInstance
  have key : ∀ (A B : Finset ι), ∏ i ∈ A, Ideal.span {p i} = ∏ i ∈ B, Ideal.span {p i} →
      A ⊆ B := by
    intro A B h i hi
    have hd : Ideal.span {p i} ∣ ∏ j ∈ B, Ideal.span {p j} := by
      rw [← h]; exact Finset.dvd_prod_of_mem _ hi
    obtain ⟨j, hj, hij⟩ := ((hprime i).dvd_finset_prod_iff _).mp hd
    have hle : Ideal.span {p j} ≤ Ideal.span {p i} := Ideal.le_of_dvd hij
    have heq : Ideal.span {p j} = Ideal.span {p i} :=
      (inferInstance : (Ideal.span {p j}).IsMaximal).eq_of_le
        (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top hle
    have : j = i := hinj heq
    rw [← this]; exact hj
  exact Finset.Subset.antisymm (key A B h) (key B A h.symm)

/-- **The full child column is the inverse polynomial of `χ`.** -/
theorem col_eq_polynomial {ι : Type} [Fintype ι] [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (χ : Character) (c : ι → ℂ)
    (hc : ∀ i, c i = -(idealCoeff χ (Ideal.span {p i}) *
      (((‖eisEmbedding (p i)‖)⁻¹ : ℝ) : ℂ)))
    (Φ : ℝ → ℂ) (Y : ℝ) (hY : 0 < Y)
    (hcover : ∀ I : Ideal O, I ≠ 0 →
      (UniqueFactorizationMonoid.moebius I : ℂ) * idealCoeff χ I ≠ 0 →
      Φ ((Ideal.absNorm I : ℝ) / Y) ≠ 0 → ∃ A : Finset ι, I = ∏ i ∈ A, Ideal.span {p i}) :
    col c (primeN p) Φ Finset.univ Y =
      polynomial χ true (fun x => Φ x * ((x : ℂ) ^ (-(1/2 : ℂ)))) Y 0 0 := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp i) inferInstance
  have hne : ∀ A : Finset ι, (∏ i ∈ A, Ideal.span {p i}) ≠ 0 :=
    fun A => Finset.prod_ne_zero_iff.mpr (fun i _ => (hprime i).ne_zero)
  let f : Finset ι → NonzeroIdeal := fun A => ⟨∏ i ∈ A, Ideal.span {p i}, hne A⟩
  have hf : Function.Injective f := by
    intro A B h
    exact prod_span_injective p hp hinj (congrArg Subtype.val h)
  have hshift : shift 0 0 = 0 := by simp [shift]
  unfold polynomial
  rw [tsum_eq_sum (s := Finset.univ.image f) ?zero]
  case zero =>
    intro I hI
    by_contra hsum
    unfold summand coefficient at hsum
    simp only [if_true] at hsum
    have h1 : (UniqueFactorizationMonoid.moebius I.val : ℂ) * idealCoeff χ I.val ≠ 0 := by
      intro h; apply hsum; rw [h]; ring
    have h2 : Φ ((Ideal.absNorm I.val : ℝ) / Y) ≠ 0 := by
      intro h; apply hsum
      simp only [OAI.SevenEighths.HeckeDyadic.norm, h, zero_mul, mul_zero]
    obtain ⟨A, hA⟩ := hcover I.val I.property h1 h2
    apply hI
    exact Finset.mem_image.mpr ⟨A, Finset.mem_univ _, Subtype.ext hA.symm⟩
  rw [Finset.sum_image (fun A _ B _ h => hf h), Finset.mul_sum]
  unfold col
  rw [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro A _
  unfold summand coefficient
  simp only [if_true, hshift, neg_zero, Complex.cpow_zero, mul_one]
  have hμ : (UniqueFactorizationMonoid.moebius (∏ i ∈ A, Ideal.span {p i}) : ℂ) =
      (-1 : ℂ) ^ A.card := prime_product_moebius _ hprime hinj A
  have hχ : idealCoeff χ (∏ i ∈ A, Ideal.span {p i}) =
      ∏ i ∈ A, idealCoeff χ (Ideal.span {p i}) := map_prod _ _ _
  have hN : OAI.SevenEighths.HeckeDyadic.norm (f A) = ∏ i ∈ A, primeN p i := by
    simp only [OAI.SevenEighths.HeckeDyadic.norm, f, map_prod, Nat.cast_prod]
    exact Finset.prod_congr rfl (fun i _ => (primeN_eq_absNorm p i).symm)
  have hNpos : 0 < ∏ i ∈ A, primeN p i :=
    Finset.prod_pos (fun i _ => lt_of_lt_of_le (by norm_num) (primeN_two_le p hp i))
  have hsqrt : Real.sqrt (∏ i ∈ A, primeN p i) = ∏ i ∈ A, ‖eisEmbedding (p i)‖ := by
    rw [← primeProductNorm_eq_prod, sqrt_primeProductNorm]
  have hkey : (Y : ℂ) ^ (-(1/2 : ℂ)) * (((∏ i ∈ A, primeN p i) / Y : ℝ) : ℂ) ^ (-(1/2 : ℂ)) =
      (((∏ i ∈ A, ‖eisEmbedding (p i)‖)⁻¹ : ℝ) : ℂ) := by
    have e1 : (Y : ℂ) ^ (-(1/2 : ℂ)) = ((Y ^ (-(1/2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hY.le]; push_cast; ring_nf
    have e2 : (((∏ i ∈ A, primeN p i) / Y : ℝ) : ℂ) ^ (-(1/2 : ℂ)) =
        ((((∏ i ∈ A, primeN p i) / Y) ^ (-(1/2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (div_pos hNpos hY).le]; push_cast; ring_nf
    rw [e1, e2, ← Complex.ofReal_mul, ← Real.mul_rpow hY.le (div_pos hNpos hY).le,
      mul_div_cancel₀ _ hY.ne', Real.rpow_neg hNpos.le, ← Real.sqrt_eq_rpow, hsqrt]
  rw [hN, hμ, hχ]
  have hc' : ∏ i ∈ A, c i = (-1 : ℂ) ^ A.card * (∏ i ∈ A, idealCoeff χ (Ideal.span {p i})) *
      (((∏ i ∈ A, ‖eisEmbedding (p i)‖)⁻¹ : ℝ) : ℂ) := by
    rw [Finset.prod_congr rfl (fun i _ => hc i), Finset.prod_neg, Finset.prod_mul_distrib]
    push_cast
    rw [Finset.prod_inv_distrib]
    ring
  rw [hc', ← hkey]
  ring

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.col_eq_polynomial
