/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Expand
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Restore.Orient

/-!
# Inverse.Restore.Column — the physical child row as a marked profiled column

`mobiusChildRow p hg pool ψ m slots lists a Φ Xc false y = markedCol (childWeight …) (primeN p) Φ
pool slots lists a Xc`, where the prime weight is
`childWeight p hg ψ m y i = -(ψ(p i) · mask_i(m) · χ_{p i}(y) / ‖p i‖)` (Möbius sign included) and
`primeN p i = ‖p i‖²`; with `Expand.markedCol_tuple` the row is a tuple sum of unmarked columns.

* `primeProductNorm_eq_prod`, `sqrt_primeProductNorm`, `rowCoprimeMask_eq_prod`,
  `finiteSquarefreeRow_eq_prod`, `supportMobius_eq_pow` (distinct primes).
* `childWeight`, `mobiusChildRow_eq_markedCol`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.FirstCauchyArithmetic (supportMobius)
open OAI.ConcreteTraceCRT (eisEmbedding)
open Qrh.MarkedAnchor.Inverse.Poisson

local notation "O" => ActualEisensteinCubic.O

section
variable {ι : Type} [DecidableEq ι] (p : ι → O)

/-- The norm of one pool prime. -/
def primeN (i : ι) : ℝ := ‖eisEmbedding (p i)‖^2

theorem primeProductNorm_eq_prod (A : Finset ι) :
    primeProductNorm p A = ∏ i ∈ A, primeN p i := by
  simp only [primeProductNorm, primeN, map_prod, norm_prod, Finset.prod_pow]

theorem sqrt_primeProductNorm (A : Finset ι) :
    Real.sqrt (primeProductNorm p A) = ∏ i ∈ A, ‖eisEmbedding (p i)‖ := by
  simp only [primeProductNorm, map_prod, norm_prod]
  exact Real.sqrt_sq (Finset.prod_nonneg (fun i _ => norm_nonneg _))

theorem rowCoprimeMask_eq_prod (P : ι → Ideal O) (A : Finset ι) (u : O) :
    rowCoprimeMask P A u = ∏ i ∈ A, rowCoprimeMask P {i} u := by
  unfold rowCoprimeMask
  by_cases h : ∃ i ∈ A, u ∈ P i
  · obtain ⟨i, hi, hu⟩ := h
    rw [if_pos ⟨i, hi, hu⟩]
    symm
    apply Finset.prod_eq_zero hi
    rw [if_pos ⟨i, Finset.mem_singleton_self i, hu⟩]
  · rw [if_neg h]
    symm
    apply Finset.prod_eq_one
    intro i hi
    rw [if_neg]
    rintro ⟨j, hj, hu⟩
    rw [Finset.mem_singleton] at hj
    subst hj
    exact h ⟨j, hi, hu⟩

theorem finiteSquarefreeRow_eq_prod (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (A : Finset ι) (u : O) :
    finiteSquarefreeRow P hg A u = ∏ i ∈ A, finiteSquarefreeRow P hg {i} u := by
  unfold finiteSquarefreeRow
  simp

theorem supportMobius_eq_pow [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hinj : Function.Injective (fun i => Ideal.span {p i})) (A : Finset ι) :
    supportMobius (fun i => Ideal.span {p i}) A = (-1 : ℂ)^A.card := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hp i) inferInstance
  exact prime_product_moebius _ hprime hinj A

/-- The prime weight of the physical child column (Möbius sign included). -/
def childWeight [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (ψ : O →* ℂ) (m y : O) (i : ι) : ℂ :=
  -(ψ (p i) * rowCoprimeMask (fun i => Ideal.span {p i}) {i} m *
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg {i} y *
    (((‖eisEmbedding (p i)‖)⁻¹ : ℝ) : ℂ))

/-- The positive physical child row is a marked profiled column. -/
theorem mobiusChildRow_eq_markedCol [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (pool : Finset ι) (ψ : O →* ℂ) (m : O)
    {σ : Type} (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (Φ : ℝ → ℂ)
    (Xc : ℝ) (y : O) :
    mobiusChildRow p hg pool ψ m slots lists a Φ Xc false y =
      markedCol (childWeight p hg ψ m y) (primeN p) Φ pool slots lists a Xc := by
  unfold mobiusChildRow markedCol
  apply Finset.sum_congr rfl
  intro A _
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [supportMobius_eq_pow p hp hinj, map_prod, rowCoprimeMask_eq_prod,
    finiteSquarefreeRow_eq_prod, sqrt_primeProductNorm, primeProductNorm_eq_prod]
  unfold childWeight
  rw [Finset.prod_neg]
  simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Complex.ofReal_prod,
    Complex.ofReal_inv]
  ring

end

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.mobiusChildRow_eq_markedCol
