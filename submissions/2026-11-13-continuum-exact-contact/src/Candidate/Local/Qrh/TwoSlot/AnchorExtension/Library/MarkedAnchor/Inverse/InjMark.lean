/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Poisson.Interface

/-!
# Inverse.InjMark — injective (marked-squarefree) column marks

The parent pools may overlap, so inside the inverse reduction the column mark is the INJECTIVE
one: a slot tuple contributes only when it hits distinct primes (the marked column stays
squarefree).

* `primeMarkInj I L a A = ∑_{p ∈ I.pi L, p injective} ∏_{i ∈ I} [p i ∈ A] a i (p i)`; it is the
  baseline `primeMark` when the lists are pairwise disjoint (`primeMarkInj_eq_primeMark`).
* `mobiusChildRowInj`, `mobiusChildSumInj`, `ChildBoundInj`: the Poisson child objects
  (`Poisson.mobiusChildRow/Sum`, `Poisson.ChildBound`) with the injective mark; they agree with
  the Poisson ones on pairwise disjoint lists. `ChildBoundInj` is the child bound that the
  restoration (`Select/Assembly.RestoreChildAt`) delivers: pools may overlap.
* `ChildBoundInj` asks for the frozen slots `Js` only at column scales `Xc` paid by an
  injective `Js`-tuple `d`: `Xc · ∏ N(d_i) ≤ 2 Xmax` (automatic for `Js = ∅`).
* `TupleInj`, `injPi` (injective tuples), `exists_injPi_of_markInj_ne_zero`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped Classical BigOperators ContDiff
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open OAI.FirstPassCubeLabels (primeProductNorm)
open OAI.FirstCauchyArithmetic (supportMobius)
open OAI.ConcreteTraceCRT (eisEmbedding)

local notation "O" => ActualEisensteinCubic.O

section Laws
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

/-- A tuple on `R` is injective. -/
def TupleInj {R : Finset σ} (d : ∀ i ∈ R, ι) : Prop :=
  ∀ i (hi : i ∈ R) j (hj : j ∈ R), d i hi = d j hj → i = j

/-- The injective tuples of `R.pi L`. -/
def injPi (R : Finset σ) (L : σ → Finset ι) : Finset (∀ i ∈ R, ι) :=
  (R.pi L).filter (fun d => TupleInj d)

theorem mem_injPi {R : Finset σ} {L : σ → Finset ι} {d : ∀ i ∈ R, ι} :
    d ∈ injPi R L ↔ d ∈ R.pi L ∧ TupleInj d := by
  unfold injPi; exact Finset.mem_filter

theorem injPi_subset (R : Finset σ) (L : σ → Finset ι) : injPi R L ⊆ R.pi L :=
  Finset.filter_subset _ _

end Laws

section Mark
variable {σ ι : Type*} [DecidableEq ι]

/-- The injective (marked-squarefree) prime mark. -/
def primeMarkInj (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ) (A : Finset ι) : ℂ :=
  ∑ p ∈ (I.pi L).filter (fun p => ∀ i (hi : i ∈ I) j (hj : j ∈ I), p i hi = p j hj → i = j),
    ∏ i ∈ I.attach, if p i.1 i.2 ∈ A then a i.1 (p i.1 i.2) else 0

/-- On pairwise disjoint lists every tuple is injective: the injective mark is the full mark. -/
theorem primeMarkInj_eq_primeMark (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) (hdis : (I : Set σ).PairwiseDisjoint L) :
    primeMarkInj I L a A = primeMark I L a A := by
  rw [primeMark_eq_tuple_sum, primeMarkInj, Finset.filter_true_of_mem]
  intro p hp i hi j hj hij
  by_contra hne
  have hpi := Finset.mem_pi.mp hp i hi
  have hpj := Finset.mem_pi.mp hp j hj
  rw [← hij] at hpj
  exact Finset.disjoint_left.mp (hdis (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) hne) hpi hpj

/-- A nonzero injective mark of `A` has an injective tuple with all its primes in `A`. -/
theorem exists_injPi_of_markInj_ne_zero (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) (h : primeMarkInj I L a A ≠ 0) :
    ∃ d ∈ injPi I L, ∀ k ∈ I.attach, d k.1 k.2 ∈ A := by
  unfold primeMarkInj at h
  obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_filter] at hd
  refine ⟨d, mem_injPi.mpr ⟨hd.1, hd.2⟩, fun k hk => ?_⟩
  by_contra hA
  exact hne (Finset.prod_eq_zero hk (if_neg hA))

end Mark

/-! ## The Poisson child with the injective mark -/

/-- `Poisson.mobiusChildRow` with the injective mark. -/
def mobiusChildRowInj {ι σ : Type} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (Xc : ℝ) (negative : Bool) (y : O) : ℂ :=
  ∑ A ∈ pool.powerset,
    supportMobius (fun i => Ideal.span {p i}) A * ψ (∏ i ∈ A, p i) *
      rowCoprimeMask (fun i => Ideal.span {p i}) A m *
      (if negative then star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A y)
        else finiteSquarefreeRow (fun i => Ideal.span {p i}) hg A y) *
      primeMarkInj slots lists a A * Φ (primeProductNorm p A / Xc) *
      (((Real.sqrt (primeProductNorm p A))⁻¹ : ℝ) : ℂ)

/-- `Poisson.mobiusChildSum` with the injective mark. -/
def mobiusChildSumInj {ι σ : Type} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (Φ : ℝ → ℂ) (Xc : ℝ) (negative : Bool) (Z Hc : ℝ) : ℝ :=
  ∑ y ∈ nonzeroChildFrequencyBall 1 (Z^Hc),
    ‖mobiusChildRowInj p hg pool ψ m slots lists a Φ Xc negative y‖^2

/-- `Poisson.ChildBound` with the injective mark (pools may overlap). -/
def ChildBoundInj {ι σ : Type} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) {J : ℕ} (Φs : Fin J → ℝ → ℂ) (degree : ℕ) (Z Xmax Gmax Hc B : ℝ) :
    Prop :=
  ∀ t ∈ pool.powerset, primeProductNorm p t ≤ Gmax →
  ∀ Js ∈ slots.powerset, ∀ ψ : O →* ℂ, Poisson.IsChildRay Ψ ψ → ∀ j : Fin J, ∀ s : ℝ,
  ∀ Xc : ℝ, 0 < Xc → Xc ≤ Xmax →
  (∃ d ∈ injPi Js lists, Xc * ∏ i ∈ Js.attach, ‖eisEmbedding (p (d i.1 i.2))‖ ^ 2 ≤ 2 * Xmax) →
  ∀ negative : Bool,
    mobiusChildSumInj p hg (pool \ t) ψ m (slots \ Js) lists a (childLogTest (Φs j) s) Xc
      negative Z Hc ≤ B * (1+‖s‖)^(2*degree)

/-- On pairwise disjoint lists the Poisson child bound gives the injective child bound (the
converse fails since `ChildBoundInj` only asks for frozen-slot scales paid by a tuple). -/
theorem childBoundInj_of_childBound {ι σ : Type} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) {J : ℕ} (Φs : Fin J → ℝ → ℂ) (degree : ℕ) (Z Xmax Gmax Hc B : ℝ)
    (hdis : (slots : Set σ).PairwiseDisjoint lists)
    (h : Poisson.ChildBound p hg pool Ψ m slots lists a Φs degree Z Xmax Gmax Hc B) :
    ChildBoundInj p hg pool Ψ m slots lists a Φs degree Z Xmax Gmax Hc B := by
  intro t ht hG Js hJs ψ hψ j s Xc hX hXm _ negative
  refine le_of_eq_of_le ?_ (h t ht hG Js hJs ψ hψ j s Xc hX hXm negative)
  have hd : ((slots \ Js : Finset σ) : Set σ).PairwiseDisjoint lists :=
    hdis.subset (Finset.coe_subset.mpr Finset.sdiff_subset)
  unfold Poisson.mobiusChildSum mobiusChildSumInj Poisson.mobiusChildRow mobiusChildRowInj
  simp only [primeMarkInj_eq_primeMark _ _ _ _ hd]

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.primeMarkInj_eq_primeMark
#print axioms Qrh.MarkedAnchor.Inverse.childBoundInj_of_childBound
