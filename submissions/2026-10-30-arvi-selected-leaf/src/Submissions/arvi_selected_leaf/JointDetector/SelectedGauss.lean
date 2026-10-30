/- Copyright (c) 2026 Joseph Bebel. -/
import Submissions.arvi_selected_leaf.JointDetector.PairGauss

/-! Gauss separation on a varying active conductor inside one fixed prime
universe. Each unary block on the right uses only its own original support. -/
namespace Qrh.JointDetector
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open OAI OAI.SevenEighths ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalRowCompletion CanonicalQuadraticSieve ConcreteTraceCRT CompletedGauss
open ConcretePrimeRowBridge GaussGeneratorTransport FiniteGaussPhase
open MixedCrossSeparation MixedGaussConversion
local notation "O" => ActualEisensteinCubic.O

def supportIn {ι : Type*} (U S : Finset ι) : Finset U :=
  Finset.univ.filter (fun i => i.val ∈ S)

@[simp] theorem mem_supportIn {ι : Type*} (U S : Finset ι) (i : U) :
    i ∈ supportIn U S ↔ i.val ∈ S := by simp [supportIn]

theorem prod_supportIn {ι M : Type*} [CommMonoid M]
    (U S : Finset ι) (hS : S ⊆ U) (f : ι → M) :
    (∏ i ∈ supportIn U S, f i.val) = ∏ i ∈ S, f i := by
  apply Finset.prod_bij (fun i _ => i.val)
  · intro i hi; exact (mem_supportIn U S i).mp hi
  · intro i hi k hk h; exact Subtype.ext h
  · intro i hi
    exact ⟨⟨i, hS hi⟩, (mem_supportIn U S _).mpr hi, rfl⟩
  · intro i hi; rfl

theorem unaryPairGauss_supportIn {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (U S : Finset ι) [DecidableEq U] (hS : S ⊆ U) (j : ℕ) :
    unaryPairGauss (fun i : U => p i.val) (fun i => hp i.val)
      (fun i => hg i.val) (supportIn U S) j = unaryPairGauss p hp hg S j := by
  unfold unaryPairGauss
  rw [← prod_supportIn U S hS]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  have he : (supportIn U S).erase i = supportIn U (S.erase i.val) := by
    ext k
    simp only [Finset.mem_erase, mem_supportIn]
    exact and_congr (not_congr Subtype.val_inj.symm) Iff.rfl
  rw [he]
  simpa only [crossSymbol] using
    prod_supportIn U (S.erase i.val) ((Finset.erase_subset _ _).trans hS)
      (fun k => crossSymbol p hg i.val k ^ j)

theorem selectedPrimeCoprime {ι : Type*} (p : ι → O)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (U : Finset ι) :
    Pairwise (Function.onFun IsCoprime (fun i : U => Ideal.span {p i.val})) := by
  intro i k hik
  exact hcop (fun h => hik (Subtype.ext h))

/-- The active modulus has exactly the primes in `S ∪ T`; it does not
include the unused primes of the common universe. -/
def selectedPairGauss {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) : ℂ :=
  canonicalNormalizedGauss (fun i : (S ∪ T : Finset ι) => Ideal.span {p i.val})
    (selectedPrimeCoprime p hcop (S ∪ T)) (fun i => hg i.val)
    (fun i => if i.val ∈ T then 5 else 1)

/-- The active conductor character is exactly the original pair, including
its natural zeros at every prime of either support. -/
theorem selectedPairRow_actual {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (hd : Disjoint S T) (n : O) :
    finiteSexticRow (fun i : (S ∪ T : Finset ι) => Ideal.span {p i.val})
      (fun i => hg i.val) (fun i => if i.val ∈ T then 5 else 1) n =
      primitivePair (Ideal.span {∏ i ∈ S, p i}) (Ideal.span {∏ i ∈ T, p i}) n := by
  let : DecidableEq (S ∪ T : Finset ι) := fun a b => Classical.propDecidable (a = b)
  have he : Finset.univ \ supportIn (S ∪ T) T = supportIn (S ∪ T) S := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_univ, mem_supportIn, true_and]
    constructor
    · intro hn; exact (Finset.mem_union.mp i.property).resolve_right hn
    · intro hi ht; exact Finset.disjoint_left.mp hd hi ht
  have hh := finite_pair_row_actual (fun i : (S ∪ T : Finset ι) => p i.val)
    (selectedPrimeCoprime p hcop (S ∪ T)) (fun i => hg i.val)
    (supportIn (S ∪ T) T) n
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
    (r : EisensteinEPrimaryPhase.Coord) (hr : residue (∏ i ∈ T, p i) = r) :
    selectedPairGauss p hcop hg S T =
      quadraticRayPair r r * unaryPairGauss p hp hg S 1 * unaryPairGauss p hp hg T 5 := by
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
    r (by simpa only [hprodT] using hr)
  rw [he, unaryPairGauss_supportIn p hp hg (S ∪ T) S hSc,
    unaryPairGauss_supportIn p hp hg (S ∪ T) T hTc] at hh
  simpa only [selectedPairGauss, mem_supportIn] using hh

end
end Qrh.JointDetector

#print axioms Qrh.JointDetector.unaryPairGauss_supportIn
#print axioms Qrh.JointDetector.selectedPairRow_actual
#print axioms Qrh.JointDetector.selectedPairGauss_fixed_ray
