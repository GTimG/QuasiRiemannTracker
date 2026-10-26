/- Copyright (c) 2026 Sil. Apache-2.0.
Exact reindexing of prime allocations by subsets of a fixed labelled slot family.
Injectivity is the temporary squarefree-marked condition; collisions are not
silently absorbed into this identity and require their separate restoration.
-/
import Candidate.FourthPower.KernelRestrictedState

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.KernelLabelledSlots
noncomputable section
open scoped Classical BigOperators
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open KernelFormal KernelAllocationIdentity KernelRestrictedState
open OAI.IdealMobiusDivisorSum (idealDivisors)
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

variable {α : Type*} [Fintype α]

def frozen (S : Finset PrimeIdeal) (slot : α → S) (T : Finset α) (P : S) : Bool :=
  decide (∃ i ∈ T, slot i=P)

def marked (S : Finset PrimeIdeal) (slot : α → S) : S → Bool := frozen S slot Finset.univ

def frozenLabels (S : Finset PrimeIdeal) (slot : α → S) (a : S → Bool) : Finset α :=
  Finset.univ.filter (fun i => a (slot i)=true)

omit [Fintype α] in
theorem frozen_true (S : Finset PrimeIdeal) (slot : α → S) (T : Finset α) (P : S) :
    frozen S slot T P=true ↔ ∃ i ∈ T, slot i=P := by simp [frozen]

theorem marked_true (S : Finset PrimeIdeal) (slot : α → S) (P : S) :
    marked S slot P=true ↔ ∃ i, slot i=P := by simp [marked,frozen]

theorem mem_frozenLabels (S : Finset PrimeIdeal) (slot : α → S) (a : S → Bool) (i : α) :
    i ∈ frozenLabels S slot a ↔ a (slot i)=true := by simp [frozenLabels]

theorem mem_choices (m b : Bool) : b ∈ choices m ↔ (b=true → m=true) := by
  cases m <;> cases b <;> simp [choices]

theorem frozen_admissible (S : Finset PrimeIdeal) (slot : α → S) (T : Finset α) :
    frozen S slot T ∈ Fintype.piFinset (fun P => choices (marked S slot P)) := by
  apply Fintype.mem_piFinset.mpr
  intro P
  rw [mem_choices]
  intro h
  obtain ⟨i,hi,he⟩ := (frozen_true S slot T P).mp h
  exact (marked_true S slot P).mpr ⟨i,he⟩

theorem frozen_frozenLabels (S : Finset PrimeIdeal) (slot : α → S) (a : S → Bool)
    (ha : a ∈ Fintype.piFinset (fun P => choices (marked S slot P))) :
    frozen S slot (frozenLabels S slot a) = a := by
  funext P
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨i,hi,he⟩ := (frozen_true S slot _ P).mp h
    exact he ▸ (mem_frozenLabels S slot a i).mp hi
  · intro h
    have hm := (mem_choices _ _).mp (Fintype.mem_piFinset.mp ha P) h
    obtain ⟨i,he⟩ := (marked_true S slot P).mp hm
    exact (frozen_true S slot _ P).mpr ⟨i,(mem_frozenLabels S slot a i).mpr (he.symm ▸ h),he⟩

theorem frozenLabels_frozen (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) (T : Finset α) :
    frozenLabels S slot (frozen S slot T) = T := by
  ext i
  rw [mem_frozenLabels,frozen_true]
  constructor
  · rintro ⟨j,hj,he⟩
    exact hinj he ▸ hj
  · intro hi
    exact ⟨i,hi,rfl⟩

def allocationEquiv (S : Finset PrimeIdeal) (slot : α → S) (hinj : Function.Injective slot) :
    {a : S → Bool // a ∈ Fintype.piFinset (fun P => choices (marked S slot P))} ≃ Finset α where
  toFun a := frozenLabels S slot a.val
  invFun T := ⟨frozen S slot T,frozen_admissible S slot T⟩
  left_inv a := Subtype.ext (frozen_frozenLabels S slot a.val a.property)
  right_inv T := frozenLabels_frozen S slot hinj T

theorem labelled_reindex (S : Finset PrimeIdeal) (slot : α → S) (hinj : Function.Injective slot)
    (f : (S → Bool) → ℤ) :
    (∑ a ∈ Fintype.piFinset (fun P => choices (marked S slot P)), f a) =
      ∑ T : Finset α, f (frozen S slot T) := by
  rw [← Finset.sum_coe_sort (Fintype.piFinset (fun P => choices (marked S slot P))) f]
  exact ((allocationEquiv S slot hinj).symm.sum_comp (fun a => f a.val)).symm

omit [Fintype α] in
theorem frozen_at_slot (S : Finset PrimeIdeal) (slot : α → S) (hinj : Function.Injective slot)
    (T : Finset α) (i : α) : frozen S slot T (slot i) = decide (i ∈ T) := by
  simp [frozen,hinj.eq_iff]

theorem live_complement (S : Finset PrimeIdeal) (slot : α → S) (hinj : Function.Injective slot)
    (T : Finset α) :
    (fun P => marked S slot P && !frozen S slot T P) = frozen S slot Tᶜ := by
  funext P
  by_cases hm : ∃ i, slot i=P
  · obtain ⟨i,rfl⟩ := hm
    simp [marked,frozen_at_slot S slot hinj]
  · have hz (U : Finset α) : frozen S slot U P=false := by
      simp only [frozen,decide_eq_false_iff_not]
      rintro ⟨i,hi,he⟩
      exact hm ⟨i,he⟩
    simp [marked,hz]

omit [Fintype α] in
theorem restricted_frozen_labels (S : Finset PrimeIdeal) (slot : α → S)
    (T : Finset α) (I J : Id) :
    Restricted S (frozen S slot T) I J ↔
      SexticSieve.PowerFree 5 (I*J) ∧ ∀ i ∈ T, ¬(slot i).val.val ∣ I*J := by
  constructor
  · rintro ⟨hfree,havoid⟩
    refine ⟨hfree,?_⟩
    intro i hi
    exact havoid (slot i) ((frozen_true S slot T (slot i)).mpr ⟨i,hi,rfl⟩)
  · rintro ⟨hfree,havoid⟩
    refine ⟨hfree,?_⟩
    intro P hP
    obtain ⟨i,hi,he⟩ := (frozen_true S slot T P).mp hP
    exact he ▸ havoid i hi

/-- Freezing an actual occurrence in a restricted sum retains its common
ordinary puncture. This differs from extraction by the inverse kernel. -/
theorem actual_freezing_restriction (S : Finset PrimeIdeal) (slot : α → S)
    (T : Finset α) (I J : Id) :
    Restricted S (marked S slot) I J ↔
      Restricted S (frozen S slot Tᶜ) I J ∧ ∀ i ∈ T, ¬(slot i).val.val ∣ I*J := by
  rw [marked,restricted_frozen_labels,restricted_frozen_labels]
  simp only [Finset.mem_univ,forall_const]
  constructor
  · rintro ⟨hfree,hall⟩
    exact ⟨⟨hfree,fun i _ => hall i⟩,fun i _ => hall i⟩
  · rintro ⟨⟨hfree,hlive⟩,hfrozen⟩
    refine ⟨hfree,?_⟩
    intro i
    by_cases hi : i ∈ T
    · exact hfrozen i hi
    · exact hlive i (Finset.mem_compl.mpr hi)

/-- The forward finite identity for the original labels, not anonymous primes. -/
theorem forward_labelled_identity (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hs : pairSupport I J ⊆ primeValues S) :
    (∑ T : Finset α, ∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
      kernelOn S (fun P => forwardFactor (frozen S slot T P)) d.1 d.2*
      kernelOn S (fun _P => ordinarySeries) (cofactorPair I J d).1 (cofactorPair I J d).2) =
      if Restricted S (marked S slot) I J then 1 else 0 := by
  rw [← labelled_reindex S slot hinj (fun a => ∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
    kernelOn S (fun P => forwardFactor (a P)) d.1 d.2*
    kernelOn S (fun _P => ordinarySeries) (cofactorPair I J d).1 (cofactorPair I J d).2)]
  exact forward_restricted_identity S (marked S slot) hI hJ hs

/-- Freezing T leaves exactly the complementary labels live in the residual. -/
theorem inverse_labelled_identity (S : Finset PrimeIdeal) (slot : α → S)
    (hinj : Function.Injective slot) {I J : Id} (hI : I ≠ 0) (hJ : J ≠ 0)
    (hs : pairSupport I J ⊆ primeValues S) :
    (∑ T : Finset α, ∑ d ∈ idealDivisors I ×ˢ idealDivisors J,
      kernelOn S (fun P => inverseFactor (frozen S slot T P)) d.1 d.2*
      kernelOn S (fun P => if frozen S slot Tᶜ P then 1 else truncatedSeries)
        (cofactorPair I J d).1 (cofactorPair I J d).2) = 1 := by
  have h := inverse_allocated_identity S (marked S slot) hI hJ hs
  rw [labelled_reindex S slot hinj] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro T hT
  have he := live_complement S slot hinj T
  simp only [inverseResidual]
  have hp (P : S) : (marked S slot P && !frozen S slot T P) = frozen S slot Tᶜ P := congrFun he P
  simp_rw [hp]

end
end Candidate.FourthPower.KernelLabelledSlots
