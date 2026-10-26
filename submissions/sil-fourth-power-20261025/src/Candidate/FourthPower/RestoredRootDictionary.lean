/- Copyright (c) 2026 Sil. Apache-2.0.
Exact root dictionaries for the ordinary-source restoration family.
No moment, source or energy estimate is assumed or concluded here.
-/
import Candidate.FourthPower.NativeMaskedEnergy
import Candidate.FourthPower.MixedCanonicalSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FixedRowMask
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.UncenteredTerminal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RestoredRootDictionary
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open QRH.Record1252270103KernelMass QRH.Record1252270103TwoIdeal
open CenteredMomentCommonMaskEnergy CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorEnergyInitialState CenteredMomentFixedRowMask
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentSourceMass CenteredMomentUncenteredTerminal
open KernelCollisionEnergy KernelAssignmentReindex KernelLabelledSlots
open KernelMarkedRows KernelNaturalSlots KernelRowExpansion KernelRowProfiles KernelRowPools KernelRestrictedState
open RestorationFamily RestorationCollisionEnergy NativeFiniteHoles NativeMaskedEnergy
open MixedCanonicalSource MixedCompletedRows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _

variable {α : Type*} [Fintype α]

abbrev Remaining (r : Setoid α) (A : Finset {q // singletonBlock r q}) :=
  {q : {q // singletonBlock r q} // q ∉ A}

/-- Surviving singleton labels embed into the original fixed slot type. -/
def remainingEmbedding (r : Setoid α) (A : Finset {q // singletonBlock r q}) :
    Remaining r A ↪ α where
  toFun q := singletonRepresentative r q.val
  inj' := fun q q' h => Subtype.ext (singletonRepresentative_injective r h)

def remainingSet (r : Setoid α) (A : Finset {q // singletonBlock r q}) : Finset α :=
  Finset.univ.map (remainingEmbedding r A)

def remainingEquiv (r : Setoid α) (A : Finset {q // singletonBlock r q}) :
    Remaining r A ≃ remainingSet r A :=
  Equiv.ofBijective (fun q => ⟨remainingEmbedding r A q,
    Finset.mem_map.mpr ⟨q, Finset.mem_univ _, rfl⟩⟩) (by
      constructor
      · intro q q' h
        exact (remainingEmbedding r A).injective (congrArg Subtype.val h)
      · intro i
        obtain ⟨q, _, hq⟩ := Finset.mem_map.mp i.property
        exact ⟨q, Subtype.ext hq⟩)

theorem remainingEquiv_val (r : Setoid α) (A : Finset {q // singletonBlock r q})
    (q : Remaining r A) :
    (remainingEquiv r A q).val = singletonRepresentative r q.val := rfl

theorem remainingEquiv_symm_val (r : Setoid α)
    (A : Finset {q // singletonBlock r q}) (i : remainingSet r A) :
    singletonRepresentative r ((remainingEquiv r A).symm i).val = i.val := by
  exact congrArg Subtype.val ((remainingEquiv r A).apply_symm_apply i)

theorem remaining_card (r : Setoid α) (A : Finset {q // singletonBlock r q}) :
    (remainingSet r A).card ≤ Fintype.card α :=
  (Finset.card_le_univ _)

theorem remaining_sum (r : Setoid α) (A : Finset {q // singletonBlock r q})
    (w : α → ℝ) :
    (∑ q : Remaining r A, w (singletonRepresentative r q.val)) =
      ∑ i ∈ remainingSet r A, w i := by
  rw [←Finset.sum_coe_sort (remainingSet r A) w]
  exact (remainingEquiv r A).sum_comp (fun i => w i.val)

theorem remaining_sum_le (r : Setoid α) (A : Finset {q // singletonBlock r q})
    (w : α → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ q : Remaining r A, w (singletonRepresentative r q.val)) ≤ ∑ i, w i := by
  rw [remaining_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => hw i)

/-- The old exact two-mask identity commutes with the common physical
height. The holes remain marked-coefficient holes only. -/
theorem restoration_height_coefficients (r : Setoid α) (S : Finset PrimeIdeal)
    (tc : {q // ¬singletonBlock r q} → S)
    (A : Finset {q // singletonBlock r q}) (ti : A → S)
    (β : α → Id → ℂ) (t : ℝ) :
    crossBeta A S ti (collisionBeta r S tc (fun i => heightCoefficient (β i) t)) =
      fun q : Remaining r A => heightCoefficient
        (holeCoefficient (fun j : Remaining r A => β (singletonRepresentative r j.val))
          (fun _ => restorationHoles r S tc A ti) q) t := by
  rw [restoration_coefficients]
  funext q I
  by_cases h : I ∈ restorationHoles r S tc A ti <;>
    simp only [holeCoefficient, heightCoefficient, h, ite_true, ite_false, zero_mul]

/-- Concrete specialization: the original character, annular coefficient,
both restoration masks and common height become literal canonical slots. -/
theorem restoration_canonical_coefficients (r : Setoid α) (S : Finset PrimeIdeal)
    (tc : {q // ¬singletonBlock r q} → S)
    (A : Finset {q // singletonBlock r q}) (ti : A → S)
    (ν : α → Character) (W : ℝ → ℂ) (P σ v : α → ℝ) (t : ℝ) :
    crossBeta A S ti (collisionBeta r S tc (fun i => heightCoefficient
      (fun I => idealCoeff (ν i) I * HeckePrimeAnnular.annularWeight W (P i) (σ i) (v i) I) t)) =
      fun q : Remaining r A => fun I =>
        slotCoefficient (fun j : Remaining r A => ν (singletonRepresentative r j.val))
          (fun _ => restorationHoles r S tc A ti) t q I *
        slotProfile W (σ (singletonRepresentative r q.val)) (v (singletonRepresentative r q.val))
          (I.absNorm / P (singletonRepresentative r q.val)) := by
  rw [restoration_height_coefficients]
  funext q I
  exact (slot_coefficient_identity
    (fun j : Remaining r A => ν (singletonRepresentative r j.val))
    (fun _ => restorationHoles r S tc A ti) W
    (fun j => P (singletonRepresentative r j.val))
    (fun j => σ (singletonRepresentative r j.val))
    (fun j => v (singletonRepresentative r j.val)) t q I).symm

section Reindex
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem marked_reindex (e : ι ≃ κ) (S : Finset PrimeIdeal) (slot : ι → S) :
    marked S (fun j => slot (e.symm j)) = marked S slot := by
  funext P
  apply Bool.eq_iff_iff.mpr
  simp only [marked_true]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨e.symm j, hj⟩
  · rintro ⟨i, hi⟩
    exact ⟨e i, by simpa only [e.symm_apply_apply] using hi⟩

/-- The whole restricted row is reindexed before taking a norm. -/
theorem row_reindex (e : ι ≃ κ) (inv : Bool) (S : Finset PrimeIdeal) (χ : Character)
    (pool : κ → Finset Id) (β : κ → Id → ℂ) (P : κ → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) :
    row inv S χ (fun i => pool (e i)) (fun i => β (e i)) (fun i => P (e i))
      W₁ W₂ b X₁ X₂ = row inv S χ pool β P W₁ W₂ b X₁ X₂ := by
  unfold row weightedSum
  apply Finset.sum_bij (fun slot _ => fun j => slot (e.symm j))
  · intro slot _
    exact Finset.mem_univ _
  · intro slot _ slot' _ h
    funext i
    have he := congrFun h (e i)
    simpa only [e.symm_apply_apply] using he
  · intro slot _
    refine ⟨fun i => slot (e i), Finset.mem_univ _, ?_⟩
    funext j
    exact congrArg slot (e.apply_symm_apply j)
  · intro slot _
    have hinj : Function.Injective (fun j => slot (e.symm j)) ↔ Function.Injective slot := by
      constructor
      · intro h i i' hii'
        apply e.injective
        apply h
        simpa only [e.symm_apply_apply] using hii'
      · intro h
        exact h.comp e.symm.injective
    have hkernel : sourceValue inv S (fun j => slot (e.symm j)) = sourceValue inv S slot := by
      unfold sourceValue
      rw [marked_reindex]
    have hprod : (∏ i, naturalCoefficients χ S pool β P (e i) (slot i)) =
        ∏ j, naturalCoefficients χ S pool β P j (slot (e.symm j)) := by
      simpa only [e.symm_apply_apply] using
        e.prod_comp (fun j => naturalCoefficients χ S pool β P j (slot (e.symm j)))
    simp only [hinj, hkernel]
    by_cases hi : Function.Injective slot
    · simp only [hi, ite_true]
      change _ * (∏ i, naturalCoefficients χ S pool β P (e i) (slot i)) = _
      rw [hprod]
    · simp only [hi, ite_false]
end Reindex

/-- Complete root-row dictionary on a subset of the ORIGINAL ambient
slots. The only deleted values are the explicit two restoration families. -/
theorem restored_row_on_original_subset (r : Setoid α) (S : Finset PrimeIdeal)
    (tc : {q // ¬singletonBlock r q} → S)
    (A : Finset {q // singletonBlock r q}) (ti : A → S)
    (χ : Character) (pool : α → Finset Id) (ν : α → Character)
    (W : ℝ → ℂ) (P σ v : α → ℝ) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) :
    row false S χ (fun q : Remaining r A => pool (singletonRepresentative r q.val))
      (crossBeta A S ti (collisionBeta r S tc (fun i => heightCoefficient
        (fun I => idealCoeff (ν i) I * HeckePrimeAnnular.annularWeight W (P i) (σ i) (v i) I) t)))
      (fun q => P (singletonRepresentative r q.val)) W₁ W₂ b X₁ X₂ =
    row false S χ (fun i : remainingSet r A => pool i.val)
      (fun i I => slotCoefficient (fun j : remainingSet r A => ν j.val)
        (fun _ => restorationHoles r S tc A ti) t i I *
        slotProfile W (σ i.val) (v i.val) (I.absNorm / P i.val))
      (fun i => P i.val) W₁ W₂ b X₁ X₂ := by
  rw [restoration_canonical_coefficients]
  exact row_reindex (remainingEquiv r A) false S χ
    (fun i : remainingSet r A => pool i.val)
    (fun i I => slotCoefficient (fun j : remainingSet r A => ν j.val)
      (fun _ => restorationHoles r S tc A ti) t i I *
      slotProfile W (σ i.val) (v i.val) (I.absNorm / P i.val))
    (fun i => P i.val) W₁ W₂ b X₁ X₂

/-- The actual initial keep has precisely the bare fixed-bad-mask gate;
we do not identify a chosen generator of the unit ideal with 1. -/
theorem initial_keep_iff (η : Character) (Q : Id) (z : O) :
    initialKeep η Q z ↔ z ≠ 0 ∧ ¬FixedInducingRow η Q fixedBadMask 1 z := by
  by_cases hz : z = 0
  · simp only [initialKeep, hz, ne_eq, not_true_eq_false, false_and]
  · have hmask := fixedInducingRow_mul_mask_iff η Q fixedBadMask (idealGenerator 1) 1 z
      fixedBadMask_ne_zero (idealGenerator_ne_zero 1 one_ne_zero) one_ne_zero hz
      (dvd_mul_right _ _) (dvd_mul_left _ _)
    simp only [initialKeep, hmask]

/-- The literal finite ordinary domain is empty. This is stronger than
a coefficient bound and leaves every normalization and marked mask intact. -/
theorem supported_rectangle_empty (S : Finset PrimeIdeal) (b X₁ X₂ : ℝ)
    (hsmall : b*X₁ < 1 ∨ b*X₂ < 1) : supportedRectangle S b X₁ X₂ = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have hr := (Finset.mem_filter.mp hn).1
  obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp hr
  have hn₁ := (mem_idealBall _ _).mp h₁
  have hn₂ := (mem_idealBall _ _).mp h₂
  rcases hsmall with hsmall | hsmall
  · exact (not_lt_of_ge ((ideal_norm_one_le hn₁.1).trans hn₁.2)) hsmall
  · exact (not_lt_of_ge ((ideal_norm_one_le hn₂.1).trans hn₂.2)) hsmall

theorem literal_row_small (inv : Bool) (S : Finset PrimeIdeal) (χ : Character)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ)
    (hsmall : b*X₁ < 1 ∨ b*X₂ < 1) :
    row inv S χ pool β P W₁ W₂ b X₁ X₂ = 0 := by
  unfold row
  rw [supported_rectangle_empty S b X₁ X₂ hsmall]
  simp only [weightedSum, normalizedRow, Finset.sum_empty, mul_zero, ite_self,
    zero_mul, Finset.sum_const_zero]

theorem literal_row_comparison_small (inv : Bool) (S : Finset PrimeIdeal) (χ : Character)
    (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) (hb : 0 ≤ b)
    (hsmall : X₁ ≤ comparisonScale b ∨ X₂ ≤ comparisonScale b) :
    row inv S χ pool β P W₁ W₂ b X₁ X₂ = 0 := by
  have hm : 0 < max (1:ℝ) b := zero_lt_one.trans_le (le_max_left _ _)
  have he : max (1:ℝ) b * comparisonScale b = 1/2 := by
    unfold comparisonScale
    field_simp [hm.ne'] <;> ring
  have hc : b*comparisonScale b ≤ 1/2 := by
    rw [←he]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (comparisonScale_pos b).le
  apply literal_row_small
  rcases hsmall with hsmall | hsmall
  · exact Or.inl (lt_of_le_of_lt ((mul_le_mul_of_nonneg_left hsmall hb).trans hc) (by norm_num))
  · exact Or.inr (lt_of_le_of_lt ((mul_le_mul_of_nonneg_left hsmall hb).trans hc) (by norm_num))

/-- Safe enclosure enlargement for a FIXED marked assignment. No new
prime can become marked, and the global fifth-free condition is identical. -/
theorem source_value_enclosure (S S' : Finset PrimeIdeal) (hSS : S ⊆ S')
    (slot : α → S) (inv : Bool) :
    sourceValue inv S' (fun i => (⟨(slot i).val, hSS (slot i).property⟩ : S')) =
      sourceValue inv S slot := by
  cases inv with
  | true => rfl
  | false =>
    funext n
    have hr : Restricted S' (marked S' (fun i =>
        (⟨(slot i).val, hSS (slot i).property⟩ : S'))) n.1 n.2 ↔
        Restricted S (marked S slot) n.1 n.2 := by
      simpa only [marked, restricted_frozen_labels, Finset.mem_univ, forall_const]
    simp only [sourceValue, Bool.false_eq_true, ite_false, restrictedValue, hr]

/-- Ordinary zero extension is also exact for the fixed marked assignment.
Only the existing off-supported character zeros and actual support enclosure
are used; there is no norm inequality or removal of restrictions. -/
theorem fixed_row_enclosure (S S' : Finset PrimeIdeal) (hSS : S ⊆ S')
    (slot : α → S) (inv : Bool) (χ : Character)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (hoff : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (hS : ∀ I, Supported I → ((I.absNorm:ℝ) ≤ b*X₁ ∨ (I.absNorm:ℝ) ≤ b*X₂) →
      QRH.Record1252270103KernelMass.primeSupport I ⊆ primeValues S) :
    normalizedRow χ (supportedRectangle S b X₁ X₂)
      (sourceValue inv S slot) W₁ W₂ X₁ X₂ =
    normalizedRow χ (supportedRectangle S' b X₁ X₂)
      (sourceValue inv S' (fun i => (⟨(slot i).val, hSS (slot i).property⟩ : S')))
      W₁ W₂ X₁ X₂ := by
  rw [source_value_enclosure S S' hSS slot inv]
  have hvalues : primeValues S ⊆ primeValues S' := by
    intro I hI
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hI
    exact Finset.mem_image.mpr ⟨P, hSS hP, rfl⟩
  calc
    _ = normalizedRow χ (rectangle b X₁ X₂) (sourceValue inv S slot)
        W₁ W₂ X₁ X₂ :=
      (normalized_row_complete χ S (rectangle b X₁ X₂) (sourceValue inv S slot)
        W₁ W₂ b X₁ X₂ hX₁ hX₂ hs₁ hs₂ (Finset.Subset.refl _) hoff hS).symm
    _ = _ := normalized_row_complete χ S' (rectangle b X₁ X₂) (sourceValue inv S slot)
      W₁ W₂ b X₁ X₂ hX₁ hX₂ hs₁ hs₂ (Finset.Subset.refl _) hoff
      (fun I hI hlen => (hS I hI hlen).trans hvalues)

/-- Full family zero extension, including the marked assignment sum.
Every extra assignment is zero because a marked value lies outside its
actual pool. The original coefficients and ordinary restrictions survive. -/
theorem row_enclosure (inv : Bool) (S S' : Finset PrimeIdeal) (hSS : S ⊆ S')
    (χ : Character) (pool : α → Finset Id) (β : α → Id → ℂ) (P : α → ℝ)
    (hp : ∀ i, pool i ⊆ primeValues S)
    (W₁ W₂ : ℝ → ℂ) (b X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b)
    (hoff : ∀ I, ¬Supported I → idealCoeff χ I = 0)
    (hS : ∀ I, Supported I → ((I.absNorm:ℝ) ≤ b*X₁ ∨ (I.absNorm:ℝ) ≤ b*X₂) →
      QRH.Record1252270103KernelMass.primeSupport I ⊆ primeValues S) :
    row inv S χ pool β P W₁ W₂ b X₁ X₂ =
      row inv S' χ pool β P W₁ W₂ b X₁ X₂ := by
  let extend : (α → S) → (α → S') := fun slot i => ⟨(slot i).val, hSS (slot i).property⟩
  have hext : Function.Injective extend := by
    intro slot slot' h
    funext i
    apply Subtype.ext
    exact congrArg (fun p : S' => p.val) (congrFun h i)
  let f : (α → S) → ℂ := fun slot => if Function.Injective slot then
    normalizedRow χ (supportedRectangle S b X₁ X₂) (sourceValue inv S slot) W₁ W₂ X₁ X₂ *
      ∏ i, naturalCoefficients χ S pool β P i (slot i) else 0
  let g : (α → S') → ℂ := fun slot => if Function.Injective slot then
    normalizedRow χ (supportedRectangle S' b X₁ X₂) (sourceValue inv S' slot) W₁ W₂ X₁ X₂ *
      ∏ i, naturalCoefficients χ S' pool β P i (slot i) else 0
  have hterm (slot : α → S) : f slot = g (extend slot) := by
    have hi : Function.Injective (extend slot) ↔ Function.Injective slot := by
      constructor
      · intro h i j hij
        apply h
        apply Subtype.ext
        exact congrArg (fun p : S => p.val) hij
      · intro h i j hij
        apply h
        apply Subtype.ext
        exact congrArg (fun p : S' => p.val) hij
    dsimp only [f, g]
    simp only [hi]
    by_cases hinj : Function.Injective slot
    · simp only [hinj, ite_true]
      rw [fixed_row_enclosure S S' hSS slot inv χ W₁ W₂ b X₁ X₂
        hX₁ hX₂ hs₁ hs₂ hoff hS]
      rfl
    · simp only [hinj, ite_false]
  have hfrow : row inv S χ pool β P W₁ W₂ b X₁ X₂ = ∑ slot, f slot := by
    unfold row weightedSum
    apply Finset.sum_congr rfl
    intro slot _
    by_cases hi : Function.Injective slot <;> simp only [f,hi,ite_true,ite_false]
  have hgrow : row inv S' χ pool β P W₁ W₂ b X₁ X₂ = ∑ slot, g slot := by
    unfold row weightedSum
    apply Finset.sum_congr rfl
    intro slot _
    by_cases hi : Function.Injective slot <;> simp only [g,hi,ite_true,ite_false]
  rw [hfrow,hgrow]
  calc
    _ = ∑ slot ∈ (Finset.univ : Finset (α → S)).image extend, g slot := by
      rw [Finset.sum_image]
      · exact Finset.sum_congr rfl (fun slot _ => hterm slot)
      · exact fun slot _ slot' _ h => hext h
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro slot _ hout
      have hpzero : (∏ i, naturalCoefficients χ S' pool β P i (slot i)) = 0 := by
        by_contra hn
        have hcoeff (i : α) : naturalCoefficients χ S' pool β P i (slot i) ≠ 0 :=
          Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ _)
        have hmem (i : α) : (slot i).val ∈ S := by
          have hpool : (slot i).val.val ∈ pool i := by
            by_contra hh
            exact hcoeff i (by simp only [naturalCoefficients, slotTerm, hh, ite_false])
          obtain ⟨Q, hQ, hQi⟩ := Finset.mem_image.mp (hp i hpool)
          exact (Subtype.ext hQi : Q = (slot i).val) ▸ hQ
        let original : α → S := fun i => ⟨(slot i).val, hmem i⟩
        apply hout
        refine Finset.mem_image.mpr ⟨original, Finset.mem_univ _, ?_⟩
        funext i
        exact Subtype.ext rfl
      dsimp only [g]
      rw [hpzero]
      simp only [mul_zero, ite_self]

end
end Candidate.FourthPower.RestoredRootDictionary
