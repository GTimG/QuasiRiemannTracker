/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Interface.Contract
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.ReferenceBridge
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Marked.DeletionOverlapSlots

/-!
# Inverse.Restore.Collide — injective slot moments from full slot moments

The restored child is an INJECTIVE (marked-squarefree) slot product; the child source
(the contract `InverseRectAt`, overlapping pools allowed) bounds FULL products `∏ directSlot` of every
sub-collection of the slots. HC `Collision.projectedSubsetBound_of_fullSubsetBound` (exact
inclusion-exclusion over collision partitions) converts:

**`inj_le_full_energy`**: if every sub-embedding `J ↪ ι` has full moment `≤ E`, the injective
moment `injSlots` is `≤ collisionProjectionCost 1 256 K · E` (`#ι ≤ K`, coefficients `≤ 1`,
pools in `[1, 2X]`-norm windows). Mirror of `Chain.full_le_inj_energy`; `injSlots` is the same
term as `Chain.injDirectSlots` (defined here so that the restoration does not import `Chain`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Restore
noncomputable section

open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-- The injective product of normalized prime slots (only tuples of distinct primes). -/
def injSlots (u : O) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (X : ι → ℝ) : ℂ :=
  ∑ x ∈ Fintype.piFinset L, if Function.Injective x then
    ∏ i, CanonicalRowCompletion.idealRowHom u (x i) *
      Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
        (L i) (β i) (X i) (x i) else 0

/-- HC's `injectiveTuplePolynomial` over atoms containing all pools is the tuple sum. -/
theorem injTuple_atoms' {I : Type} [Fintype I] (atoms : Finset (Ideal O))
    (L : I → Finset (Ideal O)) (hL : ∀ i, L i ⊆ atoms) (c : I → Ideal O → ℂ)
    (hc : ∀ i p, p ∉ L i → c i p = 0) :
    Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.injectiveTuplePolynomial
        (fun i (p : atoms) => c i p.val) =
      ∑ x ∈ Fintype.piFinset L, if Function.Injective x then ∏ i, c i (x i) else 0 := by
  unfold Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.injectiveTuplePolynomial
  have hinj (x : I → atoms) : Function.Injective x ↔ Function.Injective (fun j => (x j).val) :=
    ⟨fun h => Subtype.val_injective.comp h, fun h a b hab => h (congrArg Subtype.val hab)⟩
  refine Finset.sum_bij_ne_zero (fun x _ _ => fun j => (x j).val) ?_ ?_ ?_ ?_
  · intro x _ hx
    rw [Fintype.mem_piFinset]
    intro j
    by_contra hj
    apply hx
    split_ifs
    · exact Finset.prod_eq_zero (Finset.mem_univ j) (hc j _ hj)
    · rfl
  · intro x _ _ y _ _ hxy
    funext j
    exact Subtype.ext (congrFun hxy j)
  · intro y hy hy0
    have hmem := Fintype.mem_piFinset.mp hy
    refine ⟨fun j => ⟨y j, hL j (hmem j)⟩, Finset.mem_univ _, ?_, rfl⟩
    by_cases hyi : Function.Injective y
    · rw [if_pos hyi] at hy0
      rw [if_pos ((hinj _).mpr hyi)]
      exact hy0
    · rw [if_neg hyi] at hy0
      exact absurd rfl hy0
  · intro x _ _
    by_cases h : Function.Injective x
    · rw [if_pos h, if_pos ((hinj x).mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((hinj x).mpr h'))]

/-- **Injective ⇐ full.** The injective slot moment is bounded by
`collisionProjectionCost 1 256 K` times a bound for the full moments of all sub-embeddings. -/
theorem inj_le_full_energy {ι : Type} [Fintype ι] [DecidableEq ι] {Row : Type}
    (rows : Finset Row) (uu : Row → O) (D : Row → ℂ) (L : ι → Finset (Ideal O))
    (β : ι → Ideal O → ℂ) (X : ι → ℝ) (E : ℝ) (hE : 0 ≤ E) (K : ℕ)
    (hK : Fintype.card ι ≤ K) (hX : ∀ i, 1 ≤ X i) (hβ : ∀ i, ∀ p ∈ L i, ‖β i p‖ ≤ 1)
    (hp : ∀ i, ∀ p ∈ L i, p ≠ 0) (hN : ∀ i, ∀ p ∈ L i, (p.absNorm : ℝ) ≤ 2 * X i)
    (hfull : ∀ (J : Type) [Fintype J] (f : J ↪ ι),
      (∑ v ∈ rows, ‖D v * ∏ j, directSlot (uu v) (L (f j)) (β (f j)) (X (f j))‖^2) ≤ E) :
    (∑ v ∈ rows, ‖D v * injSlots (uu v) L β X‖^2) ≤
      QRH.Record1252270103Source.Collision.collisionProjectionCost 1 256 K * E := by
  let atoms : Finset (Ideal O) := Finset.univ.biUnion L
  have hLa (i : ι) : L i ⊆ atoms := fun p hp' => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hp'⟩
  let a : Row → ι → atoms → ℂ := fun v i p => CanonicalRowCompletion.idealRowHom (uu v) p.val *
    Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
      (L i) (β i) (X i) p.val
  let w : ι → atoms → ℝ := fun i p =>
    ‖Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
      (L i) (β i) (X i) p.val‖
  have hfullS : QRH.Record1252270103Source.Collision.fullSubsetBound rows a D E := by
    intro J _ f
    refine le_of_eq_of_le ?_ (hfull J f)
    apply Finset.sum_congr rfl
    intro v _
    congr 3
    apply Finset.prod_congr rfl
    intro j _
    exact (Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.directPrimeSlot_sum_atoms
      (uu v) (L (f j)) atoms (β (f j)) (X (f j)) (hLa (f j))).symm
  have hproj := QRH.Record1252270103Source.Collision.projectedSubsetBound_of_fullSubsetBound
    rows a w D 1 256 E le_rfl (by norm_num) hE (fun _ _ => norm_nonneg _)
    (fun i p => Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff_bound
      (L i) (β i) (X i) 1 (hX i) zero_le_one (hβ i) p.val) ?_ ?_ K hK hfullS
  · have h := hproj ι (Function.Embedding.refl ι)
    refine le_of_eq_of_le ?_ h
    apply Finset.sum_congr rfl
    intro v _
    congr 3
    unfold injSlots
    convert (injTuple_atoms' atoms L hLa
      (fun j p => CanonicalRowCompletion.idealRowHom (uu v) p *
        Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
          (L j) (β j) (X j) p)
      (fun j p hpj => by
        simp [Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff,
          hpj])).symm
    rfl
  · intro i
    dsimp only [w]
    rw [Finset.sum_coe_sort atoms (fun p => ‖Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff
      (L i) (β i) (X i) p‖^2)]
    exact Record1252270103Bootstrap.PR67.OAI.SevenEighths.Deletion26.normalizedPrimeCoeff_energy
      atoms (L i) (β i) (X i) 1 (hX i) zero_le_one (hβ i) (hp i) (hN i)
  · intro v _ i p
    dsimp only [a, w]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (CanonicalRowCompletion.idealRowHom_norm _ _)

end
end Qrh.MarkedAnchor.Inverse.Restore

#print axioms Qrh.MarkedAnchor.Inverse.Restore.inj_le_full_energy
