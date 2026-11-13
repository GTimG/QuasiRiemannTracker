/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Select.RowSplit
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.InjTuple

/-!
# Inverse.Select.RowTuple — the selection identity in tuple form (the decomposition used by the bound)

The selection takes one MARKED prime per selected slot. With the INJECTIVE mark (the lists may
overlap) the tuple split `InjTuple.markInj_tuple_split`
`markInj_S(U) = ∑_{d inj on R} ∏ a(d_i) · [img d ⊆ U] · markInj_{S\R}(U \ img d)` gives

  `canonRowInj pool Ψ m f k slots lists a W X =`
  `  ∑_{d ∈ injPi R lists} ∏_i a_i(d_i) · selectedCoefficient(img d) ·`
  `    canonRowInj (pool \ img d) Ψ m f (k·(∏_{img d} p)^4) (slots \ R) lists a`
  `      (W(N(img d) · ·)) X`,

where `img d` has exactly one prime per selected slot (`#img d = #R`); the remaining column `U'`
may still contain other primes of the selected lists (free primes). No disjointness is used.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped BigOperators Classical
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths OAI.SevenEighths.InverseMoment

local notation "O" => OAI.ActualEisensteinCubic.O

/-- Summing over the supersets of `T` inside `pool` is summing over `T ∪ U'`, `U' ⊆ pool \ T`. -/
theorem sum_powerset_supersets {ι : Type} [DecidableEq ι] (pool T : Finset ι) (hT : T ⊆ pool)
    (g : Finset ι → ℂ) :
    (∑ U ∈ pool.powerset, if T ⊆ U then g U else 0) =
      ∑ U' ∈ (pool \ T).powerset, g (T ∪ U') := by
  rw [← Finset.sum_filter]
  apply Finset.sum_nbij' (fun U => U \ T) (fun U' => T ∪ U')
  · intro U hU
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hU ⊢
    exact Finset.sdiff_subset_sdiff hU.1 le_rfl
  · intro U' hU'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hU' ⊢
    exact ⟨Finset.union_subset hT (hU'.trans Finset.sdiff_subset), Finset.subset_union_left⟩
  · intro U hU
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hU
    exact Finset.union_sdiff_of_subset hU.2
  · intro U' hU'
    simp only [Finset.mem_coe, Finset.mem_powerset] at hU'
    rw [Finset.union_sdiff_left]
    apply Finset.sdiff_eq_self_of_disjoint
    exact Finset.disjoint_of_subset_left hU' Finset.sdiff_disjoint
  · intro U hU
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hU
    rw [Finset.union_sdiff_of_subset hU.2]

section
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq σ] in
/-- `secondChildColumn` is linear in the column weight. -/
theorem secondChildColumn_mul (Ψ : O →* ℂ) (m f k : O) (c H : Finset ι → ℂ) (U : Finset ι) :
    SecondPassArithmetic.secondChildColumn p hp hcop hg Ψ m f k (fun U => c U * H U) U =
      c U * SecondPassArithmetic.secondChildColumn p hp hcop hg Ψ m f k H U := by
  unfold SecondPassArithmetic.secondChildColumn
  ring

/-- The selection identity in tuple form (injective mark, overlapping lists). -/
theorem canonical_row_select_tuple
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O) (slots R : Finset σ) (hR : R ⊆ slots)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (hpool : ∀ i ∈ R, lists i ⊆ pool)
    (W : ℝ → ℂ) (X : ℝ) :
    canonRowInj p hp hcop hg pool Ψ m f k slots lists a W X =
      ∑ d ∈ injPi R lists, (∏ i ∈ R.attach, a i.1 (d i.1 i.2)) *
        (selectedCoefficient p hp hcop hg Ψ m f k (∅ : Finset σ) lists a (tupleImage R d) *
          canonRowInj p hp hcop hg (pool \ tupleImage R d) Ψ m f
            (k * (∏ i ∈ tupleImage R d, p i)^4) (slots \ R) lists a
            (fun x => W (FirstPassCubeLabels.primeProductNorm p (tupleImage R d) * x)) X) := by
  unfold canonRowInj SecondPassArithmetic.fixedChildRow
  have hcol (U : Finset ι) : SecondPassArithmetic.secondChildColumn p hp hcop hg Ψ m f k
        (fun U => primeMarkInj slots lists a U *
          W (FirstPassCubeLabels.primeProductNorm p U / X)) U =
      ∑ d ∈ injPi R lists, (∏ i ∈ R.attach, a i.1 (d i.1 i.2)) *
        (if tupleImage R d ⊆ U then SecondPassArithmetic.secondChildColumn p hp hcop hg Ψ m f k
          (fun V => primeMarkInj (slots \ R) lists a (V \ tupleImage R d) *
            W (FirstPassCubeLabels.primeProductNorm p V / X)) U else 0) := by
    rw [secondChildColumn_mul p hp hcop hg Ψ m f k (primeMarkInj slots lists a)
      (fun U => W (FirstPassCubeLabels.primeProductNorm p U / X)) U,
      markInj_tuple_split slots lists a U R hR, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [secondChildColumn_mul p hp hcop hg Ψ m f k
      (fun V => primeMarkInj (slots \ R) lists a (V \ tupleImage R d))
      (fun U => W (FirstPassCubeLabels.primeProductNorm p U / X)) U]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun U _ => hcol U), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have himg : tupleImage R d ⊆ pool := tupleImage_subset (injPi_subset _ _ hd) pool hpool
  rw [← Finset.mul_sum, sum_powerset_supersets pool _ himg]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U' hU'
  have hU'd : Disjoint (tupleImage R d) U' :=
    (Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hU') Finset.sdiff_disjoint).symm
  rw [secondChildColumn_split_gen p hp hcop hg hpr Ψ m f k lists a _ W X _ U' hU'd]
  congr 1
  unfold SecondPassArithmetic.secondChildColumn
  simp only [Finset.union_sdiff_cancel_left hU'd]

end

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.canonical_row_select_tuple
