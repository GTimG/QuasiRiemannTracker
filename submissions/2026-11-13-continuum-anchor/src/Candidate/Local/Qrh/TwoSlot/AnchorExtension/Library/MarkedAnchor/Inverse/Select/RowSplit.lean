/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Descent.Canonical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Mellin.UniformKernelBounds

/-!
# Inverse.Select.RowSplit

The fourth-power selection identity on the canonical row. For a set `R` of selected slots whose
lists lie in `E` while the other slots avoid `E`, every squarefree column `U ⊆ pool` splits as
`U = D ∪ U'` with `D ⊆ pool ∩ E`, `U' ⊆ pool \ E`, and the exact Gauss identity
`γ₂(U' ∪ D) = γ₂(U') γ₂(D) χ_{U'}(D)^4` moves `D` into the row `k D^4` (the zero
`χ_{U'}(D) = 0` for `(U', D) ≠ 1` is preserved):

  `finiteCanonicalMarkedRow pool Ψ m f k slots lists a W X =`
  `  ∑_{D ⊆ pool ∩ E} selectedCoefficient D *`
  `    finiteCanonicalMarkedRow (pool \ E) Ψ m f (k (∏_D p)^4) (slots \ R) lists a (W(N D · ·)) X`

with `selectedCoefficient D = γ₂(D) Ψ(D) mask_D(m) χ_D(f)^4 χ_D(k) mark_R(D)`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped BigOperators Classical
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths OAI.SevenEighths.InverseMoment

local notation "O" => OAI.ActualEisensteinCubic.O

section
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

/-- The selected central coefficient. -/
def selectedCoefficient (Ψ : O →* ℂ) (m f k : O) (R : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (D : Finset ι) : ℂ :=
  SecondPassArithmetic.secondChildColumn p hp hcop hg Ψ m f k
    (fun U => primeMark R lists a U) D

omit [DecidableEq ι] in
theorem row_pow_four (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i) (S : Finset ι) (x : O) (n : ℕ) :
    finiteSquarefreeRow P hgood S (x^n) = (finiteSquarefreeRow P hgood S x)^n := by
  simp only [finiteSquarefreeRow, map_pow, Finset.prod_pow]

/-- The mark of `D ∪ U'` splits along the selection. -/
theorem primeMark_split (slots R : Finset σ) (hR : R ⊆ slots) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (E : Finset ι) (hin : ∀ i ∈ R, lists i ⊆ E)
    (hout : ∀ i ∈ slots \ R, Disjoint (lists i) E) (D U : Finset ι) (hD : D ⊆ E)
    (hU : Disjoint U E) :
    primeMark slots lists a (D ∪ U) = primeMark R lists a D * primeMark (slots \ R) lists a U := by
  classical
  unfold primeMark
  rw [← Finset.prod_sdiff hR, mul_comm]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    unfold primeSlot
    apply Finset.sum_congr rfl
    intro x hx
    have hxE : x ∈ E := hin i hi hx
    have hxU : x ∉ U := fun h => Finset.disjoint_left.mp hU h hxE
    simp [Finset.mem_union, hxU]
  · apply Finset.prod_congr rfl
    intro i hi
    unfold primeSlot
    apply Finset.sum_congr rfl
    intro x hx
    have hxE : x ∉ E := Finset.disjoint_left.mp (hout i hi) hx
    have hxD : x ∉ D := fun h => hxE (hD h)
    simp [Finset.mem_union, hxD]

/-- The termwise identity on a split column `D ∪ U'`. -/
theorem secondChildColumn_split
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m f k : O) (slots R : Finset σ) (hR : R ⊆ slots) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (E : Finset ι) (hin : ∀ i ∈ R, lists i ⊆ E)
    (hout : ∀ i ∈ slots \ R, Disjoint (lists i) E) (W : ℝ → ℂ) (X : ℝ)
    (D U : Finset ι) (hD : D ⊆ E) (hU : Disjoint U E) :
    SecondPassArithmetic.secondChildColumn p hp hcop hg Ψ m f k
        (fun U => primeMark slots lists a U * W (FirstPassCubeLabels.primeProductNorm p U / X))
        (D ∪ U) =
      selectedCoefficient p hp hcop hg Ψ m f k R lists a D *
      SecondPassArithmetic.secondChildColumn p hp hcop hg Ψ m f (k * (∏ i ∈ D, p i)^4)
        (fun U' => primeMark (slots \ R) lists a U' *
          W (FirstPassCubeLabels.primeProductNorm p D *
            (FirstPassCubeLabels.primeProductNorm p U' / X))) U := by
  have hdisj : Disjoint D U := by
    rw [Finset.disjoint_left]
    intro x hxD hxU
    exact Finset.disjoint_left.mp hU hxU (hD hxD)
  have hA := FirstPassCubeLabels.columnCoefficient_union_row_four p hp hcop hg hpr U D
    hdisj.symm
  rw [Finset.union_comm U D] at hA
  have hmark := primeMark_split slots R hR lists a E hin hout D U hD hU
  have hnorm := FirstPassCubeLabels.primeProductNorm_union p D U hdisj
  have hrow : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U (k * (∏ i ∈ D, p i)^4) =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U k *
        (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U (∏ i ∈ D, p i))^4 := by
    simp only [finiteSquarefreeRow, map_mul, map_pow, Finset.prod_mul_distrib, Finset.prod_pow]
  unfold selectedCoefficient SecondPassArithmetic.secondChildColumn
  simp only [hA, hmark, hnorm, hrow, Finset.prod_union hdisj, map_mul,
    FirstPassCubeLabels.row_union _ hg D U hdisj, FirstPassCubeLabels.mask_union _ hg D U hdisj,
    mul_div_assoc, mul_pow]
  ring

/-- The termwise identity on a split column `D ∪ U` for a general column weight `G` (no
assumption on the lists: used with the injective mark). -/
theorem secondChildColumn_split_gen
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (Ψ : O →* ℂ) (m f k : O) (lists : σ → Finset ι) (a : σ → ι → ℂ) (G : Finset ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (D U : Finset ι) (hdisj : Disjoint D U) :
    SecondPassArithmetic.secondChildColumn p hp hcop hg Ψ m f k
        (fun U => G U * W (FirstPassCubeLabels.primeProductNorm p U / X)) (D ∪ U) =
      selectedCoefficient p hp hcop hg Ψ m f k (∅ : Finset σ) lists a D *
      SecondPassArithmetic.secondChildColumn p hp hcop hg Ψ m f (k * (∏ i ∈ D, p i)^4)
        (fun U' => G (D ∪ U') *
          W (FirstPassCubeLabels.primeProductNorm p D *
            (FirstPassCubeLabels.primeProductNorm p U' / X))) U := by
  have hA := FirstPassCubeLabels.columnCoefficient_union_row_four p hp hcop hg hpr U D
    hdisj.symm
  rw [Finset.union_comm U D] at hA
  have hnorm := FirstPassCubeLabels.primeProductNorm_union p D U hdisj
  have hrow : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U (k * (∏ i ∈ D, p i)^4) =
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U k *
        (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U (∏ i ∈ D, p i))^4 := by
    simp only [finiteSquarefreeRow, map_mul, map_pow, Finset.prod_mul_distrib, Finset.prod_pow]
  unfold selectedCoefficient SecondPassArithmetic.secondChildColumn
  simp only [hA, hnorm, hrow, Finset.prod_union hdisj, map_mul,
    FirstPassCubeLabels.row_union _ hg D U hdisj, FirstPassCubeLabels.mask_union _ hg D U hdisj,
    mul_div_assoc, mul_pow, primeMark_empty]
  ring

/-- The selection identity on the canonical marked row. -/
theorem canonical_row_select
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O) (slots R : Finset σ) (hR : R ⊆ slots)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (E : Finset ι) (hin : ∀ i ∈ R, lists i ⊆ E)
    (hout : ∀ i ∈ slots \ R, Disjoint (lists i) E) (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X =
      ∑ D ∈ (pool.filter (· ∈ E)).powerset,
        selectedCoefficient p hp hcop hg Ψ m f k R lists a D *
        finiteCanonicalMarkedRow p hp hcop hg (pool.filter (· ∉ E)) Ψ m f
          (k * (∏ i ∈ D, p i)^4) (slots \ R) lists a
          (fun x => W (FirstPassCubeLabels.primeProductNorm p D * x)) X := by
  unfold finiteCanonicalMarkedRow SecondPassArithmetic.fixedChildRow
  simp only [Finset.mul_sum]
  rw [← Finset.sum_product']
  symm
  apply Finset.sum_nbij' (fun x => x.1 ∪ x.2)
    (fun U => (U.filter (· ∈ E), U.filter (· ∉ E)))
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_powerset] at hx ⊢
    exact Finset.union_subset (hx.1.trans (Finset.filter_subset _ _))
      (hx.2.trans (Finset.filter_subset _ _))
  · intro U hU
    simp only [Finset.mem_product, Finset.mem_powerset] at hU ⊢
    exact ⟨Finset.filter_subset_filter _ hU, Finset.filter_subset_filter _ hU⟩
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_powerset] at hx
    have h1 : ∀ y ∈ x.1, y ∈ E := fun y hy => (Finset.mem_filter.mp (hx.1 hy)).2
    have h2 : ∀ y ∈ x.2, y ∉ E := fun y hy => (Finset.mem_filter.mp (hx.2 hy)).2
    ext y
    · simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hy | hy, hyE⟩
        · exact hy
        · exact absurd hyE (h2 y hy)
      · intro hy; exact ⟨Or.inl hy, h1 y hy⟩
    · simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hy | hy, hyE⟩
        · exact absurd (h1 y hy) hyE
        · exact hy
      · intro hy; exact ⟨Or.inr hy, h2 y hy⟩
  · intro U _
    ext y
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_powerset] at hx
    have hD : x.1 ⊆ E := fun y hy => (Finset.mem_filter.mp (hx.1 hy)).2
    have hU : Disjoint x.2 E := by
      rw [Finset.disjoint_left]
      intro y hy hyE
      exact (Finset.mem_filter.mp (hx.2 hy)).2 hyE
    exact (secondChildColumn_split p hp hcop hg hpr Ψ m f k slots R hR lists a E hin hout W X
      x.1 x.2 hD hU).symm

end

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.canonical_row_select
