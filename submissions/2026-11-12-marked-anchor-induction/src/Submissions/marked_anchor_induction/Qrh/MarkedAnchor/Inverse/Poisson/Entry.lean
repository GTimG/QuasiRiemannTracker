/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.Grouping
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Poisson.Projector
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.CubicSieve.RowMajorants

/-!
# Inverse.Poisson.Entry — from the selected canonical energy to the physical rows

The sharp Gauss-row ball `0 < ‖k‖² ≤ Z^K'` is majorized by the smooth compactly supported
`rowMajorant(‖k‖²/Z^K')` (baseline `finite_row_energy_le_rowMajorant`), and the grouped
identity (`Grouping.grouped_identity`) is applied label by label:

`selectedEnergy ≤ ∑_{f ∈ labels} D f · Z^(-(N'+V)) · Re ∑_{g} ∑_{a,b ⊆ pool\g, a∩b=∅} groupedTerm g a b`.

Everything after this point is a bound for the explicit physical-row sum `groupedTerm`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Poisson
noncomputable section

open scoped Classical BigOperators SchwartzMap
open OAI OAI.ActualEisensteinCubic OAI.SevenEighths.InverseMoment
open ConcreteTraceCRT (eisEmbedding)
open OAI.FirstPassCubeLabels (primeProductNorm)

local notation "O" => ActualEisensteinCubic.O

variable {ι σ : Type} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The canonical marked row as a column sum of `canonCoeff · χ_U(k)`. -/
theorem canonical_row_eq (pool : Finset ι) (Ψ : O →* ℂ) (m f k : O) (slots : Finset σ)
    (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    canonRowInj p hp hcop hg pool Ψ m f k slots lists a W X =
      ∑ U ∈ pool.powerset, canonCoeff p hp hcop hg Ψ m f
        (fun U => primeMarkInj slots lists a U * W (primeProductNorm p U / X)) U *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U k := by
  unfold canonRowInj SecondPassArithmetic.fixedChildRow
  apply Finset.sum_congr rfl
  intro U _
  exact secondChildColumn_eq p hp hcop hg Ψ m f k _ U

theorem norm_sq_scaled (Z F : ℝ) (hZ : 0 < Z) (x : ℂ) :
    ‖((Z^(-F/2) : ℝ) : ℂ) * x‖^2 = Z^(-F) * ‖x‖^2 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hZ _), mul_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul hZ.le]
  congr 2
  push_cast
  ring

variable (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)

include hinj hc hpr in
/-- Entry of the second Poisson step: the selected canonical energy is bounded by the
normalized label sum of the real parts of the exact physical-row sums. -/
theorem selectedEnergy_le_grouped (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (labels : Finset (Ideal O))
    (D : Ideal O → ℝ) (W : ℝ → ℂ) (Z N' V K' s₀ : ℝ) (hZ : 0 < Z)
    (hD : ∀ f ∈ labels, 0 ≤ D f) :
    selectedEnergy p hp hcop hg pool Ψ m slots lists a labels D W Z N' V K' s₀ ≤
      ∑ f ∈ labels, D f * (Z^(-(N'+V)) *
        (∑ g ∈ pool.powerset, ∑ a' ∈ (pool \ g).powerset, ∑ b' ∈ (pool \ g).powerset,
          if Disjoint a' b' then groupedTerm p hp hcop hg Ψ m (CompletedGauss.primaryGenerator f)
            (fun U => primeMarkInj slots lists a U * childLogTest W s₀ (primeProductNorm p U / Z^N'))
            SecondPassArithmetic.rowMajorant (Z^K') g a' b' else 0).re) := by
  unfold selectedEnergy columnEnergyInj
  apply Finset.sum_le_sum
  intro f hf
  apply mul_le_mul_of_nonneg_left _ (hD f hf)
  simp only [norm_sq_scaled Z (N'+V) hZ]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZ.le _)
  have hY : 0 < Z^K' := Real.rpow_pos_of_pos hZ _
  rw [← grouped_identity p hp hinj hcop hg hc hpr pool Ψ m (CompletedGauss.primaryGenerator f)
    _ SecondPassArithmetic.rowMajorant (Z^K') hY]
  simp only [canonical_row_eq p hp hcop hg]
  apply SecondPassArithmetic.finite_row_energy_le_rowMajorant _ _ _ hY
  intro k hk
  have h := ((mem_nonzeroChildFrequencyBall 1 one_ne_zero (Z^K') k).mp hk).2
  rw [one_mul, eisEmbedding_norm_sq_eq_absNorm_span] at h
  exact h

end
end Qrh.MarkedAnchor.Inverse.Poisson

#print axioms Qrh.MarkedAnchor.Inverse.Poisson.selectedEnergy_le_grouped
#print axioms Qrh.MarkedAnchor.Inverse.Poisson.grouped_identity
#print axioms Qrh.MarkedAnchor.Inverse.Poisson.pair_gauss_identity
#print axioms Qrh.MarkedAnchor.Inverse.Poisson.disjoint_pair_projector
#print axioms Qrh.MarkedAnchor.Inverse.Poisson.prefactor_identities
