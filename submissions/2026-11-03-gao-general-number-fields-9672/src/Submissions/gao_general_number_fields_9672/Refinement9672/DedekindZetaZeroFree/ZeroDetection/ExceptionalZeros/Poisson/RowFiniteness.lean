/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9672;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/ZeroDetection/ExceptionalZeros/Poisson/RowFiniteness.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRowCount
public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.ZeroDetection.Conductors.Poisson.MaximalSieve

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.DetectRows

noncomputable section

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private theorem heightMax_nonneg (b ω : Ideal (𝓞 F) → ℂ) (N T : ℝ) :
    0 ≤ detectorHeightPrefixMaximum F b ω N T := by
  unfold detectorHeightPrefixMaximum
  apply Real.sSup_nonneg
  rintro v ⟨t, _, rfl⟩
  unfold detectorPrefixMaximum
  apply Real.sSup_nonneg
  rintro v ⟨y, _, rfl⟩
  positivity

open _root_.DedekindZetaZeroFree.Quantitative.DetectorSieve
open DedekindZetaZeroFree.Quantitative.DetectorSieve in

theorem card_dyad (U M T δ : ℝ) (b : Ideal (𝓞 F) → ℂ) :
    {u : D.Row | u.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U ∧
      δ ≤ detectorHeightPrefixMaximum F b (fun J => (D.omega u).character J) M T}.Finite ∧
    (({u : D.Row | u.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U ∧
      δ ≤ detectorHeightPrefixMaximum F b (fun J => (D.omega u).character J) M T}.ncard : ℕ) : ℝ)
      * δ ≤ rowMaximalSum D U M T b := by
  have hdy : ∀ u : D.Row, U ≤ D.q u → D.q u < 2 * U →
      u ∈ PoissonKernel.dyadRows D U := fun u h1 h2 => ⟨h1, h2⟩
  have hfin : {u : D.Row | u.u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U ∧
      δ ≤ detectorHeightPrefixMaximum F b (fun J => (D.omega u).character J) M T}.Finite :=
    (ActualRowCount.dyadRows_finite D U).subset (fun u hu => hdy u hu.2.1 hu.2.2.1)
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have hsum : rowMaximalSum D U M T b = ∑ u ∈ (ActualRowCount.dyadRows_finite D U).toFinset,
      (if FixedData.Row.u u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U then
        detectorHeightPrefixMaximum F b (fun J => (D.omega u).character J) M T else 0) := by
    unfold rowMaximalSum
    apply finsum_eq_sum_of_support_subset
    intro u hu
    rw [Function.mem_support] at hu
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    split_ifs at hu with hc
    · exact hdy u hc.2.1 hc.2.2
    · exact absurd rfl hu
  rw [hsum]
  calc ((hfin.toFinset.card : ℕ) : ℝ) * δ = ∑ u ∈ hfin.toFinset, δ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ u ∈ hfin.toFinset,
        (if FixedData.Row.u u ≠ 1 ∧ U ≤ D.q u ∧ D.q u < 2 * U then
          detectorHeightPrefixMaximum F b (fun J => (D.omega u).character J) M T else 0) := by
        apply Finset.sum_le_sum
        intro u hu
        rw [Set.Finite.mem_toFinset] at hu
        split_ifs with hc
        · exact hu.2.2.2
        · exact absurd ⟨hu.1, hu.2.1, hu.2.2.1⟩ hc
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro u hu
          rw [Set.Finite.mem_toFinset] at hu
          exact (ActualRowCount.dyadRows_finite D U).mem_toFinset.mpr (hdy u hu.2.1 hu.2.2.1)
        · intro u _ _
          split_ifs
          · exact heightMax_nonneg _ _ _ _
          · exact le_rfl

theorem dyadRows_finite (U : ℝ) : (PoissonKernel.dyadRows D U).Finite :=
  ActualRowCount.dyadRows_finite D U

end

end DedekindZetaZeroFree.Quantitative.DetectRows

end Refinement9672
