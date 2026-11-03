/-
Tracker adaptation of Gaozhongpai/DedekindZetaZeroFree at 1823f8b90a601a29eda3cded57796e7200f2af9f.
2026-11-03, Zhongpai Gao with AI assistance. Apache-2.0.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686;
native declaration namespaces, proof bodies, and attribution are retained.
Full endpoint compilation and independent verification remain pending.
-/
/-
Successor namespace extension, 2026-11-03, Zhongpai Gao with AI assistance.
Original source: AxiomMath/DedekindZetaZeroFree at09afbb4ce6570c1615d58509dc197fc9f0956b7d;
starting refinement: Gaozhongpai/DedekindZetaZeroFree at829193272c1eaf223bb7228fbfb9003f414808e9.
Original path: DedekindZetaZeroFree/Moments/Probes/Poisson/AllFrequencies/LowContour.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LowZControls
public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LowWControls
public import Submissions.gao_general_number_fields_9686.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.AllFrequencies.LowContourBound

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.RawLowRowContour31

noncomputable section

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree NumberField MeasureTheory Set Filter Complex
open _root_.DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison
open _root_.DedekindZetaZeroFree.Quantitative.RawFixed _root_.DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawFixed.FixedData
open scoped Classical Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem initialRowIntegral_eq_triple (u : Frequency D.recipe) (hu : u ≠ principalFrequency D.recipe)
    (Z : ℝ) (hZ : 0 < Z) :
    initialRowIntegral D u Z = triple D u Scales.rightLine Scales.wLine Scales.zLine Z := by
  rw [← RawLowXiControls31.triple_xi_shift D u hu Z hZ]
  unfold initialRowIntegral triple comparisonVerticalIntegral
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  have hξ : (((4 : ℝ) : ℂ) + (t : ℂ) * I).re = 4 := by simp
  rw [← RawLowWControls31.Iwz_w_shift D u hu Z hZ _ hξ]
  unfold Iwz comparisonVerticalIntegral
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only
  have hw : Scales.wLine ≤ (((4 : ℝ) : ℂ) + (s : ℂ) * I).re ∧
      (((4 : ℝ) : ℂ) + (s : ℂ) * I).re ≤ 4 := by
    simp [Scales.wLine]
    norm_num
  rw [RawLowZControls31.Iz_z_shift D u hu Z hZ _ _ hξ hw]

theorem initialRowIntegral_dyad_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe), u ≠ principalFrequency D.recipe →
      ∀ U : ℝ, 2 ≤ U → U ≤ frequencyNorm D.recipe u → frequencyNorm D.recipe u < 2 * U →
      ∀ Z : ℝ, 2 ≤ Z →
        ‖initialRowIntegral D u Z‖ ≤
          C * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) * U ^ ((1 : ℝ) / 40 + ε) := by
  obtain ⟨C, hC, h⟩ := RawLowRowBound31.raw_low_dyad_bound D ε hε
  refine ⟨C, hC, fun u hu U hU h1 h2 Z hZ => ?_⟩
  rw [initialRowIntegral_eq_triple D u hu Z (by linarith)]
  exact h u hu U hU h1 h2 Z hZ

theorem initialRowIntegral_fixed_bound (u : Frequency D.recipe)
    (hu : u ≠ principalFrequency D.recipe) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖initialRowIntegral D u Z‖ ≤ Cu * Z ^ (Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine) := by
  obtain ⟨Cu, hC, h⟩ := RawLowRowBound31.raw_low_fixed_row_bound D u hu
  refine ⟨Cu, hC, fun Z hZ => ?_⟩
  rw [initialRowIntegral_eq_triple D u hu Z (by linarith)]
  exact h Z hZ

end

end DedekindZetaZeroFree.Quantitative.RawLowRowContour31

end Refinement9672
