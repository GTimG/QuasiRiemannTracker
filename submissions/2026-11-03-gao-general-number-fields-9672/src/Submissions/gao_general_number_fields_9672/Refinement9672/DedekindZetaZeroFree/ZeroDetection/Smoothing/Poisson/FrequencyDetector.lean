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
Original path: DedekindZetaZeroFree/ZeroDetection/Smoothing/Poisson/FrequencyDetector.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.ZeroDetection.ExceptionalZeros.Poisson.FrequencyCount

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.RawDetector31

open _root_.DedekindZetaZeroFree
open DedekindZetaZeroFree NumberField
open _root_.DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison
open _root_.DedekindZetaZeroFree.Quantitative.RawFixed _root_.DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31
open DedekindZetaZeroFree.Quantitative.RawFixed DedekindZetaZeroFree.Quantitative.RawDetectorHeightPrefix31

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem detector_exists (D : FixedData S η) :
    ∃ A ρ : ℝ, 0 ≤ A ∧ RawConvexityExponent D A ∧ HeightSpec D A ρ ∧
      ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
        (FixedData.rawExceptionalSet D ρ U).Finite ∧
          ((FixedData.rawExceptionalSet D ρ U).ncard : ℝ) ≤ C * U ^ DetectorDef.α := by
  obtain ⟨A, ρ, hA, hc, hρ⟩ := height_exists D
  exact ⟨A, ρ, hA, hc, hρ, DedekindZetaZeroFree.Quantitative.RawDetectorCount31.rawExceptionalSet_card D A ρ hA hρ⟩

theorem detector_exists_prefix (D : FixedData S η) :
    ∃ A ρ : ℝ, 0 ≤ A ∧ RawConvexityExponent D A ∧ HeightSpec D A ρ ∧
      (∃ c₁ : ℝ, 0 < c₁ ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
        ∀ u ∈ FixedData.rawExceptionalSet D ρ U, ∀ s : ℂ,
          DetectorDef.IsLZero (FixedData.primMinus D u) s → DetectorDef.σ₀ ≤ s.re → s.re ≤ 1 →
          |s.im| ≤ 4 * U ^ ρ →
          ∃ N y : ℝ, U ^ DetectorDef.qExp / 2 < N ∧ N ≤ U ^ DetectorDef.r' ∧ N ≤ y ∧
            y ≤ 2 * N ∧
            c₁ / Real.log U ≤ ‖DetectorPrefix.prefixSum F U (FixedData.primMinus D u).character
              s.im N y‖) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U →
        (FixedData.rawExceptionalSet D ρ U).Finite ∧
          ((FixedData.rawExceptionalSet D ρ U).ncard : ℝ) ≤ C * U ^ DetectorDef.α := by
  obtain ⟨A, ρ, hA, hc, hρ⟩ := height_exists D
  exact ⟨A, ρ, hA, hc, hρ, detector_prefix D A ρ hρ,
    DedekindZetaZeroFree.Quantitative.RawDetectorCount31.rawExceptionalSet_card D A ρ hA hρ⟩

end DedekindZetaZeroFree.Quantitative.RawDetector31

end Refinement9672
