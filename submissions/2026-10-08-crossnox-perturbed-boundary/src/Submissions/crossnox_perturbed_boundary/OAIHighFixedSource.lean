/-
Source: CrossNox/quasi-riemann-hypothesis-extension, commit
3dddb77a62182f8d530c368ed5e9220079fbd1b9, lean/OAIHighFixedSource.lean.
Apache-2.0; see the repository LICENSE and tracker NOTICE.
Adapted for QuasiRiemannTracker on 2026-11-03: import paths relocated;
the original theorem bodies and declaration namespaces are preserved.
-/
import Submissions.crossnox_perturbed_boundary.OAIHighFiniteProductX
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.ParametersFixedSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.MarkedExclusions

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.Parameters

open ProbePhysical ProbeHighRowFamily ProbeEuler CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem exists_fixed_source_on_perturbed_boundary
    (e : ℝ) (he : 0 < e)
    (S₀ : Finset (Ideal O)) (hS₀ : ∀ P ∈ S₀, Prime P) :
    ∃ S : Finset (Ideal O), S₀ ⊆ S ∧ SourceExclusions S ∧
      FirstTail (4 * e) S ∧ PerturbedCorrectionTail S ∧
      (∀ P ∈ S, P.IsMaximal) := by
  obtain ⟨S₁, hsub, hS₁, hfirst, _⟩ := exists_fixed_source e he S₀ hS₀
  obtain ⟨N, hN, hcut⟩ := exists_uniform_perturbed_global_cutoff
  let S := S₁ ∪ smallPrimeSet N
  have hpS : ∀ P ∈ S, Prime P := by
    intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact hS₁.prime P hP
    · exact (Finset.mem_filter.mp hP).2
  have htail : PerturbedCorrectionTail S := by
    apply hcut
    intro P hP
    exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)
  refine ⟨S, hsub.trans Finset.subset_union_left,
    ⟨hpS, hS₁.bad.trans Finset.subset_union_left, htail.to_source⟩,
    firstTail_mono hfirst Finset.subset_union_left, htail, ?_⟩
  intro P hP
  exact (Ideal.isPrime_of_prime (hpS P hP)).isMaximal (hpS P hP).ne_zero

end SevenEighths.Parameters

end

end OAI
