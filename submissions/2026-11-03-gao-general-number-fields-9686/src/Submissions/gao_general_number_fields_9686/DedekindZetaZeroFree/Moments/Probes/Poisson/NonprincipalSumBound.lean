/-
2026-11-03 frozen baseline packaging by Zhongpai Gao (https://github.com/Gaozhongpai).
This support module retains the registered PR #114 native source at 09afbb4ce6570c1615d58509dc197fc9f0956b7d,
whose endpoint is 31/32. The separate Refinement9672 namespace supplies the new candidate.
Only local module import paths are relocated under Submissions.gao_general_number_fields_9686.
Original declaration namespaces and source attribution are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Moments/Probes/Poisson/NonprincipalSumBound.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencySumBound

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.OmittedProbeBound

open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem omittedSum_bound (D : FixedData S η) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖PoissonFrequencyDecomposition.omittedSum D Z‖ ≤ C * Z ^ (717 / 2000 : ℝ) :=
  RawOmittedRowsAssembly31.rawOmittedSum_bound D

end DedekindZetaZeroFree.Quantitative.OmittedProbeBound
