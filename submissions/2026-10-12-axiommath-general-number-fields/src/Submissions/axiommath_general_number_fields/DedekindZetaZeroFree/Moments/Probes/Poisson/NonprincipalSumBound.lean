/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Moments/Probes/Poisson/NonprincipalSumBound.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencySumBound

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
