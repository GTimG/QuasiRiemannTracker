/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Moments/Probes/Poisson/FrequencySupport.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyDecomposition

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.InitialFrequencySupport

noncomputable section

open DedekindZetaZeroFree NumberField
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem initial_all_frequency_partition (D : FixedData S η) (Z : ℝ) (hZ : 0 < Z) :
    D.Iscale Z = ∑' u : D.Row, PoissonFrequencyDecomposition.rowIntegral D u Z +
      PoissonFrequencyDecomposition.omittedSum D Z :=
  (PoissonFrequencyDecomposition.Iscale_eq_rows_add_omitted D Z hZ).2.2.2.2.2.2.2.2

end

end DedekindZetaZeroFree.Quantitative.InitialFrequencySupport
