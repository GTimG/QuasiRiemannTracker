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
Original path: DedekindZetaZeroFree/Moments/Probes/Poisson/FrequencySupport.lean
Apache-2.0. Original source/dependency attribution and copyright notices are retained.
Changes: separate Refinement9672 declaration namespace/import cone and successor
scales/endpoint constants. The independent old Hecke baseline remains unchanged.
This work in progress does not yet claim a compiled or admitted .9672 endpoint.
-/
module

public import Submissions.gao_general_number_fields_9672.Refinement9672.DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyDecomposition

@[expose] public section

namespace Refinement9672

open _root_.DedekindZetaZeroFree

namespace DedekindZetaZeroFree.Quantitative.InitialFrequencySupport

noncomputable section

open _root_.DedekindZetaZeroFree
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

end Refinement9672
