/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Weil/PhaseSigns.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData

@[expose] public section

namespace DedekindZetaZeroFree

theorem weil_zeta12_cube_sq (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F) : (A.zeta12 ^ 3) ^ 2 = (-1 : F) := by
  simpa only [← pow_mul] using A.zeta12_pow_six

theorem weil_finite_minus_one_square (F : Type) [Field F] [NumberField F]
    (A : SArithmeticData F)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    (algebraMap F (v.adicCompletion F) (A.zeta12 ^ 3)) ^ 2 =
      (-1 : v.adicCompletion F) := by
  simpa only [map_pow, map_neg, map_one] using
    congrArg (algebraMap F (v.adicCompletion F)) (weil_zeta12_cube_sq F A)

end DedekindZetaZeroFree
