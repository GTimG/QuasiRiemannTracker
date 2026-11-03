/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LargeSieve/Exponents/QuadraticHeckeExponentOne.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.LargeSieve.Exponents.QuadraticHeckeBandBootstrap

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve

theorem hasSieveExponent_one
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) :
    HasSieveExponent F c Q 1 :=
  hasSieveExponent_one_of_band F hF c Q

end DedekindZetaZeroFree.LargeSieve.Sieve
