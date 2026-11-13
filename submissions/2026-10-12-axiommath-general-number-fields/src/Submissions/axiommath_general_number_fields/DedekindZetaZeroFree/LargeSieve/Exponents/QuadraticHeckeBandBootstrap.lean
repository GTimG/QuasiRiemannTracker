/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/LargeSieve/Exponents/QuadraticHeckeBandBootstrap.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.LargeSieve.Exponents.ConductorControlledTransfer

@[expose] public section

open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.LargeSieve.Sieve

theorem hasSieveExponent_one_of_band
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) :
    HasSieveExponent F c Q 1 := by
  exact hasSieveExponent_one_of_core_transfer F hF c Q

end DedekindZetaZeroFree.LargeSieve.Sieve
