/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/HarmonicAnalysis/Haar/TraceCharactersAndGaussShifts.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.HarmonicAnalysis.Haar.ComplexTraceMeasureParameters
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Arithmetic.Ideals.RootAlignedPrincipalization

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem trace_haar_transport_exists (R : PrincipalMellin.ActualRecipe S η)
    (hR : RootAligned R) : Nonempty (TraceHaarTransport R) := by
  exact TraceHaarTransport.traceHaarTransport_exists R

end DedekindZetaZeroFree.ThetaExpansion
