/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Moments/Comparison/CompatibleThetaMomentData.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Moments.Probes.SignedUnfoldingAndAngularCancellation

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources

theorem selected_moment_source_of_certified_packet {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) (C : CertifiedPacket R) :
    RootAligned R ∧ Nonempty (SelectedMomentSource R) :=
  momentSource_of_certified_packet R C
end DedekindZetaZeroFree.ThetaExpansion
