/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Moments/Comparison/CompatibleThetaMomentData.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Moments.Probes.SignedUnfoldingAndAngularCancellation

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources

theorem selected_moment_source_of_certified_packet {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η) (C : CertifiedPacket R) :
    RootAligned R ∧ Nonempty (SelectedMomentSource R) :=
  momentSource_of_certified_packet R C
end DedekindZetaZeroFree.ThetaExpansion
