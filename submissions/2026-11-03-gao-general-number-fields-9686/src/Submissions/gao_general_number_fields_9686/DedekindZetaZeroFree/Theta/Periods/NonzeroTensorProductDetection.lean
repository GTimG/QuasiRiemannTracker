/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/NonzeroTensorProductDetection.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.RankOne.ComplexSliceSpans
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.RankOne.FiniteSliceSpans
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.TensorRealization.ExteriorSphericalVectors
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.TensorRealization.HarishChandraHeckeGeneration
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.TensorRealization.LocalAndSU2Actions
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.TensorRealization.NonzeroTraceDetection
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.TensorRealization.ScalarCore

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

end DedekindZetaZeroFree.ThetaExpansion

section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem detected_period_factorization
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (prior : Nonempty (JointRealizedFlatSources R N)) :
    Nonempty (JointHaarFactorizedSources R N) := by
  have h1 := tensorSeed_nonempty  R hR N prior
  have h2 := tensorHC_nonempty  R hR N h1
  have h3 := tensorActions_nonempty  R hR N h2
  have h4 := tensorDetected_nonempty  R hR N h3
  have h5 := tensorSpherical_nonempty  R hR N h4
  have h6 := tensorFiniteLines_nonempty  R hR N h5
  obtain ⟨D⟩ := tensorLocalLines_nonempty  R hR N h6
  exact ⟨FourierContinuation.jointHaarFactorizedSources_of_factorization D.toJointRealizedFlatSources D.factorization⟩
end DedekindZetaZeroFree.ThetaExpansion

end
