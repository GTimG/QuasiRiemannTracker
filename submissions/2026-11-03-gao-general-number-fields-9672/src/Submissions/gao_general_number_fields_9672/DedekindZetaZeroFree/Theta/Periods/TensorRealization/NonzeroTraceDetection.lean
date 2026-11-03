/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/TensorRealization/NonzeroTraceDetection.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.PositiveTraceCoefficient
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Periods.NonzeroTensor.LocalRealization
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Periods.NonzeroTensor.ScalarInjectivityAndRegularity
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Periods.NonzeroTensor.LieWordGeneration
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Periods.NonzeroTensor.FiniteCoverCovariance
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Periods.NonzeroTensor.SU2Covariance

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources FourierContinuation
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem tensorDetected_nonempty
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (prior : Nonempty (TensorActions R N)) :
    Nonempty (TensorDetected R N) := by
  obtain ⟨P⟩ := prior
  obtain ⟨D₁, _, _⟩ := detected_period_source_exists  R hR N ⟨P.toJointRealizedFlatSources⟩
  obtain ⟨D₂, _⟩ := detected_dictionary_exists  R N ⟨D₁⟩
  obtain ⟨D₃, _⟩ := detected_faithful_dictionary_exists  R N ⟨D₂⟩
  obtain ⟨D₄, _⟩ := detected_hc_generated_dictionary_exists  R N ⟨D₃⟩
  obtain ⟨D₅, _⟩ := detected_finite_covariant_dictionary_exists  R N ⟨D₄⟩
  obtain ⟨D₆, _⟩ := detected_complex_covariant_dictionary_exists  R N ⟨D₅⟩
  exact ⟨D₆.tensorDetected R N⟩
end DedekindZetaZeroFree.ThetaExpansion

end
