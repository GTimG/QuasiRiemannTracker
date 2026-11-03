/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/NonzeroTensor/SU2Covariance.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Whittaker.Sources.CovariantExistence

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources FourierContinuation.NonDegenerate
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem detected_complex_covariant_dictionary_exists
    (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
    (prior : Nonempty (FiniteCovariant R N)) :
    ∃ D : ComplexCovariant R N, D.coreMap (D.selected D.probe) ≠ 0 := by
  suffices h : Nonempty (ComplexCovariant R N) by
    obtain ⟨D⟩ := h
    exact ⟨D, D.toDictionary.image_ne⟩
  obtain ⟨D⟩ := prior
  exact FourierContinuation.LiteralSource.current_covariant_nonempty  R D.aligned N

end DedekindZetaZeroFree.ThetaExpansion

end
