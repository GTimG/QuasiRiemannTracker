/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/PositiveTraceCoefficient.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.SourceExistence
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Profiles.ResidueSphericality

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources FourierContinuation.NonDegenerate
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem detected_period_source_exists
    (R : PrincipalMellin.ActualRecipe S η) (hR : RootAligned R)
    (N : TraceHaarTransport R) (prior : Nonempty (JointRealizedFlatSources R N)) :
    ∃ D : PeriodSource R N,
      fourier R D.sources.dq (D.realization.theta D.probe) 1 ≠ 0 ∧
      (D.sources.flat D.probe).val 0 ≠ 0 := by
  suffices h : Nonempty (PeriodSource R N) by
    obtain ⟨D⟩ := h
    exact ⟨D, D.detected, D.flat_ne⟩
  exact FourierContinuation.LiteralSource.current_period_source_nonempty  R hR N

end DedekindZetaZeroFree.ThetaExpansion

end
