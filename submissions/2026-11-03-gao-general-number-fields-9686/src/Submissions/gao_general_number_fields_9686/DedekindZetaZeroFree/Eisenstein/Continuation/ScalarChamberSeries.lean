/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/ScalarChamberSeries.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.FlatSectionResolvent
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.ScalarAndSmoothGerms
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.ChamberAbsoluteConvergence

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure SelectedScalarBranch (R : PrincipalMellin.ActualRecipe S η)
    {N : TraceHaarTransport R} (B : JointRootAlignedSources R N) (v : R.A.UnitQuotient) where
  E : ℂ → Functions R
  normal : ∀ g, MeromorphicNFOn (fun s => E s g) KPContinuation.spectralDomain
  chamber : ∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
    E s g = KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
      B.sources.K (B.sources.flat v) s g

theorem selected_scalar_branch_exists
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R} (B : JointRootAlignedSources R N)
    (v : R.A.UnitQuotient) : Nonempty (SelectedScalarBranch R B v) := by
  obtain ⟨E, hnormal, hchamber⟩ :=
    EisensteinSmoothGerms.ScalarSource.selected_scalar_continuation R B v
  exact ⟨⟨E, hnormal, hchamber⟩⟩

end DedekindZetaZeroFree.ThetaExpansion

end
