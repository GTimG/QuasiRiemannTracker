/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Continuation/SelectedPoleSets.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Continuation.ScalarChamberSeries

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

structure SelectedPoleSet {R : PrincipalMellin.ActualRecipe S η}
    {N : TraceHaarTransport R} {B : JointRootAlignedSources R N} {v : R.A.UnitQuotient} (D : SelectedScalarBranch R B v) where
  poles : Set ℂ
  subset : poles ⊆ KPContinuation.spectralDomain
  isolated : ∀ z ∈ KPContinuation.spectralDomain, ∃ r : ℝ, 0 < r ∧
    Metric.ball z r ⊆ KPContinuation.spectralDomain ∧
    ∀ s ∈ Metric.ball z r, s ∈ poles → s = z
  chamber_disjoint : ∀ s, (1 / 3 : ℝ) < s.re → s ∉ poles
  regular : ∀ s ∈ KPContinuation.spectralDomain, s ∉ poles →
    ∀ g, AnalyticAt ℂ (fun z => D.E z g) s

end DedekindZetaZeroFree.ThetaExpansion

end
