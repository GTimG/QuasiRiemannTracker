/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/GroupVariableContinuity.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.UniformDiskSpatialContinuity

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms Filter
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_scalar_numerator_zero_continuous
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R} (B : JointRootAlignedSources R N)
    (v : R.A.UnitQuotient) (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (hjoint : ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ))
    (horder : ∀ g, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun s => D.E s g) 0)
    (r : ℝ) (hr : 0 < r)
    (hb : Metric.ball (0 : ℂ) r ⊆ KPContinuation.spectralDomain)
    (hp : ∀ s ∈ Metric.ball (0 : ℂ) r, s ∈ P.poles → s = 0) :
    Continuous (selectedScalarNumerator D r 0) := by
  exact ResidueContinuity.selected_residue_continuous D P hjoint horder r hr hb hp

end DedekindZetaZeroFree.ThetaExpansion

end
