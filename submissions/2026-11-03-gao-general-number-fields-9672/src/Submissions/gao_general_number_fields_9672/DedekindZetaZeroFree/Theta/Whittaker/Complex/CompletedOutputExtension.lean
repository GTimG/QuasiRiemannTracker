/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/Complex/CompletedOutputExtension.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Whittaker.Evaluation.CompletedContinuity
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.CompactResidueBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts ComplexLines
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "ζ" => R.A.zeta12
local notation "hζ" => R.A.primitive_zeta12
variable (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
variable (x : ∀j : s.val,LiteralSource.Plus R.A P C j.val)
variable (w : InfinitePlace F) (hw : Sum.inl w∈s.val)

def actualSlot : complexCore →ₗ[ℂ] (KPLiteralRaw.G F ζ hζ → ℂ) :=
  (LiteralSource.coreResidue R P C).comp (restrictedSlotTensor R.A P C s x w hw)

theorem actualSlot_continuous (v : complexCore) : Continuous (actualSlot R P C s x w hw v) :=
  (LiteralSource.coreResidue_raw_automorphic R P C _).1.1

end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
