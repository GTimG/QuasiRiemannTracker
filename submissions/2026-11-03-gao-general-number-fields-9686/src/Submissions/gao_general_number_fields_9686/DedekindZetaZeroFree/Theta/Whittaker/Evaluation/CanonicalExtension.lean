/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/Evaluation/CanonicalExtension.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Whittaker.Complex.CompletedOutputExtension
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Eisenstein.Residues.RestrictedTensors.CompactTranslationBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension
open MomentSources KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts ComplexLines
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)

variable (s : RestrictedTensorSimple.Level (LiteralSource.bad R.A P C))
variable (x : ∀j : s.val,LiteralSource.Plus R.A P C j.val)
variable (w : InfinitePlace F) (hw : Sum.inl w∈s.val)

include N  in
theorem actualSlot_bound : CompactBound (actualSlot R P C s x w hw) := by
  intro K hK
  obtain ⟨orders,B,hB,h⟩ := restrictedSlot_actual_compact_bound R N P C  s x w hw K hK
  exact ⟨orders,⟨B,hB.le⟩,h⟩

def canonicalOutput (g : KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12) :
    PrincipalSeries negativeParameter →L[ℂ] ℂ :=
  extendedEvaluation (actualSlot R P C s x w hw) (actualSlot_bound R N P C  s x w hw) g

theorem canonicalOutput_core (g : KPLiteralRaw.G F R.A.zeta12 R.A.primitive_zeta12)
    (v : complexCore) :
    canonicalOutput R N P C  s x w hw g (smoothInclusion v)=
      LiteralSource.coreResidue R P C (restrictedSlotTensor R.A P C s x w hw v) g :=
  extendedEvaluation_core _ _ g v

end DedekindZetaZeroFree.FourierContinuation.CurrentOutputExtension

end
