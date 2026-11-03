/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/FiniteSourceImage.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Continuation.LaurentNumeratorCovariance
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.SourceResidueLinearMap

@[expose] public section

noncomputable section
open scoped Classical Topology
namespace DedekindZetaZeroFree.SharedSource
open MomentSources EisensteinSmoothGerms
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_zero → smooth_zero
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_smul → smooth_smul
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming kfinite_fullCompact → kfinite_fullCompact
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ActualProjectedFlatExpansion renaming kfinite_add → kfinite_add
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ActualProjectedFlatExpansion renaming kfinite_smul → kfinite_smul
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
variable {C : ScalarContinuation R Q}

def scalarResidualStage (H : ∀ v, ScalarGerm C v) : Submodule ℂ (Functions R) :=
  Submodule.span ℂ (Set.range (fun v => ((H v).cleared 0 : Functions R)))

theorem finiteSourceResidue_range_stage (H : ∀ v, ScalarGerm C v) :
    (finiteSourceResidue H).range = scalarResidualStage H :=
  finiteSourceResidue_range H

end DedekindZetaZeroFree.SharedSource

end
