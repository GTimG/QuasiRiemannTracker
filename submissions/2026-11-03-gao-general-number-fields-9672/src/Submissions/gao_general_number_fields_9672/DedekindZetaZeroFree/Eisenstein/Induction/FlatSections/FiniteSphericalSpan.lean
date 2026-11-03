/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Induction/FlatSections/FiniteSphericalSpan.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Residues.SpanAutomorphy
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Eisenstein.Induction.Convolution.ProjectedFlatExpansion
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Profiles.IdelicDilation

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SharedSource
open MomentSources
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_zero → smooth_zero
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_smul → smooth_smul
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ActualProjectedFlatExpansion renaming kfinite_add → kfinite_add
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ActualProjectedFlatExpansion renaming kfinite_smul → kfinite_smul
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η}

def flatScalarStage (Q : AdmissibleFlatSources R) : Submodule ℂ (Functions R) :=
  Submodule.span ℂ (Set.range (fun v => (Q.flat v).val 0))

end DedekindZetaZeroFree.SharedSource

end
