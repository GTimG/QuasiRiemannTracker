/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Metaplectic/Induction/LocalSectionProductEvaluation.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Cubic.ReciprocityAndGenuineCharacterConventions
public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TensorRealization.LocalRangeQuotients

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPActualReflectionData.LiteralProductEvaluator
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts

variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)

def complexMatrix (w : NumberField.InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F A.zeta12 A.primitive_zeta12 (Sum.inl w)) :
    KPCplxCharacterHaar.ComplexGL2 :=
  Matrix.GeneralLinearGroup.map
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F A.zeta12 A.primitive_zeta12 w)).toRingHom g.g

end DedekindZetaZeroFree.KPActualReflectionData.LiteralProductEvaluator

end
