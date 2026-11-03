/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Unfolding/TensorProducts/ProductCompactCovariance.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.TensorProducts.IntegralQuotientActions
public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Metaplectic.Induction.LocalSectionProductEvaluation

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.TensorActionSource
open KPGlobalResidualConstruction KPActualReflectionData.LiteralProductEvaluator
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F]
variable (A : SArithmeticData F)

def literalLocalCompact (w : NumberField.InfinitePlace F)
    (k : KPCplxCharacterHaar.ComplexSU2) :
    KPLocalCover.CubicGL2Raw F A.zeta12 A.primitive_zeta12 (Sum.inl w) :=
  KPLocalCover.sectionMap F A.zeta12 A.primitive_zeta12 (Sum.inl w)
    (Matrix.GeneralLinearGroup.map
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F A.zeta12 A.primitive_zeta12 w)).symm.toRingHom
      (KPCplxCharacterHaar.complexSU2Embedding k))

theorem literalLocalCompact_global (w : NumberField.InfinitePlace F)
    (k : KPCplxCharacterHaar.ComplexSU2) :
    KPAdelicCoverRestrictedProduct.scalarQuotient F A.zeta12 A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.localInjection F A.zeta12 A.primitive_zeta12
        (Sum.inl w) (literalLocalCompact A w k)) =
    complexCompactLift F A.zeta12 A.primitive_zeta12 w k := rfl

theorem complexMatrix_literalLocalCompact (w : NumberField.InfinitePlace F)
    (k : KPCplxCharacterHaar.ComplexSU2) :
    complexMatrix A w (literalLocalCompact A w k) =
      KPCplxCharacterHaar.complexSU2Embedding k := by
  unfold complexMatrix literalLocalCompact
  change Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map _ _) = _
  apply Units.ext
  ext i j
  simp [Matrix.GeneralLinearGroup.map]

theorem literalLocalValue_compact
    (w : NumberField.InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2)
    (x : KPLiteralTensor.harmonicPlus)
    (g : KPLocalCover.CubicGL2Raw F A.zeta12 A.primitive_zeta12 (Sum.inl w)) :
    (KPSourceConvention.ordinaryGenuineCharacter F A.zeta12 A.primitive_zeta12
      g.epsilon : ℂ) * (harmonicSourceAction k x).val (complexMatrix A w g) =
    (KPSourceConvention.ordinaryGenuineCharacter F A.zeta12 A.primitive_zeta12
      (g * literalLocalCompact A w k).epsilon : ℂ) *
        x.val (complexMatrix A w (g * literalLocalCompact A w k)) := by
  have he : (g * literalLocalCompact A w k).epsilon = g.epsilon := by
    change g.epsilon * 1 * KPLocalCover.sigmaTwo F A.zeta12 A.primitive_zeta12 (Sum.inl w) g.g
      (literalLocalCompact A w k).g = _
    rw [KPLocalChartTopology.complex_sigmaTwo_eq_one]
    simp
  have hm : complexMatrix A w (g * literalLocalCompact A w k) =
      complexMatrix A w g * KPCplxCharacterHaar.complexSU2Embedding k := by
    unfold complexMatrix
    change Matrix.GeneralLinearGroup.map _ (g.g * (literalLocalCompact A w k).g) = _
    rw [map_mul]
    exact congrArg (Matrix.GeneralLinearGroup.map _ g.g * ·)
      (complexMatrix_literalLocalCompact A w k)
  rw [he, hm]
  rfl

end DedekindZetaZeroFree.FourierContinuation.TensorActionSource

end
