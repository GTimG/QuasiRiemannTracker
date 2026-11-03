/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Unfolding/TensorProducts/QuotientCompactCovariance.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ScalarSections.CentralDescent
public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.Theta.Unfolding.TensorProducts.CoreCompactCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
namespace DedekindZetaZeroFree.FourierContinuation.LiteralSource
open NumberField KPGlobalTorusFiniteStages TensorActionSource KPGlobalResidualConstruction
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)

theorem quotientCoreEvaluator_compact (w : InfinitePlace F)
    (k : KPCplxCharacterHaar.ComplexSU2)
    (x : RestrictedTensorSimple.Core (Plus A P C) (plusReference A P C) (bad A P C))
    (g : G F A.zeta12 A.primitive_zeta12) :
    quotientCoreEvaluator A P C (coreCompactSlot A P C w k x) g =
      quotientCoreEvaluator A P C x
        (g * complexCompactLift F A.zeta12 A.primitive_zeta12 w k) := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H a =>
      change quotientCoreValue A P C _
        (KPAdelicCoverRestrictedProduct.scalarQuotient F A.zeta12 A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.amalgamation F A.zeta12 A.primitive_zeta12 a)) =
        quotientCoreValue A P C x
          (KPAdelicCoverRestrictedProduct.scalarQuotient F A.zeta12 A.primitive_zeta12
            (KPAdelicCoverRestrictedProduct.amalgamation F A.zeta12 A.primitive_zeta12 a) *
            complexCompactLift F A.zeta12 A.primitive_zeta12 w k)
      rw [← literalLocalCompact_global A w k]
      change _ = quotientCoreValue A P C x
        (KPAdelicCoverRestrictedProduct.scalarQuotient F A.zeta12 A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.amalgamation F A.zeta12 A.primitive_zeta12 a) *
         KPAdelicCoverRestrictedProduct.scalarQuotient F A.zeta12 A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.amalgamation F A.zeta12 A.primitive_zeta12
            (KPAdelicCoverRestrictedProduct.localToRestricted F A.zeta12 A.primitive_zeta12
              (Sum.inl w) (literalLocalCompact A w k))))
      rw [← map_mul, ← map_mul, quotientCoreValue_raw, quotientCoreValue_raw]
      exact rawCoreInsertion_compact A P C w k x a

end DedekindZetaZeroFree.FourierContinuation.LiteralSource

end
