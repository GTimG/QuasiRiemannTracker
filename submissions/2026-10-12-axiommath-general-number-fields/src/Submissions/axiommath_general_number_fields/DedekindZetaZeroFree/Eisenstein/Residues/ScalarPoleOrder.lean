/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Eisenstein/Residues/ScalarPoleOrder.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Eisenstein.Residues.EvaluationSimplePoleBounds

@[expose] public section

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms
open scoped Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem selected_scalar_order_at_zero_ge_neg_one
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R} (B : JointRootAlignedSources R N)
    (v : R.A.UnitQuotient) (D : SelectedScalarBranch R B v) :
    ∀ g, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (fun s => D.E s g) 0 := by
  exact EisensteinSmoothGerms.ScalarSource.selected_scalar_order_zero R B v D

end DedekindZetaZeroFree.ThetaExpansion
