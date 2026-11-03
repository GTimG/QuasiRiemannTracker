/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9672; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Whittaker/FinitePlaces/CoefficientRankBound.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9672.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9672.DedekindZetaZeroFree.RepresentationTheory.Kirillov.WhittakerProfileRank

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.FourierContinuation.TensorActions
open MomentSources
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

theorem finite_slice_rank_le_one_of_coefficient_rank (D : TensorActions R N)
    (q : KPFinitePlace F)
    (hJ : Module.rank ℂ (ActualKirillov.coefficient F R.A.zeta12 R.A.primitive_zeta12 q
      (D.finiteData q).inducing (D.finiteData q).inducing.polarization
      (D.finiteData q).haar (D.finiteData q).haar_integer) ≤ 1) :
    Module.rank ℂ (D.toTensorHC.sliceLine (Sum.inr q)) ≤ 1 := by
  exact (Submodule.rank_mono (D.sliceLine_le_intrinsicWhittaker q)).trans
    (ExteriorWhittakerValues.ActualWhittaker.equivariant_rank_le_one_of_coinvariant_rank_le_one
      _ _ _ hJ)

end DedekindZetaZeroFree.FourierContinuation.TensorActions

end
