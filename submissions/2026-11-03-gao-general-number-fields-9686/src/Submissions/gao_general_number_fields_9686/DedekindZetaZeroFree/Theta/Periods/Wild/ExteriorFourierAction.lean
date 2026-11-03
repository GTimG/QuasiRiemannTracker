/-
2026-11-03 tracker adaptation by Zhongpai Gao: the PR #114 support prefix is
relocated to Submissions.gao_general_number_fields_9686; original proof bodies,
declaration namespaces, licensing and provenance below are retained.
-/
/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/Theta/Periods/Wild/ExteriorFourierAction.lean
Tracker adaptation: local module import paths relocated under Submissions.gao_general_number_fields_9686.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.gao_general_number_fields_9686.DedekindZetaZeroFree.Theta.Periods.Wild.ExteriorFiniteAction

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap
open MomentSources KPKirillovFiniteTensor WildCurrentTensor WildCurrentReindex WildCurrentJointPeriod
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable (D : TensorActions R N) (W : Finset (KPFinitePlace F))
  (s : RestrictedTensorSimple.Level D.bad) (hW : places W ⊆ s.val)
  (x : ∀ p : s.val, actualLocal R D.finiteData p)
  (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val) (ho : Sum.inr q ∉ places W)
  (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))

include ho in
theorem outside_fourier (z : AmbientTensor F W (fiber D W))
    (g : KPGlobalTorusFunctionData.G F R.A.zeta12 R.A.primitive_zeta12) :
    fourier R D.sources.dq (globalMap D W s hW (outsideTuple D s x q hq a) z) g =
    fourier R D.sources.dq (globalMap D W s hW x z)
      (g * KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)) := by
  unfold MomentSources.fourier
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with u
  rw [outside_finite D W s hW x q hq ho a]
  simp only [mul_assoc]
end DedekindZetaZeroFree.FourierContinuation.WildCurrentGlobalMap

end
