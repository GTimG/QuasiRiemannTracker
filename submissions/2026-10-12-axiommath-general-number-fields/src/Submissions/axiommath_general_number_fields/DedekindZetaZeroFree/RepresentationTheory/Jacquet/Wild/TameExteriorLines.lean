/-
AxiomMath/DedekindZetaZeroFree, Apache-2.0.
Imported revision: 09afbb4ce6570c1615d58509dc197fc9f0956b7d
Original path: DedekindZetaZeroFree/RepresentationTheory/Jacquet/Wild/TameExteriorLines.lean
Tracker adaptation: local module import paths relocated under Submissions.axiommath_general_number_fields.
Original theorem bodies and declaration namespaces retained.
-/
module

public import Submissions.axiommath_general_number_fields.DedekindZetaZeroFree.Theta.Whittaker.FinitePlaces.RankBoundAwayFromThree

@[expose] public section

noncomputable section
open scoped NumberField Classical TensorProduct
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.WildCurrentTameExterior
open MomentSources
variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

def tameSlot (p : KPHilbert.Place F) : Prop :=
  match p with
  | Sum.inl _ => False
  | Sum.inr q => (3 : 𝓞 F) ∉ q.asIdeal

theorem tame_line_finrank (D : TensorDetected R N)
    (p : KPHilbert.Place F) (hp : tameSlot p) :
    Module.finrank ℂ (D.toTensorHC.sliceLine p) = 1 := by
  obtain ⟨l,hl,hn⟩ := D.exists_nonzero_slice p
  apply line_finrank_one _ _ l hl hn
  cases p with
  | inl w => exact hp.elim
  | inr q => exact D.toTensorActions.finite_slice_rank_le_one_of_three_not_mem q hp

end DedekindZetaZeroFree.FourierContinuation.WildCurrentTameExterior

end
