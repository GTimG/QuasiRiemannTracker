/- Original source pools remain bounded in the actual second datum. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativePhysicalHeightAliases
import Candidate.Cycle63.Physical.InitialMass.SecondProjectorShell
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPayment

set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentSecondPhysicalBlock
variable {alpha : Type*}[Fintype alpha][DecidableEq alpha]

/-- The native first child only restricts the original source pools.
This is the actual cap used by the residual shell operator, with no
replacement by the much larger source-dictionary norm. -/
theorem native_second_datum_pool_cap
    (reflected : Bool)(s : Input alpha)(R seed : Ideal O)
    (Z Mrow amp xi reserve b firstHeight : ℝ)(N : ℕ)(hZ : 1<Z)(key : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key q)
    (bound : ℝ)(hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤bound) :
    let datum:=geometryLowSecondDatum reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key q hz1 hz2 n
    ∀i I,I∈datum.input.pools i→(I.absNorm:ℝ)≤bound :=by
  exact actual_child_pool_cap s
    (geometryColumnIdeal reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val)
    R q.2
    (geometryColumnCharacter reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key q.1.val)
    firstHeight bound hpool

/-- The ordinary ray datum changes only the row sum. Its exact input,
including all original pools and its physical height, stays literal. -/
theorem ordinary_second_datum_input
    (d : SecondInputDatum alpha)(chi0 : RayFourExpansion.RayCharacter)(Q : Ideal O)(m : O) :
    (ordinarySecondDatum d chi0 Q m).input=d.input :=by rfl
end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.native_second_datum_pool_cap
#print axioms OAI.SevenEighths.Cycle153RegionalLow.ordinary_second_datum_input
