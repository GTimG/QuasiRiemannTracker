/- Literal history code for the actual continuing carrier used by
NativeForestAttach. Residual choices remain attached metadata. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeLowHistoryCode
import Candidate.Research.RecursiveAffine.PhysicalHistoryCode
import Candidate.Cycle63.Moment.DepthTwoCount
import Candidate.Research.RecursiveAffine.HistoryPrepend
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPayment
import Candidate.Cycle63.Physical.InitialMass.SecondLabelDisintegration

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153JointCount
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentSectorLocalization CenteredMomentEnergyState
open CenteredMomentFirstCanonicalFamily CenteredMomentLogDyadic
open CenteredMomentOriginalCommonHarmonic IdealMobiusDivisorSum
open CenteredMomentSecondHeightFamily

variable {alpha Label : Type} [Fintype alpha] [DecidableEq alpha] [Fintype Label]
variable (reflected : Bool) (s : Input alpha) (R seed : Ideal O)
variable (Z Mrow amp xi reserve b firstHeight : ℝ) (N : ℕ) (hZ : 1<Z)
variable (key : ℤ×(Fin 5→ℤ)) (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
variable (firstIndex : Label → GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)

local notation "Rows" => ↥(mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp xi reserve b
  firstHeight N hZ key hz1 hz2 firstIndex)
local notation "first" => fun l=>geometryFirstLabel s R seed (Z^Mrow) Z xi
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val

/-- The literal LOW history key inherits supported first/second common
ideals, equal prime supports and the exact old-seed incidence from its
original physical source coefficient. None of these gates is assumed. -/
theorem nativeLowHistoryCode_native_gates (r : Rows) :
    let c:=nativeLowHistoryCode reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ key hz1 hz2 firstIndex r
    (Supported c.1.1.1.1 ∧ c.1.1.1.2≠0 ∧ Supported c.1.2.1.1 ∧ c.1.2.1.2≠0) ∧
    (primeSupport c.1.1.1.1=primeSupport c.1.1.1.2 ∧ primeSupport c.1.2.1.1=primeSupport c.1.2.1.2) ∧
    Squarefree c.2.1 ∧ c.2.1∣c.1.2.1.1 := by
  intro c
  let f:=geometryFirstSource s R seed (Z^Mrow) Z xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex r.val.1).1.val.1
  let datum:=geometryLowSecondDatum reflected s R seed Z Mrow amp xi reserve b firstHeight N hZ
    key (firstIndex r.val.1) hz1 hz2 r.val.2
  have hseed:=actual_first_live_squarefree (geometryFirstSource s R seed (Z^Mrow) Z xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key) (fun _=>logAnnulus)
    (firstIndex r.val.1).1.val (firstIndex r.val.1).1.property
  have hg:=actual_common_gates
    (geometryLowFirstChild reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex r.val.1))
    (R*geometryColumnIdeal reflected s R seed (Z^Mrow) Z xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex r.val.1).1.val)
    (firstIndex r.val.1).1.val.2.1.val hseed hz1 hz2 _ _ r.val.2.1.val.property
  exact ⟨⟨f.hC,f.hD.1,datum.hC,datum.hD.1⟩,⟨f.sameSupport,datum.sameSupport⟩,hseed,hg.2.2.2.1⟩

end
end OAI.SevenEighths.Cycle153JointCount
#print axioms OAI.SevenEighths.Cycle153JointCount.nativeLowHistoryCode_native_gates
