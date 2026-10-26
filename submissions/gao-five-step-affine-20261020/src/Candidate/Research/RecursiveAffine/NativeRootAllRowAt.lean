/- Literal root all-row sources after the genuine arithmetic cutoff. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootAllRowThreshold
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63InitialMass Cycle63Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentCommonProfile CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstCanonicalFamily
open CenteredMomentSourceLiveColumn
open Cycle153SourceSchedule Cycle153ActualSourceGates
variable {alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
noncomputable local instance rootAllRowAtLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger

variable (budget : ℕ)(Z : ℝ)(hlarge : actualRootAllRowThreshold budget≤Z)(hZ : 1<Z)
variable (reflected second : Bool)(s : Input alpha)(p : Profiles (1/4) (9/4))(Cs : ℝ)
variable (caps : GeometryAffineLowSourceGates s p Cs Z)(hcard : Fintype.card alpha≤budget)
variable (amp firstHeight : ℝ)(bin : ℤ×(Fin 5→ℤ))
variable (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (nativeMu/64)
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
variable (hf : ∀l,frozenCoefficient (firstIndex l).2.val
  (geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (nativeMu/64)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val) 1 s.ν s.W s.P≠0)

/-- The literal root puncture is bounded by Z^8 on every selected row. -/
def actualRootAllRowMasksAt :=
  let hvolume3 : volume s≤Z^(3:ℝ):=caps.volume.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  (actualRootAllRowAfter budget Z hlarge).2.2 reflected second s 1 1 1 amp
    (nativeMu/64) (nativeMu/8) firstHeight 0 hZ hcard caps.endpoints squarefree_one one_ne_zero
    (by norm_num) (by simp only [map_one,Nat.cast_one,Real.rpow_zero,le_refl]) caps.zero₁ caps.zero₂
    caps.sourceCap hvolume3 bin firstIndex hf

/-- Native cap3/selected cap4 and true absolute dyads supply ALL literal
root history codes, including rows whose analytic source is empty. -/
def actualRootAllRowFactsAt (hamp0 : 0≤amp)(hamp1 : amp≤1)
    (units : FirstSourceLabel→O)(hunits : ∀l,IsUnit (units l)) :=
  (actualRootAllRowAfter budget Z hlarge).1.2 hZ reflected s p Cs caps 1 1 squarefree_one amp firstHeight
    hamp0 hamp1 hcard bin firstIndex hf units hunits
end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actualRootAllRowMasksAt
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actualRootAllRowFactsAt
