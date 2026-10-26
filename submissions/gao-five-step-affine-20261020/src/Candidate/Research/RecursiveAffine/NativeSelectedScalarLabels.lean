/- Actual scalar source payment on the literal native selected labels. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedScalarThreshold
import Candidate.Research.RecursiveAffine.NativeForestAttach

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualSourceGates
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentSectorLocalization CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalScalar CenteredMomentSourceLiveColumn
open CenteredMomentFiniteProfileExceptional
open Cycle63FinalCapacity Cycle63FinalNatural
open Cycle63Moment Cycle63InitialMass Cycle63FinalLow Cycle153RegionalLow Cycle153SourceSchedule
variable [L : Cycle63.AffineLedger]
variable {alpha Label : Type} [Fintype alpha] [DecidableEq alpha] [Fintype Label]

/-- Apply the original inverse-volume source theorem to the SAME complete
selected-row carrier and its supported payment labels. The only size
premise is the producer's fixed threshold; the desired scalar inequality
is proved here, rather than supplied by the caller. -/
theorem actual_selected_scalar_labels
    (budget : ℕ)(epsV : ℝ)(hepsV : 0<epsV)(Z : ℝ)(hZ : 1<Z)
    (hlarge : actualSelectedScalarThreshold budget epsV hepsV≤Z)
    (s : Input alpha)(p : Profiles (1/4) (9/4))(Cs : ℝ)
    (caps : GeometryAffineLowSourceGates s p Cs Z)(hcard : Fintype.card alpha≤budget)
    (reflected second : Bool)(R seed : Ideal O)(hseed : Squarefree seed)
    (Mrow amp firstHeight common pad shellLoss : ℝ)(hShell : 0 ≤ shellLoss)
    (key : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)
    (hf : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val)
      R s.ν s.W s.P≠0) :
    let Rows:=NativeLowRows reflected s R seed Z Mrow amp (nativeMu/64) (nativeMu/8) (9/4)
      firstHeight (Fintype.card alpha) hZ key caps.zero₁ caps.zero₂ firstIndex
    let first:=fun l=>geometryFirstLabel s R seed (Z^Mrow) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val
    let label:=fun r : Rows=>actualSecondSupportedLabel _ _ _ _ _ _ _ r.val.2
      (actual_main_low_selected_inactive reflected s R seed Z Mrow amp (nativeMu/64) (nativeMu/8)
        (9/4) firstHeight (Fintype.card alpha) hZ key caps.zero₁ caps.zero₂ firstIndex r)
    let childSrc:=fun l=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstHeight (firstIndex l)
    let radius:=fun r : Rows=>firstMainRadius reflected (Z^Mrow) (volume s) Z (nativeMu/64)
      (3*amp) (nativeMu/8) (first r.val.1)
    let nominal:=fun r : Rows=>secondNominal 1 Z amp (frequencyLoss Z 32 (nativeMu/64)+nativeMu/8)
      (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
      (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
      (label r).1.1 (label r).1.2 (label r).2.val
    let ownNorm:=fun r : Rows=>((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)
    ∀r : Rows,
      Z^(-amp)*(radius r/volume (childSrc r.val.1))*
        (normalizer (label r).1.1 (label r).1.2 (label r).2.val*(ownNorm r)^(shellLoss-1))*
        Z^(nominal r+amp+common+pad)≤
      Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first r.val.1)+
        (common+pad)+(1-Mrow)+epsV+130*shellLoss)/ownNorm r :=by
  intro Rows first label childSrc radius nominal ownNorm r
  exact (actualSelectedScalarAfter budget epsV hepsV Z hlarge).2 L hZ s p Cs caps hcard
    reflected second R seed hseed Mrow amp firstHeight common pad shellLoss key firstIndex hf hShell r

end
end OAI.SevenEighths.Cycle153ActualSourceGates
#print axioms OAI.SevenEighths.Cycle153ActualSourceGates.actual_selected_scalar_labels
