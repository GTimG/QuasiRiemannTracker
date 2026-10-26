/- One whole licensed arithmetic majorant closes a real regional node.
Copyright (c)2026 Zhongpai Gao. Native physical sources by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeNodeRawLow
import Candidate.Research.RecursiveAffine.NativeTerminalNode

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentAllocatedRayDictionary
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open Cycle63InitialMass Cycle153Reachable Cycle153RegionalState Cycle153SourceReturn
open Cycle153RecursiveHighProvider Cycle153SourceSchedule Cycle153Geometry
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M ≤ H)
variable {C : SourceContext (α:=alpha) M H}

/-- The genuine native HIGH producer supplies a nonempty arithmetic
domain. Native counting bounds that whole domain before the current
energy, so a single licensed majorant pays all actual LOW configurations.
The literal raw physical estimate is normalized here; no normalized LOW
or current NodeOutput is assumed. Every metadata field comes from the
SAME majorant used in the resulting energy bound. Native schedules and
the actual raw source are separately constructed before invoking this
consumer. -/
theorem actual_node_output_from_raw_physical_source {j : Fin 4}(N : ReachableNode C j)
    (hgrid : C.gridDenominator=Cycle153.RegionalSchedule.gridSize)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule)(epsilon tauLow lossNeeded tauT : ℝ)
    (Psi : 𝓢(ℝ,ℂ))(SH : Finset (ℕ×ℕ))(dh degree : ℕ)(S : Finset (ℕ×ℕ))
    (Cenergy Chigh Cs Kh Kclass Kreturn Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))
    (Sp : Finset alpha→Finset (ℕ×ℕ))(degreeLow : Finset alpha→ℕ)(Klow : Finset alpha→ℝ)
    (hT : 2<N.localBase^g.τ)(hCenergy : 0≤Cenergy)(hChigh : 0≤Chigh)(hKh : 0≤Kh)
    (hKreturn : 0 ≤ Kreturn)(hKlow : ∀J,0 ≤ Klow J)
    (hBsrc : 0 ≤ Bsrc)(hbudget : ∀d : SuffixDepth (4-j.val),
      (suffixOffset (4-j.val) d:ℝ)*Bsrc ≤ C.Bnorm)(hZtwo : 2 ≤ N.localBase)
    (hclass : Kclass≤C.highClassCap)(hloss : lossNeeded+epsilon≤terminalLossCap j)
    (htau : tauLow≤tauT)(hheight : C.Tz=N.localBase^tauT)
    (hAt : letI : Cycle63.AffineLedger:=N.ledger
      RegionalAtState (α:=alpha) M H hH C.W C.W_smooth C.W_support hbeta hbetaHi
        g 2 20 C.slotMesh epsilon (by norm_num) Psi SH dh degree S Cenergy Chigh Cs
        Sp degreeLow Klow (by norm_num) C.slotMesh_pos.le C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase)
    (hsource : letI : Cycle63.AffineLedger:=N.ledger
      ActualHighNodeAt (base:=prefixDictionary j.val) (α:=alpha) M H hH
        C.W C.W_smooth C.W_support hbeta hbetaHi g (1/4) (9/4) 2 20
        C.slotMesh epsilon tauLow C.Bnorm lossNeeded (by norm_num)
        Psi SH dh Kclass Kh C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase)
    (hraw : letI : Cycle63.AffineLedger:=N.ledger
      NativeNodeRawLowAt hH N hbeta g Cs Sp degreeLow Klow hT hbetaHi
        (N.state.rowWidth+3*g.δ-Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
          (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit)))+epsilon)
        Kreturn Bsrc boxes)
    (hamp : letI : Cycle63.AffineLedger:=N.ledger
      3*g.δ≤Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit)))) :
    Nonempty (NodeOutput hH N (Cenergy*(1+Chigh*(2*Kreturn+2*Kh))) epsilon Bsrc S degree boxes) := by
  letI : Cycle63.AffineLedger:=N.ledger
  obtain ⟨own,hm,hA,ha,hl,hcard,_,hgiven⟩:=actual_reachable_own_high hH N
    hbeta hbetaHi g epsilon tauLow lossNeeded Psi SH dh Kclass Kh hsource hT tauT htau hheight
  have hlossOwn : own.loss≤terminalLossCap j := hl.trans_le hloss
  have hcardOwn : ∀b,(Fintype.card (own.record b).Class:ℝ)≤C.highClassCap :=
    fun b=>(hcard b).trans hclass
  have herror0 : 0≤42/(C.gridDenominator:ℝ) := by positivity
  have herrorFine : 42/(C.gridDenominator:ℝ)≤1/1000000000000 := by
    rw [hgrid];norm_num [Cycle153.RegionalSchedule.gridSize]
  have hAmpOwn : N.unit*own.amp≤
      ![Coordinates.a1 N.coordinates,Coordinates.a2 N.coordinates,
        Coordinates.a3 N.coordinates,Coordinates.a4 N.coordinates] j+42/C.gridDenominator := by
    rw [ha];exact node_own_amplifier_receipt N
  let ownReceipt:=native_own_forest_receipt hH N own hm hA ha hlossOwn hcardOwn
    (42/C.gridDenominator) herror0 herrorFine hAmpOwn Bsrc boxes
  have hvalue : ownReceipt.family.value=own.value :=
    native_own_forest_receipt_value hH N own hm hA ha hlossOwn hcardOwn
      (42/C.gridDenominator) herror0 herrorFine hAmpOwn Bsrc boxes
  have hTzero : 0 ≤ C.Tz := by rw [hheight];exact (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _).le
  obtain ⟨envelope⟩:=actual_whole_arithmetic_envelope hBsrc hbudget hZtwo hTzero ownReceipt
  have hown : own.value ≤ 2*envelope.receipt.family.value :=
    envelope.own_bound ownReceipt own.value hvalue.ge
  have hlow:=native_node_low_at_of_actual_raw_source hH N hbeta hbetaHi g Cs Sp degreeLow
    Klow hKlow hT _ Kreturn Bsrc boxes hKreturn envelope hraw
  have he:=actual_node_at_state_from_whole_forest hH N hbeta hbetaHi g epsilon Psi SH dh degree S
    Cenergy Chigh Cs Sp degreeLow Klow hT hCenergy hChigh hAt own envelope.receipt.family
    Kh (2*Kreturn) hKh (mul_nonneg (by norm_num) hKreturn) hown hamp hlow hgiven
  refine ⟨⟨envelope.receipt.family,envelope.receipt.chronology,envelope.receipt.path,
    envelope.receipt.terminalLoss,envelope.receipt.terminalSource,envelope.receipt.classCap,he⟩⟩

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_node_output_from_raw_physical_source
