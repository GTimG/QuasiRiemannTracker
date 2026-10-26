/- The finite recursion ends in the genuine incumbent LOW source.
Copyright (c)2026 Zhongpai Gao. Native analytic sources by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeNodeAtState
import Candidate.Research.RecursiveAffine.NativeWholeNodeForest
import Candidate.Research.RecursiveAffine.RegionalTerminalLow
import Candidate.Research.RecursiveAffine.ActualNodeCoordinates
import Candidate.Research.RecursiveAffine.ChosenAnalyticSchedule

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
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M≤H)
variable {C : SourceContext (α:=alpha) M H}

/-- The last ledger genuinely deletes into the incumbent OLD region.
There is no recursive LOW daughter at depth three. -/
theorem terminal_node_deletes_old (N : ReachableNode C (3:Fin 4)) :
    @Cycle63.AffineLedger.DeletesIntoOldRegion N.ledger :=
  Cycle153Terminal.terminal_regional_deletes_old N.position N.positionFacts

/-- The actual native terminal LOW source, on the literal node input,
has exactly zero returned contribution. The source spec is the output of
terminal_actual_low_spec, not an assumed energy estimate. -/
theorem terminal_node_low_at_zero (N : ReachableNode C (3:Fin 4))
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule)(Cs : ℝ)
    (Sp : Finset alpha→Finset (ℕ×ℕ))(degreeLow : Finset alpha→ℕ)(Klow : Finset alpha→ℝ)
    (hT : 2<N.localBase^g.τ)
    (hclosed : letI : Cycle63.AffineLedger:=N.ledger
      GeometryAffineLowSelectedSpec (α:=N.slots) M H hH C.W hbeta g 2
        (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs (fun _ _ _=>True)
        (fun _ _ _ _ _=>True) (Sp N.slots) (degreeLow N.slots) (Klow N.slots)
        C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase) :
    NativeNodeLowAt hH N hbeta g Cs Sp degreeLow Klow hT hbetaHi 0 := by
  letI : Cycle63.AffineLedger:=N.ledger
  intro caps hm hrow hfit hwL hwr hslots haff
  exact Cycle153Terminal.terminal_low_zero_return M H hH C.W hbeta g 2
    (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs (fun _ _ _=>True)
    (fun _ _ _ _ _=>True) (Sp N.slots) (degreeLow N.slots) (Klow N.slots)
    C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase N.localBase_gt_one
    (N.input hH) N.profiles caps (fun i=>C.theta i) (fun i=>C.originalWeight i/N.unit)
    (fun i=>C.sigma i) (fun i=>C.frequency i) hm N.state.puncture 1 20 N.state.rowWidth
    N.state.puncture_ne_zero squarefree_one (by norm_num) N.state.puncture_bound
    N.state.row_nonneg hrow hfit trivial N.height C.slotMesh
    (fun i=>div_nonneg (C.originalWeight_nonneg i) N.unit_pos.le)
    hwL hwr C.slotMesh_pos.le N.weight_mesh (fun i=>C.sigma_fixed i)
    N.height_nonneg N.frequency_bound hT hbetaHi hslots haff hclosed

/-- Rounding costs the actual global error 42/grid, uniformly over all
reachable sources. This follows from the retained physical coordinates. -/
theorem node_own_amplifier_receipt {j : Fin 4}(N : ReachableNode C j) :
    letI : Cycle63.AffineLedger:=N.ledger
    N.unit*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit)))≤
      ![Coordinates.a1 N.coordinates,Coordinates.a2 N.coordinates,
        Coordinates.a3 N.coordinates,Coordinates.a4 N.coordinates] j+42/C.gridDenominator := by
  letI : Cycle63.AffineLedger:=N.ledger
  have hgrid : 0<(C.gridDenominator:ℝ) := by exact_mod_cast C.grid_positive
  have he : 0≤42*(1/(C.gridDenominator:ℝ)) := by positivity
  have h:=mul_le_mul_of_nonneg_left (actual_node_amp_bounds N).2 N.unit_pos.le
  have hc:=mul_le_mul_of_nonneg_right N.unit_le_one he
  have heq : N.unit*(modelAmplification j N.coordinates/N.unit)=modelAmplification j N.coordinates := by
    field_simp [ne_of_gt N.unit_pos]
  have hm : modelAmplification j N.coordinates=
      ![Coordinates.a1 N.coordinates,Coordinates.a2 N.coordinates,
        Coordinates.a3 N.coordinates,Coordinates.a4 N.coordinates] j := by fin_cases j <;> rfl
  rw [mul_add,heq,hm] at h
  simp only [mul_one_div,one_mul] at h hc
  linarith only [h,hc]

/-- Assemble the terminal NodeOutput from the proved native source
interfaces. The literal own HIGH forest supplies every arithmetic receipt;
the native OLD source pays LOW without any child callback. All constants
are parameters fixed by the finite uniform native schedules before Z. -/
theorem actual_terminal_node_output (N : ReachableNode C (3:Fin 4))
    (hgrid : C.gridDenominator=Cycle153.RegionalSchedule.gridSize)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule)(epsilon tauLow lossNeeded tauT : ℝ)
    (Psi : 𝓢(ℝ,ℂ))(SH : Finset (ℕ×ℕ))(dh degree : ℕ)(S : Finset (ℕ×ℕ))
    (Cenergy Chigh Cs Kh Kclass Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ))
    (Sp : Finset alpha→Finset (ℕ×ℕ))(degreeLow : Finset alpha→ℕ)(Klow : Finset alpha→ℝ)
    (hT : 2<N.localBase^g.τ)(hCenergy : 0≤Cenergy)(hChigh : 0≤Chigh)(hKh : 0≤Kh)
    (hclass : Kclass≤C.highClassCap)(hloss : lossNeeded+epsilon≤terminalLossCap (3:Fin 4))
    (htau : tauLow≤tauT)(hheight : C.Tz=N.localBase^tauT)
    (hAt : letI : Cycle63.AffineLedger:=N.ledger
      RegionalAtState (α:=alpha) M H hH C.W C.W_smooth C.W_support hbeta hbetaHi
        g 2 20 C.slotMesh epsilon (by norm_num) Psi SH dh degree S Cenergy Chigh Cs
        Sp degreeLow Klow (by norm_num) C.slotMesh_pos.le C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase)
    (hclosed : letI : Cycle63.AffineLedger:=N.ledger
      GeometryAffineLowSelectedSpec (α:=N.slots) M H hH C.W hbeta g 2
        (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs (fun _ _ _=>True)
        (fun _ _ _ _ _=>True) (Sp N.slots) (degreeLow N.slots) (Klow N.slots)
        C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase)
    (hsource : letI : Cycle63.AffineLedger:=N.ledger
      ActualHighNodeAt (base:=prefixDictionary 3) (α:=alpha) M H hH
        C.W C.W_smooth C.W_support hbeta hbetaHi g (1/4) (9/4) 2 20
        C.slotMesh epsilon tauLow C.Bnorm lossNeeded (by norm_num)
        Psi SH dh Kclass Kh C.etaSeed C.Q C.Q_le_M C.fixed_small N.localBase)
    (hamp : letI : Cycle63.AffineLedger:=N.ledger
      3*g.δ≤Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit)))) :
    Nonempty (NodeOutput hH N (Cenergy*(1+Chigh*(2*Kh))) epsilon Bsrc S degree boxes) := by
  letI : Cycle63.AffineLedger:=N.ledger
  obtain ⟨own,hm,hA,ha,hl,hcard,_,hgiven⟩:=actual_reachable_own_high hH N
    hbeta hbetaHi g epsilon tauLow lossNeeded Psi SH dh Kclass Kh hsource hT tauT htau hheight
  have hlossOwn : own.loss≤terminalLossCap (3:Fin 4) := hl.trans_le hloss
  have hcardOwn : ∀b,(Fintype.card (own.record b).Class:ℝ)≤C.highClassCap :=
    fun b=>(hcard b).trans hclass
  have herror0 : 0≤42/(C.gridDenominator:ℝ) := by positivity
  have herrorFine : 42/(C.gridDenominator:ℝ)≤1/1000000000000 := by
    rw [hgrid];norm_num [Cycle153.RegionalSchedule.gridSize]
  have hAmpOwn : N.unit*own.amp≤
      ![Coordinates.a1 N.coordinates,Coordinates.a2 N.coordinates,
        Coordinates.a3 N.coordinates,Coordinates.a4 N.coordinates] (3:Fin 4)+42/C.gridDenominator := by
    rw [ha];exact node_own_amplifier_receipt N
  let receipt:=native_own_forest_receipt hH N own hm hA ha hlossOwn hcardOwn
    (42/C.gridDenominator) herror0 herrorFine hAmpOwn Bsrc boxes
  have hvalue : receipt.family.value=own.value :=
    native_own_forest_receipt_value hH N own hm hA ha hlossOwn hcardOwn
      (42/C.gridDenominator) herror0 herrorFine hAmpOwn Bsrc boxes
  have hown0:=own.value_nonneg (zero_lt_one.trans N.localBase_gt_one).le
  have hown : own.value≤2*receipt.family.value := by rw [hvalue];linarith
  have hlow:=terminal_node_low_at_zero hH N hbeta hbetaHi g Cs Sp degreeLow Klow hT hclosed
  have hlow' : NativeNodeLowAt hH N hbeta g Cs Sp degreeLow Klow hT hbetaHi
      (0*N.localBase^(-(N.state.rowWidth+3*g.δ-
        Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
          (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit)))+epsilon))*receipt.family.value) := by
    simpa only [zero_mul] using hlow
  have he:=actual_node_at_state_from_whole_forest hH N hbeta hbetaHi g epsilon Psi SH dh degree S
    Cenergy Chigh Cs Sp degreeLow Klow hT hCenergy hChigh hAt own receipt.family Kh 0 hKh le_rfl hown
    hamp hlow' hgiven
  refine ⟨⟨receipt.family,receipt.chronology,receipt.path,receipt.terminalLoss,
    receipt.terminalSource,receipt.classCap,?_⟩⟩
  simpa only [zero_add] using he

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.terminal_node_deletes_old
#print axioms OAI.SevenEighths.Cycle153RegionalLow.terminal_node_low_at_zero
#print axioms OAI.SevenEighths.Cycle153RegionalLow.node_own_amplifier_receipt
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_terminal_node_output
