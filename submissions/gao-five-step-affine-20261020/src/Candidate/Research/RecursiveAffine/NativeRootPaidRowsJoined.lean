/- The actual ROOT paid-column outputs are summed with their original native coefficients.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedRawColumnsSum
import Candidate.Research.RecursiveAffine.NativeSelectedScalarLabels
import Candidate.Research.RecursiveAffine.NativeSelectedFamilyResidual
import Candidate.Research.RecursiveAffine.NativeRootColumnPaidResult
import Candidate.Research.RecursiveAffine.NativeRootPaidSource

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass Cycle63FinalLow Cycle63FinalCapacity
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentCommonProfile CenteredMomentFiniteProfileExceptional Cycle153Geometry Cycle153JointCount
open CenteredMomentSourceLiveColumn CenteredMomentOriginalCommonHarmonic CenteredMomentFirstCanonicalFamily
open CenteredMomentSecondCanonicalScalar CenteredMomentEnergyState CenteredMomentFirstAmplificationChoice
open Cycle153RegionalLow Cycle153SourceSchedule Cycle153Reachable Cycle153RootStep Cycle153ActualSourceGates
variable {alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M≤H}{C : SourceContext (α:=alpha) M H}
noncomputable local instance rootPaidRowsJoinedLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger

private theorem source_column_factor {energy K F own old ret pad : ℝ}
    (h : energy≤(K*F*own*pad)*(old+ret)) :
    energy≤K*F*own*(old+ret)*pad :=by
  calc
    energy≤(K*F*own*pad)*(old+ret):=h
    _=K*F*own*(old+ret)*pad:=by ring

/-- Sum the SAME actual paid results. The reciprocal scalar payment and
first-bin mass bound are proved from the native source producers; every
family and deletion is taken from its unchanged one-column result. -/
theorem actual_root_paid_rows_joined
    (s : Input alpha)(p : Profiles (1/4) (9/4))(Cs : ℝ)
    (caps : GeometryAffineLowSourceGates s p Cs C.globalBase)
    (budget : ℕ)(hcard : Fintype.card alpha≤budget)
    (g : GeometryAffineLowSchedule)(epsNode epsShell epsV : ℝ)
    (hepsShell : 0≤epsShell)(hepsV : 0<epsV)
    (hlarge : actualSelectedScalarThreshold budget epsV hepsV≤C.globalBase)
    (reflected second : Bool)(firstHeight : ℝ)(key : ℤ×(Fin 5→ℤ))
    (hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key)
    (hf1 : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val)
      1 s.ν s.W s.P≠0)
    (Psi : 𝓢(ℝ,ℂ))(sideLower : ℝ)
    (hside : ∀l,sideLower≤geometryHighSide reflected (Real.logb C.globalBase (volume s))
      (geometryExponents s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (nativeMu/64) (firstIndex l).1.val.1.val))
    (mesh : ℝ)(hmesh : 0 ≤ mesh)(feeBudget : ℕ)
    (Cg fixed : ℝ)(hCg : 0≤Cg)(hfixed : 0≤fixed)
    (constant epsilon Bsrc : ℝ)(control : Finset (ℕ×ℕ))(degree : ℕ)
    (boxes : ℕ→Finset (Fin 4→ℤ)) :
    let Z:=C.globalBase
    let amp:=rootSourceAmp C.originalWeight
    let Rows:=NativeLowRows reflected s 1 1 Z 1 amp (nativeMu/64) (nativeMu/8) (9/4)
      firstHeight (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2 firstIndex
    let first:=fun l=>geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val
    let label:=fun r : Rows=>actualSecondSupportedLabel _ _ _ _ _ _ _ r.val.2
      (actual_main_low_selected_inactive reflected s 1 1 Z 1 amp (nativeMu/64) (nativeMu/8)
        (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2 firstIndex r)
    let datum:=fun r : Rows=>geometryLowSecondDatum reflected s 1 1 Z 1 amp (nativeMu/64) (nativeMu/8)
      (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2
    let childSrc:=fun l=>geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key firstHeight (firstIndex l)
    let radius:=fun r : Rows=>firstMainRadius reflected (Z^(1:ℝ)) (volume s) Z (nativeMu/64)
      (3*amp) (nativeMu/8) (first r.val.1)
    let nominal:=fun r : Rows=>secondNominal 1 Z amp (frequencyLoss Z 32 (nativeMu/64)+nativeMu/8)
      (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
      (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
      (label r).1.1 (label r).1.2 (label r).2.val
    let allowance:=fun r : Rows=>lowAllowance Z
      (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
      (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
      (label r).1.1 (label r).1.2 (if second then (label r).1.2 else (label r).1.1)
    let ownNorm:=fun r : Rows=>((if second then (label r).1.2 else (label r).1.1).absNorm:ℝ)
    let common:=nativeMu/8+(nativeMu/64)/2-Cycle63.AffineLedger.lowReserve+nativeMu/64+
      2*g.δ*31*(Fintype.card alpha:ℝ)+Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)*
        (frequencyLoss Z 32 (nativeMu/64)+nativeMu/8+nativeMu/8)+Cycle63.AffineLedger.q*mesh
    let pad:=actualRootSourcePad C s
    let mass:=fun l=>geometryFirstHighMass reflected s 1 1 Psi 1 Z (nativeMu/64) g.δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val
    let physical:=geometryHighFactor reflected (geometrySupportConstant budget 1 (1/4) (1/4)) key
    let outer:=1+3*g.δ-amp+oldLoss epsNode
    let fees:=3*g.δ-sideLower+3*g.δ+oldLoss epsNode+epsV+130*epsShell+pad+
      2*g.δ*31*(Fintype.card alpha:ℝ)+Cycle63.AffineLedger.q*mesh
    ∀(rawRoot : Rows→O)(paid : Rows→NativePaidPathNode Z)(energy : Rows→ℝ)
      (result : ∀r,RootColumnPaidResult (hH:=hH) C s (paid r) epsNode feeBudget mesh hmesh
        (rawRoot r) constant epsilon Bsrc control degree boxes (energy r)
        (Cg*fixed*(ownNorm r)^(epsShell-1)*Z^pad)
        (Z^(nominal r+amp+common+allowance r))
        (fun R=>Z^(2*g.δ*31*(Fintype.card alpha:ℝ)+Cycle63.AffineLedger.q*((∑i∈R,C.originalWeight i/1)+mesh)))),
    Z^outer*(∑r : Rows,(mass r.val.1/volume (childSrc r.val.1)*radius r*
      normalizer (label r).1.1 (label r).1.2 (label r).2.val)*energy r)≤
      Z^outer*Cycle153LowPhysical.nativeOldSelectedCost reflected second s 1 Z 1 amp
        (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one
        key hz1 hz2 firstIndex Psi g.δ epsShell (common+pad) Cg fixed+
      Cg*fixed*physical*(∑r : Rows,Z^(1+actualHighCoordinates reflected (!reflected) second
        (first r.val.1) (label r).1.1 (label r).1.2 (label r).2.val Z 1
        (Real.logb Z (volume s)) amp (nativeMu/64) (nativeMu/8) epsV 0+
        Cycle63.AffineLedger.q*(∑i∈(result r).deleted,C.originalWeight i)+fees)*(result r).family.value) :=by
  intro Z amp Rows first label datum childSrc radius nominal allowance ownNorm common pad mass physical outer fees
    rawRoot paid energy result
  have hphysical : 0≤physical:=(geometry_high_factor_pos reflected
    (geometrySupportConstant budget 1 (1/4) (1/4)) key
    (geometrySupportConstant_pos budget 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
  let hpay:=actual_selected_scalar_labels budget epsV hepsV Z C.globalBase_gt_one hlarge
    s p Cs caps hcard reflected second 1 1 (by simp) 1 amp firstHeight common pad epsShell hepsShell
    key firstIndex hf1
  have hsum:=actual_selected_raw_columns_sum reflected second s 1 1 Z 1 amp (nativeMu/64) (nativeMu/8)
    epsV (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2 firstIndex
    g.δ (oldLoss epsNode) common pad (3*g.δ-sideLower) epsV 130 epsShell
    (2*g.δ*31*(Fintype.card alpha:ℝ)) Cycle63.AffineLedger.q mesh Cg fixed physical
    hCg hfixed hphysical C.originalWeight (fun r=>(result r).deleted) rawRoot (fun r=>(result r).family)
    mass (fun r=>nominal r+amp+common+allowance r) allowance energy
    (fun r=>(datum r).hC) (fun r=>(datum r).hD)
    (fun r=>geometry_first_high_mass_nonneg reflected s 1 1 Psi 1 Z (nativeMu/64) g.δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex r.val.1).1.val)
    (fun _=>CenteredMomentAmplificationChildInput.volume_pos _)
    (fun r=>(first_main_radius_pos reflected (Z^(1:ℝ)) (volume s) Z (nativeMu/64)
      (3*amp) (nativeMu/8) (zero_lt_one.trans C.globalBase_gt_one) (first r.val.1)).le)
    (fun _=>le_rfl) hpay
    (fun r=>actual_geometry_low_uniform_mass reflected budget 1 (1/4) (by norm_num) (by norm_num)
      s 1 1 Psi 1 Z (nativeMu/64) 3 g.δ sideLower C.globalBase_gt_one
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) g.δ_pos.le hcard
      (by rw [caps.lower]) (by simp) hz1 hz2 caps.sourceCap caps.support₁ caps.support₂
      key (firstIndex r.val.1).1.val (hside r.val.1))
    (fun r=>by
      have h:=(result r).energy_bound
      simp only [div_one] at h
      exact source_column_factor h)
  let pay0:=fun r : Rows=>Z^(-amp)*(radius r/volume (childSrc r.val.1))*
    (normalizer (label r).1.1 (label r).1.2 (label r).2.val*(ownNorm r)^(epsShell-1))*
    Z^(nominal r+amp+common+pad)
  have hold : (∑r : Rows,Cg*fixed*(mass r.val.1*Z^amp)*(pay0 r*Z^(allowance r)))=
      Cycle153LowPhysical.nativeOldSelectedCost reflected second s 1 Z 1 amp (nativeMu/64)
        (nativeMu/8) (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2
        firstIndex Psi g.δ epsShell (common+pad) Cg fixed :=by
    unfold Cycle153LowPhysical.nativeOldSelectedCost
    apply Finset.sum_congr rfl
    intro r hr
    simp only [pay0,add_assoc]
    rfl
  exact replace_selected_old_cost hsum hold
end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actual_root_paid_rows_joined
