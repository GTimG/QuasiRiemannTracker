/- Actual all-row arithmetic gates before branch/source selection. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeAllRowKeyFacts
import Candidate.Research.RecursiveAffine.NativeGlobalDyadBox
import Candidate.Research.RecursiveAffine.ActualSourcePrimitiveSchedule
import Candidate.Research.RecursiveAffine.NativeNodeStep
import Candidate.Research.RecursiveAffine.TerminalSourceReceipt
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineLowPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighSourceCaps

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentFirstCanonicalFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
open Cycle153Reachable Cycle153JointCount Cycle153SourceSchedule Cycle153SourceUniform
open Cycle153.RegionalSchedule Cycle153ActualSourceGates
open CenteredMomentSourceLiveColumn CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState
attribute [local irreducible] ReachableNode.input nodeSourceAmp nativeLowHistoryCode mainLowSelectedNonzeroRows

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

/-- Genuine uniform native source caps and the actual absolute dyad box
supply counting gates for ALL literal selected rows, including zero,
Direct and OLD branches. No live daughter, successor output, arbitrary
box membership, multiplier estimate or energy/count bound is assumed. -/
theorem eventual_actual_all_row_source_facts
    (hH : RayOrthogonality.globalUnits M ≤ H)(budget : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(C : SourceContext (α:=alpha) M H)(j : Fin 4)(N : ReachableNode C j),C.globalBase=Z→
      j.val<3 → Fintype.card N.slots ≤ budget→
    letI : Cycle63.AffineLedger:=N.ledger
    ∀(Cs : ℝ)(caps : GeometryAffineLowSourceGates (N.input hH) N.profiles Cs N.localBase)
      (R seed : Ideal O)(hseed : Squarefree seed)(reflected : Bool)(bin : ℤ×(Fin 5→ℤ))
      (firstHeight : ℝ){Label : Type}[Fintype Label]
      (firstIndex : Label→GeometryLowFirstIndex reflected (N.input hH) R seed
        (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin),
    (∀l,frozenCoefficient (firstIndex l).2.val (geometryColumnIdeal reflected (N.input hH) R seed
      (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin (firstIndex l).1.val)
      R (N.input hH).ν (N.input hH).W (N.input hH).P≠0)→
    ∀(units : FirstSourceLabel→O),(∀l,IsUnit (units l))→
    ∀r : NativeLowRows reflected (N.input hH) R seed N.localBase N.state.rowWidth (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots) N.localBase_gt_one
      bin caps.zero₁ caps.zero₂ firstIndex,
    DecoratedFacts (fun _ : Unit=>N.presentation.mult) (!reflected) (fun _=>units)
      N.localBase 250000 (rootNativeDyadBox Z budget)
      ((),nativeLowHistoryCode reflected (N.input hH) R seed N.localBase N.state.rowWidth (nodeSourceAmp N)
        (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots) N.localBase_gt_one
        bin caps.zero₁ caps.zero₂ firstIndex r) :=by
  have hmu0:=div_pos nativeMu_pos (by norm_num : (0:ℝ)<8)
  have hmu1 : nativeMu/8 ≤ 1 :=by norm_num [nativeMu,primitiveError]
  have hc:=eventual_actual_geometry_main_high_source_caps budget (9/4) (9/4) (nativeMu/8)
    (by norm_num) (by norm_num) hmu0 hmu1
  have hcGlobal:=eventually_all_rebased_sources _ hc
  choose Cb hCb hboxNative using fun n : Fin (budget+1)=>
    eventual_actual_geometry_main_absolute_box n.val 4 (nativeMu/8)
      (9/4) (9/4) (nativeMu/64) 1 (by norm_num) hmu0 (by norm_num) (by norm_num)
      (div_nonneg nativeMu_pos.le (by norm_num)) (by nlinarith only [nativeMu_pos]) (by norm_num)
  have hbox := Filter.eventually_all.mpr hboxNative
  have hboxGlobal:=eventually_all_rebased_sources _ hbox
  filter_upwards [hcGlobal,hboxGlobal,eventually_actual_source_small budget] with Z hc hb hs
  refine ⟨hc.1,?_⟩
  intro C j N hbase hj hcard
  letI : Cycle63.AffineLedger:=N.ledger
  intro Cs caps R seed hseed reflected bin firstHeight Label _ firstIndex hf units hunits r
  have hcaps:=hc.2 N.unit N.unit_floor
  have hbLocal:=(hb.2 N.unit N.unit_floor) ⟨Fintype.card N.slots,by omega⟩
  have hsmall:=hs.2 N.unit N.unit_floor
  rw [←hbase,←N.localBase_eq] at hcaps hbLocal hsmall
  have hrow1 : N.state.rowWidth ≤ 1 :=by
    have hh:=N.width_le_one
    unfold NaturalState.width at hh
    linarith only [hh,N.state.character_nonneg]
  have hamp0 : 0 ≤ nodeSourceAmp N :=by
    have hcell:=Cycle63.AffineLedger.originalCell_mem ⟨N.window.slots_ge,N.window.slots_le⟩
    have hh:=Cycle63.AffineLedger.amp_pos (Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1)
    rw [nodeSourceAmp_eq_native N] at hh
    exact hh.le
  have hamp1 : nodeSourceAmp N ≤ 1 :=by
    rw [←nodeSourceAmp_eq_native N]
    exact N.actual_amp_le_one
  let original:=mainLowSelectedOriginal reflected (N.input hH) R seed N.localBase N.state.rowWidth
    (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one bin caps.zero₁ caps.zero₂ firstIndex r
  have hvolume3 : volume (N.input hH) ≤ N.localBase^(3:ℝ) :=
    caps.volume.trans (Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le (by norm_num))
  have hc2:=hcaps.2 reflected (N.input hH) R seed N.state.rowWidth (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) firstHeight N.localBase_gt_one hcard caps.endpoints hseed caps.zero₁
    caps.zero₂ caps.sourceCap hvolume3 bin 1 1 1 original.val (hf r.val.1)
  have hsecondC:=hc2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le
    (show (4:ℝ)≤130 by norm_num))
  have hsecondD:=hc2.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le
    (show (4:ℝ)≤130 by norm_num))
  have hboxLocal:=hbLocal.2.2 reflected (N.input hH) R seed N.state.rowWidth (nodeSourceAmp N)
    (nativeMu/8) firstHeight (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _)
    le_rfl caps.endpoints hseed caps.zero₁ caps.zero₂
    (caps.sourceCap.trans (Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le (by norm_num)))
    (caps.volumeLog.trans (by norm_num))
    (by rw [abs_of_nonneg N.state.row_nonneg];linarith only [hrow1])
    (by rw [abs_of_nonneg hamp0];linarith only [hamp1])
    (by rw [abs_of_nonneg hsmall.1];exact hsmall.2.1.trans (by norm_num))
    hamp0 (div_nonneg nativeMu_pos.le (by norm_num)) bin (firstIndex r.val.1).1.val
    (firstIndex r.val.1).1.property (firstIndex r.val.1).2 (hf r.val.1) r.val.2
  have hboxRoot:=local_native_dyad_subset_root C.globalBase N.unit (Fintype.card N.slots) budget
    C.globalBase_gt_one N.unit_pos N.unit_le_one hcard
  rw [←N.localBase_eq,hbase] at hboxRoot
  exact actual_selected_all_row_key_facts N hj reflected (N.input hH) R seed N.state.rowWidth
    (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    bin hseed caps.zero₁ caps.zero₂ caps.sourceCap firstIndex units hunits (rootNativeDyadBox Z budget)
    r (by simpa only [nativeLowHistoryCode,original,mainLowSelectedOriginal,geometryMainOrdinaryDatum,ordinarySecondDatum,geometryLowSecondDatum,actualSecondBlockDatum,actualSecondInputDatum,Cycle63InitialMass.actualSecondArithmeticLabel] using hsecondC)
      (by simpa only [nativeLowHistoryCode,original,mainLowSelectedOriginal,geometryMainOrdinaryDatum,ordinarySecondDatum,geometryLowSecondDatum,actualSecondBlockDatum,actualSecondInputDatum,Cycle63InitialMass.actualSecondArithmeticLabel] using hsecondD)
      (hboxRoot (by simpa only [nativeLowHistoryCode,geometryLowFirstChild] using hboxLocal))
end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.eventual_actual_all_row_source_facts
