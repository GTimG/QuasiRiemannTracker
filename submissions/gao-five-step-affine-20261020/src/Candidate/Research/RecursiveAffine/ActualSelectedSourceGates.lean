/- Actual source-specific coarse/fine gates at the same physical row.
Copyright (c) 2026 Zhongpai Gao. Native geometry by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.ActualSourcePrimitiveSchedule
import Candidate.Research.RecursiveAffine.NativeSelectedPaidSource
import Candidate.Research.RecursiveAffine.NativeCoarseSource
import Candidate.Research.RecursiveAffine.TerminalSourceReceipt
import Candidate.Research.RecursiveAffine.NativeNodeStep
import Candidate.Cycle63.Physical.InitialMass.GeometryMainHighSourceCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowNormalizedPayment

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000
namespace OAI.SevenEighths.Cycle153ActualSourceGates
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentFirstCanonicalFamily CenteredMomentCanonicalFirst CenteredMomentOriginalCommonHarmonic
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState
open Cycle153Reachable Cycle153JointCount Cycle153LowPhysical Cycle153RegionalLow
open Cycle153SourceSchedule Cycle153SourceUniform Cycle153.RegionalSchedule

variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}

/-- Genuine same-bin mass/side production, exact source norms and the
chosen native small-error schedule jointly populate the actual paid
node's gates. All thresholds precede the moving source and selected row.
Neither coarse/fine gates nor any count/energy/fee bound is an input. -/
theorem eventual_actual_selected_paid_gates
    (hH : RayOrthogonality.globalUnits M ≤ H)(budget : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(C : SourceContext (α:=alpha) M H)(j : Fin 4)(N : ReachableNode C j),C.globalBase=Z→
      Fintype.card N.slots ≤ budget→
    letI : Cycle63.AffineLedger:=N.ledger
    ∀(Cs : ℝ)(caps : GeometryAffineLowSourceGates (N.input hH) N.profiles Cs N.localBase)
      (R seed : Ideal O)(hseed : Squarefree seed)(reflected : Bool)(key : ℤ×(Fin 5→ℤ))
      (Psi : 𝓢(ℝ,ℂ)),
    ∃exponent sideLower : ℝ,
    let massLoss:=3*nativeDriverRate budget-sideLower
    let sideError:=actualSideError N.localBase budget
    ∃hside : ∀l : FirstColumnIndex (geometryFirstSource (N.input hH) R seed
        (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key),
      massLoss+lowLabelSide reflected N.localBase (Real.logb N.localBase (volume (N.input hH)))
        (geometryFirstLabel (N.input hH) R seed (N.localBase^N.state.rowWidth)
          N.localBase (nativeMu/64) (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key l) ≤ sideError,
      (∀l : FirstColumnIndex (geometryFirstSource (N.input hH) R seed
        (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key),
        geometryFirstHighMass reflected (N.input hH) R seed Psi N.state.rowWidth N.localBase (nativeMu/64)
          (nativeDriverRate budget) (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key l ≤
          geometryHighFactor reflected (geometrySupportConstant budget 1 (1/4) (1/4)) key*N.localBase^massLoss) ∧
    ∀(second : Bool)(firstHeight : ℝ){Label : Type}[Fintype Label]
      (firstIndex : Label→GeometryLowFirstIndex reflected (N.input hH) R seed (N.localBase^N.state.rowWidth)
        N.localBase (nativeMu/64) (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key),
      (∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected (N.input hH) R seed (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val)
        R (N.input hH).ν (N.input hH).W (N.input hH).P≠0)→
    ∀r : NativeLowRows reflected (N.input hH) R seed N.localBase N.state.rowWidth (nodeSourceAmp N)
        (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
        N.localBase_gt_one key caps.zero₁ caps.zero₂ firstIndex,
    let p:=actualSelectedPaidNode N reflected second (N.input hH) R seed N.state.rowWidth (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (nativeDriverRate budget) (9/4) firstHeight (Fintype.card N.slots)
      key caps.zero₁ caps.zero₂ firstIndex massLoss sideError (fun l=>hside (firstIndex l).1.val) r
    p.SourceGates ∧ p.FineSourceGates := by
  have hmu0:=div_pos nativeMu_pos (by norm_num : (0:ℝ)<8)
  have hmu1 : nativeMu/8 ≤ 1 :=by norm_num [nativeMu,primitiveError]
  have hcaps:=eventual_actual_geometry_main_high_source_caps budget (9/4) (9/4) (nativeMu/8)
    (by norm_num) (by norm_num) hmu0 hmu1
  have hcapsGlobal:=eventually_all_rebased_sources _ hcaps
  filter_upwards [hcapsGlobal,eventually_actual_source_small budget] with Z hc hs
  refine ⟨hc.1,?_⟩
  intro C j N hbase hcard
  letI : Cycle63.AffineLedger:=N.ledger
  intro Cs caps R seed hseed reflected key Psi
  have hsmall:=hs.2 N.unit N.unit_floor
  have hsourceCaps:=hc.2 N.unit N.unit_floor
  rw [←hbase,←N.localBase_eq] at hsmall hsourceCaps
  have hrow1 : N.state.rowWidth ≤ 1 :=by
    have hh:=N.width_le_one
    unfold NaturalState.width at hh
    linarith only [hh,N.state.character_nonneg]
  have hlog : Real.logb N.localBase (volume (N.input hH))=
      length N.localBase N.X1+length N.localBase N.X2+∑i : N.slots,C.originalWeight i/N.unit :=by
    apply mul_left_cancel₀ N.unit_pos.ne'
    exact (N.volume_model (hH:=hH)).trans N.length_eq.symm
  have hlog0 : 0 ≤ Real.logb N.localBase (volume (N.input hH)) :=by
    rw [hlog]
    have h1:=N.positionFacts.windowBottom_pos.trans_le N.window.left_ge
    have h2:=N.positionFacts.windowBottom_pos.trans_le N.window.right_ge
    have hw : 0 ≤ ∑i : N.slots,C.originalWeight i/N.unit :=
      Finset.sum_nonneg (fun i _=>div_nonneg (C.originalWeight_nonneg i) N.unit_pos.le)
    linarith only [h1,h2,hw]
  have hamp0 : 0 ≤ nodeSourceAmp N :=by
    have hcell:=Cycle63.AffineLedger.originalCell_mem ⟨N.window.slots_ge,N.window.slots_le⟩
    have hh:=Cycle63.AffineLedger.amp_pos (Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1)
    rw [nodeSourceAmp_eq_native N] at hh
    exact hh.le
  have hamp1 : nodeSourceAmp N ≤ 1 :=by
    rw [←nodeSourceAmp_eq_native N]
    exact N.actual_amp_le_one
  obtain ⟨exponent,sideLower,hbin,hfirst⟩:=actual_selected_paid_source N reflected budget 1 (1/4)
    (by norm_num) (by norm_num) (N.input hH) R seed Psi N.state.rowWidth (nativeMu/64) 3
    (nativeDriverRate budget) hcard (by rw [caps.lower]) hseed caps.zero₁ caps.zero₂ caps.sourceCap
    (nativeDriverRate_budgets budget).1.le caps.support₁ caps.support₂ key
  refine ⟨exponent,sideLower,?_⟩
  intro massLoss sideError
  let hside : ∀l : FirstColumnIndex (geometryFirstSource (N.input hH) R seed
      (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key),
      massLoss+lowLabelSide reflected N.localBase (Real.logb N.localBase (volume (N.input hH)))
        (geometryFirstLabel (N.input hH) R seed (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key l) ≤ sideError :=fun l=>(hfirst l).2.2
  refine ⟨hside,fun l=>(hfirst l).2.1,?_⟩
  intro second firstHeight Label _ firstIndex hf r p
  have hfirstCaps:=actual_main_low_first_source_gates reflected (N.input hH) R seed
    (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64) 3
    (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) hseed caps.zero₁ caps.zero₂ caps.sourceCap key firstIndex r.val.1
  let original:=mainLowSelectedOriginal reflected (N.input hH) R seed N.localBase N.state.rowWidth (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots) N.localBase_gt_one key
    caps.zero₁ caps.zero₂ firstIndex r
  have hvolume3 : volume (N.input hH) ≤ N.localBase^(3:ℝ) :=
    caps.volume.trans (Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le (by norm_num))
  have hsecondCaps:=hsourceCaps.2 reflected (N.input hH) R seed N.state.rowWidth (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) firstHeight N.localBase_gt_one hcard caps.endpoints hseed
    caps.zero₁ caps.zero₂ caps.sourceCap hvolume3 key 1 1 1 original.val (hf r.val.1)
  have hC : (p.C.absNorm:ℝ) ≤ N.localBase^(4:ℝ) :=hsecondCaps.2.2.1
  have hD : (p.D.absNorm:ℝ) ≤ N.localBase^(4:ℝ) :=hsecondCaps.2.2.2
  have hown : ((if second then p.D else p.C).absNorm:ℝ) ≤ N.localBase^(130:ℝ) :=by
    apply le_trans (by cases second <;> assumption)
    exact Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le (by norm_num)
  have htiny : (1/(10:ℝ)^15) ≤ 1/4 :=by norm_num
  constructor
  · refine ⟨N.unit_le_one,N.state.row_nonneg,hrow1,hlog0,
      (abs_le.mp caps.volumeLog).2.trans (by norm_num),hamp0,hamp1,?_,?_,?_,?_,?_,?_,?_⟩
    · change 0 ≤ frequencyLoss (C.globalBase^N.unit) 32 (nativeMu/64)+nativeMu/8
      rw [←N.localBase_eq];exact hsmall.1
    · change frequencyLoss (C.globalBase^N.unit) 32 (nativeMu/64)+nativeMu/8 ≤ 1/4
      rw [←N.localBase_eq];exact hsmall.2.1.trans htiny
    · exact hsmall.2.2.1
    · exact hsmall.2.2.2.1.trans htiny
    · exact hsmall.2.2.2.2.trans htiny
    · change _ ≤ (C.globalBase^N.unit)^(3:ℝ) ∧ _ ≤ (C.globalBase^N.unit)^(3:ℝ)
      rw [←N.localBase_eq]
      exact ⟨hfirstCaps.2.2.2.2.2.1,hfirstCaps.2.2.2.2.2.2.1⟩
    · change _ ≤ (C.globalBase^N.unit)^(130:ℝ)
      rw [←N.localBase_eq];exact hown
  · have he : (1:ℝ)/10^15=1/1000000000000000 :=by norm_num
    refine ⟨?_,?_,?_⟩
    · simpa only [p,actualSelectedPaidNode,←N.localBase_eq,he] using hsmall.2.1
    · simpa only [p,actualSelectedPaidNode,he] using hsmall.2.2.2.1
    · simpa only [p,actualSelectedPaidNode,he] using hsmall.2.2.2.2

end
end OAI.SevenEighths.Cycle153ActualSourceGates
#print axioms OAI.SevenEighths.Cycle153ActualSourceGates.eventual_actual_selected_paid_gates
