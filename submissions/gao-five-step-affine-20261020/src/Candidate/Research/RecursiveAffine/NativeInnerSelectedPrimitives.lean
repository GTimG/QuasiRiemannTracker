/- All actual ROOT selected-row primitive receipts precede the moving source.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeSelectedPaidGateAtBin
import Candidate.Research.RecursiveAffine.ActualNodeNativeFee
import Candidate.Research.RecursiveAffine.NativeAllRowSourceFacts
import Candidate.Research.RecursiveAffine.ActualRootSourceThresholds
import Candidate.Research.RecursiveAffine.NativeAllRowMasks
import Candidate.Cycle63.Physical.InitialMass.GeometryLossSchedule

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153ActualSourceGates
noncomputable section
open scoped Classical BigOperators SchwartzMap HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass Cycle63FinalCapacity
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open Cycle153Reachable Cycle153RegionalLow Cycle153RootStep Cycle153SourceSchedule Cycle153.RegionalSchedule
open Cycle153ActualSourceGates Cycle153JointCount
open CenteredMomentCommonProfile CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands
open CenteredMomentSourceLiveColumn
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
open Cycle153ActualRootSourceGates Cycle153ReachableGeometry Cycle153SourceUniform Cycle63FinalNatural
open CenteredMomentNaturalFixedRaySource CenteredMomentEnergyState

/-- Primitive actual-source licences at the literal retained node. All
fields are generated before the moving node, source rows and native bin;
no energy, callback, class payment, or counting conclusion is assumed. -/
structure InnerSelectedPrimitivePacket
    (hH : RayOrthogonality.globalUnits M ≤ H)(C : SourceContext (α:=alpha) M H)
    (j : Fin 4)(N : ReachableNode C j)[L : Cycle63.AffineLedger](Cs : ℝ)
    (caps : GeometryAffineLowSourceGates (N.input hH) N.profiles Cs N.localBase)
    (epsNode : ℝ)(budget : ℕ) where
  gates :
    ∀(R seed : Ideal O)(hseed : Squarefree seed)(reflected : Bool)(key : ℤ×(Fin 5→ℤ))
      ,
    ∀(epsRow : ℝ),0 ≤ epsRow → epsRow ≤ nativeDriverRate budget →
    ∀sideLower : ℝ,
    let massLoss:=3*nativeDriverRate budget-sideLower
    let sideError:=actualSideError N.localBase budget
    ∀hside : ∀l : FirstColumnIndex (geometryFirstSource (N.input hH) R seed
        (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key),
      massLoss+lowLabelSide reflected N.localBase (Real.logb N.localBase (volume (N.input hH)))
        (geometryFirstLabel (N.input hH) R seed (N.localBase^N.state.rowWidth)
          N.localBase (nativeMu/64) (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key l) ≤ sideError,
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
      (nativeMu/64) (nativeMu/8) epsRow (9/4) firstHeight (Fintype.card N.slots)
      key caps.zero₁ caps.zero₂ firstIndex massLoss sideError (fun l=>hside (firstIndex l).1.val) r
    p.SourceGates ∧ p.FineSourceGates
  sourceMesh : C.slotMesh≤localSlotMesh epsNode
  rowCap : N.state.rowWidth≤2
  slotWindow : Cycle63.AffineLedger.slotFloor≤∑i,Real.logb N.localBase ((N.input hH).P i) ∧
    (∑i,Real.logb N.localBase ((N.input hH).P i))≤Cycle63.AffineLedger.slotTop
  affine : length N.localBase (N.input hH).X₁+length N.localBase (N.input hH).X₂+
    Cycle63.AffineLedger.lam*(∑i,Real.logb N.localBase ((N.input hH).P i))≤Cycle63.AffineLedger.B
  prefixSmall : Real.logb N.localBase 4+2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+(nativeMu/64)/2≤1
  fit : N.state.rowWidth+Real.logb N.localBase ((N.input hH).η.modulus.absNorm:ℝ)≤1+(nativeMu/8)/2
  constants : Real.logb N.localBase CenteredMomentFirstPhysicalSource.fixedPresentationCost+
    2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+Real.logb N.localBase 1+
    Real.logb N.localBase (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤(nativeMu/8)/2
  pad : supportPadding (Fintype.card N.slots) (9/4) (N.input hH).b₁ (N.input hH).b₂ N.localBase≤nativeMu/8
  omega : frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8≤1/1000000000000000
  widthError : nativeMu/8+(nativeMu/64)/2≤1/1000000000000000
  finite : Real.logb N.localBase 128+252*(1/C.gridDenominator:ℝ)+actualNodeLocalSourcePad (hH:=hH) N≤1/100000000000000000000
  fee : ∀(R : Finset N.slots)
    (hd : (∑i∈R,C.originalWeight i/N.unit)≤nodeDetectorDeletion N+C.slotMesh),
    (actualNodeGlobalFee (hH:=hH) N epsNode budget R hd).amount≤1/1000000000000000
  gridFine : (1/C.gridDenominator:ℝ)≤1/10000000000000000000000000000000000000000
  gridMargin : 500*(1/C.gridDenominator:ℝ)≤positionMargin
  masks : ∀(reflected second : Bool)(firstHeight : ℝ)(key : ℤ×(Fin 5→ℤ))
    {Label : Type}[Fintype Label]
    (firstIndex : Label→GeometryLowFirstIndex reflected (N.input hH) N.state.puncture 1
      (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key),
    (∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected (N.input hH) N.state.puncture 1 (N.localBase^N.state.rowWidth)
        N.localBase (nativeMu/64) (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key
        (firstIndex l).1.val) N.state.puncture (N.input hH).ν (N.input hH).W (N.input hH).P≠0)→
    ∀r : NativeLowRows reflected (N.input hH) N.state.puncture 1 N.localBase N.state.rowWidth (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key caps.zero₁ caps.zero₂ firstIndex,
    let datum:=geometryLowSecondDatum reflected (N.input hH) N.state.puncture 1 N.localBase N.state.rowWidth
      (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key (firstIndex r.val.1) caps.zero₁ caps.zero₂ r.val.2
    let E:=if second then datum.D else datum.C
    datum.R*E≠0 ∧ ((datum.R*E).absNorm:ℝ)≤N.localBase^(28:ℝ) ∧ Supported E ∧ datum.seed∣E
  decorated :
    ∀(R seed : Ideal O)(hseed : Squarefree seed)(reflected : Bool)(bin : ℤ×(Fin 5→ℤ))
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
      N.localBase 250000 (rootNativeDyadBox C.globalBase budget)
      ((),nativeLowHistoryCode reflected (N.input hH) R seed N.localBase N.state.rowWidth (nodeSourceAmp N)
        (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots) N.localBase_gt_one
        bin caps.zero₁ caps.zero₂ firstIndex r)

/-- One original-base threshold supplies all primitive gates at every
actual retained base and node. The scheduled budget is the genuine
ambient native budget; the surviving row cardinality only satisfies its
bound and is kept literal in fees and source factors. -/
theorem eventually_actual_inner_selected_primitives
    (hH : RayOrthogonality.globalUnits M ≤ H)(etaSeed : Character)
    (epsNode : ℝ)(heps : 0<epsNode)(budget : ℕ) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(C : SourceContext (α:=alpha) M H)(j : Fin 4)(N : ReachableNode C j)
      (Cs : ℝ)(caps : letI : Cycle63.AffineLedger:=N.ledger
      GeometryAffineLowSourceGates (N.input hH) N.profiles Cs N.localBase),
      C.globalBase=Z→j.val<3→C.gridDenominator=gridSize→
      C.slotMesh≤localSlotMesh epsNode→Fintype.card N.slots≤budget→
    letI : Cycle63.AffineLedger:=N.ledger
    Nonempty (InnerSelectedPrimitivePacket hH C j N Cs caps epsNode budget) :=by
  have ht:=eventually_all_rebased_sources _ (eventually_actual_root_native_thresholds etaSeed budget)
  have hm:=eventually_all_rebased_sources _ (eventual_actual_selected_all_row_masks budget)
  filter_upwards [eventual_actual_selected_paid_gates_at_bin (alpha:=alpha) hH budget,
    ht,eventually_actual_node_fee_budget (alpha:=alpha) (hH:=hH) epsNode heps budget,
    eventually_actual_native_pad budget,eventually_actual_source_small budget,
    hm,eventual_actual_all_row_source_facts (alpha:=alpha) hH budget] with Z hg ht hf hp ho hm hd
  refine ⟨hg.1,?_⟩
  intro C j N Cs caps hbase hj hgrid hmesh hcard
  letI : Cycle63.AffineLedger:=N.ledger
  have htLocal:=ht.2 N.unit N.unit_floor
  have hmLocal:=hm.2 N.unit N.unit_floor
  have hs:=ho.2 N.unit N.unit_floor
  rw [←hbase,←N.localBase_eq] at htLocal hmLocal hs
  have hcardR : (Fintype.card N.slots:ℝ)≤budget:=by exact_mod_cast hcard
  have hlog : 0≤Real.logb N.localBase (9/4):=Real.logb_nonneg N.localBase_gt_one (by norm_num)
  have hcost : 2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)≤
      2*(budget:ℝ)*Real.logb N.localBase (9/4):=by nlinarith only [mul_le_mul_of_nonneg_right hcardR hlog]
  have hb1 : (N.input hH).b₁=(9/4:ℝ):=rfl
  have hb2 : (N.input hH).b₂=(9/4:ℝ):=rfl
  have hpadFull:=hp.2 N.unit N.unit_floor (Fintype.card N.slots) hcard (9/4)
    (N.input hH).b₁ (N.input hH).b₂ (by norm_num) le_rfl hb1.le hb2.le
  rw [←hbase,←N.localBase_eq] at hpadFull
  have hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator:ℝ)+
      actualNodeLocalSourcePad (hH:=hH) N≤1/100000000000000000000:=by
    simpa only [hgrid,actualNodeLocalSourcePad,div_eq_mul_inv,one_mul,add_assoc,
      show (10:ℝ)^20=100000000000000000000 by norm_num] using hpadFull
  have hlog128 : 0≤Real.logb N.localBase 128:=Real.logb_nonneg N.localBase_gt_one (by norm_num)
  have hg0 : 0≤252*(1/C.gridDenominator:ℝ):=by positivity
  have hpad : supportPadding (Fintype.card N.slots) (9/4) (N.input hH).b₁ (N.input hH).b₂ N.localBase≤nativeMu/8:=by
    change actualNodeLocalSourcePad (hH:=hH) N≤_
    have he : (1/100000000000000000000:ℝ)≤nativeMu/8:=by norm_num [nativeMu,primitiveError]
    linarith only [hfinite,hlog128,hg0,he]
  have hfit : N.state.rowWidth+Real.logb N.localBase ((N.input hH).η.modulus.absNorm:ℝ)≤1+(nativeMu/8)/2:=by
    have hw:=N.width_le_one
    unfold NaturalState.width at hw
    have heta : (N.input hH).η=N.state.character:=rfl
    rw [heta]
    have hnorm : (0:ℝ)<(N.state.character.modulus.absNorm:ℝ):=by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr N.state.character.modulus_ne_bot)
    have hchar:=(Real.logb_le_iff_le_rpow N.localBase_gt_one hnorm).mpr N.state.modulus_bound
    have hmu:=nativeMu_pos
    linarith only [hw,hchar,hmu]
  have hrow : N.state.rowWidth≤2:=by
    have hw:=N.width_le_one
    unfold NaturalState.width at hw
    linarith only [hw,N.state.character_nonneg]
  have hlogScale : (∑i,Real.logb N.localBase ((N.input hH).P i))=∑i : N.slots,C.originalWeight i/N.unit:=by
    apply Finset.sum_congr rfl
    intro i _
    have hi : (N.input hH).P i=N.localBase^(C.originalWeight i/N.unit):=rfl
    rw [hi]
    exact Real.logb_rpow (zero_lt_one.trans N.localBase_gt_one) N.localBase_gt_one.ne'
  have hslots : Cycle63.AffineLedger.slotFloor≤∑i,Real.logb N.localBase ((N.input hH).P i) ∧
      (∑i,Real.logb N.localBase ((N.input hH).P i))≤Cycle63.AffineLedger.slotTop:=by
    rw [hlogScale]
    exact ⟨N.window.slots_ge,N.window.slots_le⟩
  have haff : length N.localBase (N.input hH).X₁+length N.localBase (N.input hH).X₂+
      Cycle63.AffineLedger.lam*(∑i,Real.logb N.localBase ((N.input hH).P i))≤Cycle63.AffineLedger.B:=by
    rw [hlogScale]
    exact N.window.plane
  refine ⟨{ gates := ?_
            sourceMesh := hmesh
            rowCap := hrow
            slotWindow := hslots
            affine := haff
            prefixSmall := ?_
            fit := hfit
            constants := ?_
            pad := hpad
            omega := ?_
            widthError := ?_
            finite := hfinite
            fee := ?_
            gridFine := ?_
            gridMargin := ?_
            masks := ?_
            decorated := ?_ }⟩
  · exact hg.2 C j N hbase hcard Cs caps
  · linarith only [htLocal.2.2.1,hcost]
  · linarith only [htLocal.2.2.2.1,hcost]
  · exact hs.2.1.trans (by norm_num)
  · norm_num [nativeMu,primitiveError]
  · intro R hsum
    have hh:=hf.2 C j N hbase hgrid hmesh hcard R hsum
    simpa only [show (10:ℝ)^15=1000000000000000 by norm_num] using hh
  · norm_num [hgrid,gridSize]
  · norm_num [hgrid,gridSize,positionMargin]
  · intro reflected second firstHeight key Label _ firstIndex hfirst r datum E
    have hvolume3 : volume (N.input hH)≤N.localBase^(3:ℝ):=
      caps.volume.trans (Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le (by norm_num))
    have hh:=hmLocal.2 reflected second (N.input hH) N.state.puncture 1 N.state.rowWidth
      (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) firstHeight 20 N.localBase_gt_one hcard caps.endpoints
      squarefree_one N.state.puncture_ne_zero le_rfl N.state.puncture_bound
      caps.zero₁ caps.zero₂ caps.sourceCap hvolume3 key firstIndex hfirst r
    exact ⟨hh.1,hh.2.2.1,hh.2.2.2.2.2.1,hh.2.2.2.2.2.2⟩
  · simpa only [hbase] using hd.2 C j N hbase hj hcard Cs caps

end
end OAI.SevenEighths.Cycle153ActualSourceGates
#print axioms OAI.SevenEighths.Cycle153ActualSourceGates.eventually_actual_inner_selected_primitives
