/- The actual INNER LOW height splice, preserving one licensed whole receipt.
Copyright (c)2026 Zhongpai Gao. Native height splice by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerLargeHeight
import Candidate.Research.RecursiveAffine.NativeNodeRawLow
import Candidate.Research.RecursiveAffine.NativeInnerCanonicalInvoke
import Candidate.Research.RecursiveAffine.NativeSelectedScalarThreshold

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Cycle153InnerLowSchedule Cycle63FinalCapacity Cycle63FinalNatural Cycle63FinalLow Cycle153ActualColumn HeckeFamily

theorem normalize_raw_small_source
    (Z outer target E Kold Kreturn returned control heightPower : ℝ)(hZ : 0<Z)
    (hraw : Z^outer*E≤(Kold*Z^(outer+target)+Kreturn*returned)*control*heightPower) :
    E≤(Kold*control*Z^target+Z^(-outer)*Kreturn*returned*control)*heightPower:=by
  have hc : Z^(-outer)*Z^outer=(1:ℝ):=by
    rw [←Real.rpow_add hZ]
    simp only [neg_add_cancel,Real.rpow_zero]
  have hm:=mul_le_mul_of_nonneg_left hraw (Real.rpow_nonneg hZ.le (-outer))
  have hl : Z^(-outer)*(Z^outer*E)=E:=by rw [←mul_assoc,hc,one_mul]
  rw [hl] at hm
  apply hm.trans_eq
  rw [Real.rpow_add hZ]
  calc
    _=(Kold*control*Z^target*heightPower)*(Z^(-outer)*Z^outer)+
      Z^(-outer)*Kreturn*returned*control*heightPower:=by ring
    _=_:=by rw [hc,mul_one];ring

theorem splice_actual_raw_physical
    (original : ℕ)(tau : ℝ)(htau : 0<tau)(smallDegree : ℕ)
    (Z outer target firstHeight height t0 u E Kold Kcoarse Kreturn control returned : ℝ)
    (hZ : 1<Z)(htarget : -1≤target)(hheight : 0≤height)
    (hKold : 0≤Kold)(hKcoarse : 0≤Kcoarse)(hKreturn : 0≤Kreturn)
    (hcontrol : 0≤control)(hreturned : 0≤returned)
    (hsmall : 2*(1+|firstHeight|+height+2*Real.pi*(|t0|+|u|))≤Z^tau →
      E≤(Kold*control*Z^target+Z^(-outer)*Kreturn*returned*control)*
        (2*(1+|firstHeight|+height+2*Real.pi*(|t0|+|u|)))^smallDegree)
    (hcoarse : E≤Kcoarse*control*Z^(nativeLowCoarseExponent original original)) :
    Z^outer*E≤
      ((2+4*Real.pi)^(innerLowDegree original tau htau smallDegree)*(Kold+Kcoarse))*
        (control*(1+|firstHeight|+height)^(innerLowDegree original tau htau smallDegree)*
          (1+|t0|)^(innerLowDegree original tau htau smallDegree)*
          (1+|u|)^(innerLowDegree original tau htau smallDegree))*Z^(outer+target)+
      ((2+4*Real.pi)^(innerLowDegree original tau htau smallDegree)*Kreturn)*
        (control*(1+|firstHeight|+height)^(innerLowDegree original tau htau smallDegree)*
          (1+|t0|)^(innerLowDegree original tau htau smallDegree)*
          (1+|u|)^(innerLowDegree original tau htau smallDegree))*returned :=by
  have hZ0:=zero_lt_one.trans hZ
  have hRet : 0≤Z^(-outer)*Kreturn*returned:=by positivity
  have hb:=innerLowDegreeRule original tau htau smallDegree Z target firstHeight height t0 u E
    Kold Kcoarse control 1 (Z^(-outer)*Kreturn*returned) hZ.le htarget hheight hKold hKcoarse
    hcontrol le_rfl hRet (by simpa only [div_one] using hsmall) hcoarse
  have hh:=mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hZ0.le outer)
  have hcancel : Z^outer*Z^(-outer)=(1:ℝ):=by
    rw [←Real.rpow_add hZ0]
    simp only [add_neg_cancel,Real.rpow_zero]
  apply hh.trans_eq
  rw [Real.rpow_add hZ0]
  calc
    _ = ((2+4*Real.pi)^(innerLowDegree original tau htau smallDegree)*(Kold+Kcoarse))*
        (control*(1+|firstHeight|+height)^(innerLowDegree original tau htau smallDegree)*
          (1+|t0|)^(innerLowDegree original tau htau smallDegree)*
          (1+|u|)^(innerLowDegree original tau htau smallDegree))*(Z^outer*Z^target)+
      ((2+4*Real.pi)^(innerLowDegree original tau htau smallDegree)*Kreturn)*
        (control*(1+|firstHeight|+height)^(innerLowDegree original tau htau smallDegree)*
          (1+|t0|)^(innerLowDegree original tau htau smallDegree)*
          (1+|u|)^(innerLowDegree original tau htau smallDegree))*returned*(Z^outer*Z^(-outer)):=by
      simp only [innerLowDegree]
      ring
    _ = _:=by rw [hcancel,mul_one]

open scoped Classical BigOperators SchwartzMap HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentSourceLiveColumn CenteredMomentSecondCanonical
open CenteredMomentOriginalCommonHarmonic CenteredMomentSectorLocalization
open Cycle153SourceSchedule Cycle153Reachable Cycle153SourceReturn
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional LocalMoment
variable {alpha Label : Type}[Fintype alpha][DecidableEq alpha][Fintype Label]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M ≤ H}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
attribute [local irreducible] ReachableNode.input MainLowCompleteCoarseSpec NativeLowCoarseSubsetAt

variable (N : ReachableNode C j)
open Cycle153ActualSourceGates Cycle153InnerLowSchedule CenteredMomentEnergyState


private theorem actual_input_slot_log_sum :
    (∑i,Real.logb N.localBase ((N.input hH).P i))=∑i : N.slots,C.originalWeight i/N.unit:=by
  apply Finset.sum_congr rfl
  intro i hi
  have hPi : (N.input hH).P i=N.localBase^(C.originalWeight i/N.unit):=by
    unfold ReachableNode.input
    rfl
  rw [hPi,Real.logb_rpow (zero_lt_one.trans N.localBase_gt_one) (ne_of_gt N.localBase_gt_one)]

private theorem actual_input_amp_eq :
    letI : Cycle63.AffineLedger:=N.ledger
    (1:ℝ)*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑i,Real.logb N.localBase ((N.input hH).P i))/(1:ℝ))))=
      nodeSourceAmp N :=by
  letI : Cycle63.AffineLedger:=N.ledger
  rw [one_mul,div_one,actual_input_slot_log_sum N,nodeSourceAmp_eq_native N]

theorem actual_node_native_coarse_bound :
    letI : Cycle63.AffineLedger:=N.ledger
    ∀(Cs Kcoarse : ℝ)(hKcoarse : 0≤Kcoarse)
    (coarse : NativeLowCoarseSubsetAt N.slots (Fintype.card alpha) Cs Kcoarse N.localBase)
    (caps : GeometryAffineLowSourceGates (N.input hH) N.profiles Cs N.localBase)
    (epsNode : ℝ)(primitive : InnerSelectedPrimitivePacket hH C j N Cs caps epsNode (Fintype.card alpha))
    (Sp : Finset (ℕ×ℕ))(hzero : (0,0)∈Sp)
    (reflected second : Bool)(firstHeight : ℝ)
    (bin : ℤ×(Fin 5→ℤ))
    (firstIndex : Label→GeometryLowFirstIndex reflected (N.input hH) N.state.puncture 1 (N.localBase^N.state.rowWidth)
      N.localBase (nativeMu/64) (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin)
    (hf : ∀l,frozenCoefficient (firstIndex l).2.val (geometryColumnIdeal reflected (N.input hH) N.state.puncture 1
      (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin (firstIndex l).1.val)
      N.state.puncture (N.input hH).ν (N.input hH).W (N.input hH).P≠0)
    (hinj : Function.Injective (fun l=>(geometryFirstLabel (N.input hH) N.state.puncture 1 (N.localBase^N.state.rowWidth)
      N.localBase (nativeMu/64) (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _)
      bin (firstIndex l).1.val,(firstIndex l).1.val.2.1.val))),
    let rows:=mainLowSelectedNonzeroRows reflected (N.input hH) N.state.puncture 1 N.localBase N.state.rowWidth (nodeSourceAmp N) (nativeMu/64)
      (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots) N.localBase_gt_one bin caps.zero₁ caps.zero₂ firstIndex
    let datum:=fun r : rows=>geometryLowSecondDatum reflected (N.input hH) N.state.puncture 1 N.localBase N.state.rowWidth (nodeSourceAmp N) (nativeMu/64)
      (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots) N.localBase_gt_one bin (firstIndex r.val.1)
      caps.zero₁ caps.zero₂ r.val.2
    ∀(W : 𝓢(ℝ,ℂ))(chi : rows→RayFourExpansion.RayCharacter)(Q : rows→Ideal O)(m : rows→O)
      (t0 u e : ℝ)
      (select : (r : rows)→(x y : RayFourExpansion.RayCharacter)→
        mainLowSourceRows second (ordinarySecondDatum (datum r) (chi r) (Q r) (m r))
          (fun _=>True)→BufferIndex e),
      mainLowPhysicalCompleteCost (Fintype.card N.slots) 1 (1/4) second
          (fun r : rows=>ordinarySecondDatum (datum r) (chi r) (Q r) (m r))
          (fun r=>geometryFirstHighMass reflected (N.input hH) N.state.puncture 1 W N.state.rowWidth N.localBase (nativeMu/64)
            (nativeDriverRate (Fintype.card alpha))
            (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin (firstIndex r.val.1).1.val/
            volume (geometryLowFirstChild reflected (N.input hH) N.state.puncture 1 (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
              (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin firstHeight (firstIndex r.val.1)))
          t0 u select ≤
        Kcoarse*((N.profiles.control Sp)^2*geometryHighFactor reflected
          (geometrySupportConstant (Fintype.card N.slots) 1 (1/4) (1/4)) bin)*
            N.localBase^(nativeLowCoarseExponent (Fintype.card alpha) (Fintype.card alpha)) :=by
  dsimp only
  letI : Cycle63.AffineLedger:=N.ledger
  intro Cs Kcoarse hKcoarse coarse caps epsNode primitive Sp hzero reflected second firstHeight
    bin firstIndex hf hinj W chi Q m t0 u e select
  have hcoarse:=native_low_coarse_subset_receipt N.slots N.ledger (inferInstance : DecidableEq N.slots) (Fintype.card alpha) Cs Kcoarse N.localBase coarse
  have hrow : N.state.rowWidth≤1:=by
    have hw:=N.width_le_one
    unfold NaturalState.width at hw
    linarith only [hw,N.state.character_nonneg]
  have hamp0 : 0≤nodeSourceAmp N:=by
    rw [←nodeSourceAmp_eq_native N]
    have hcell:=Cycle63.AffineLedger.originalCell_mem ⟨N.window.slots_ge,N.window.slots_le⟩
    exact (Cycle63.AffineLedger.amp_pos (Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1)).le
  have hamp : |nodeSourceAmp N|≤4:=by
    rw [abs_of_nonneg hamp0]
    have hamp1 : nodeSourceAmp N≤1:=by
      rw [←nodeSourceAmp_eq_native N]
      exact N.actual_amp_le_one
    exact hamp1.trans (by norm_num)
  have hw0:=frequencyLoss_nonneg N.localBase 32 (nativeMu/64) N.localBase_gt_one (by norm_num)
    (div_nonneg nativeMu_pos.le (by norm_num))
  have homega : |frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8|≤4:=by
    rw [abs_of_nonneg (add_nonneg hw0 (div_nonneg nativeMu_pos.le (by norm_num)))]
    exact primitive.omega.trans (by norm_num)
  have hc:=actual_affine_low_coarse_cost_from_source (Fintype.card alpha) Cs Kcoarse N.localBase
    N.localBase_gt_one hcoarse (N.input hH) N.profiles caps Sp hzero reflected second N.state.puncture 1 squarefree_one
    N.state.rowWidth (nodeSourceAmp N) (nativeMu/8) firstHeight N.state.row_nonneg hrow hamp0 hamp homega
    (div_nonneg nativeMu_pos.le (by norm_num)) bin firstIndex hf hinj W chi Q m t0 u e select
  have hcard : Fintype.card N.slots ≤ Fintype.card alpha :=by
    simpa only [Fintype.card_coe,Finset.card_univ] using Finset.card_le_card (Finset.subset_univ N.slots)
  have hexponent : nativeLowCoarseExponent (Fintype.card N.slots) (Fintype.card alpha) ≤
      nativeLowCoarseExponent (Fintype.card alpha) (Fintype.card alpha) :=by
    have hh : (Fintype.card N.slots:ℝ) ≤ (Fintype.card alpha:ℝ):=by exact_mod_cast hcard
    unfold nativeLowCoarseExponent
    nlinarith only [hh]
  have hcontrol : 0 ≤ (N.profiles.control Sp)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card N.slots) 1 (1/4) (1/4)) bin :=by
    exact mul_nonneg (sq_nonneg _) (geometry_high_factor_pos reflected _ bin
      (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  have hcmax:=hc.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le hexponent)
    (by simpa only [mul_assoc] using mul_nonneg hKcoarse hcontrol))
  simpa only [mul_assoc] using hcmax

end
end OAI.SevenEighths.Cycle153RegionalLow

#print axioms OAI.SevenEighths.Cycle153RegionalLow.normalize_raw_small_source
#print axioms OAI.SevenEighths.Cycle153RegionalLow.splice_actual_raw_physical
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_node_native_coarse_bound
