/- The genuine large-height LOW branch, with a literal empty arithmetic return.
Copyright (c)2026 Zhongpai Gao. Native coarse estimate by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeLowCoarseInvoke
import Candidate.Research.RecursiveAffine.InnerLowQuantitativeMetadata
import Candidate.Research.RecursiveAffine.NativeInnerSelectedPrimitives
import Candidate.Research.RecursiveAffine.NativeWholeNodeForest

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
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

/-- The large-height branch calls the actual native coarse source on the
SAME selected rows, then absorbs its polynomial scale by the genuine
height cutoff. Its return is the literal empty fully licensed receipt.
No small-height, node-energy, column-energy or returned-count estimate is
assumed. The raw outer scale and the moving native OLD target stay exact. -/
theorem actual_node_low_large_height_empty_return :
    letI : Cycle63.AffineLedger:=N.ledger
    ∀    (g : GeometryAffineLowSchedule)(hmu : g.μ=nativeMu)(hdelta : g.δ=nativeDriverRate (Fintype.card alpha))
    (Cs Kold Kcoarse : ℝ)(hKold : 0≤Kold)(hKcoarse : 0≤Kcoarse)(smallDegree : ℕ)
    (coarse : NativeLowCoarseSubsetAt N.slots (Fintype.card alpha) Cs Kcoarse N.localBase)
    (caps : GeometryAffineLowSourceGates (N.input hH) N.profiles Cs N.localBase)
    (epsNode : ℝ)(primitive : InnerSelectedPrimitivePacket hH C j N Cs caps epsNode (Fintype.card alpha))
    (Sp : Finset (ℕ×ℕ))(hzero : (0,0)∈Sp)
    (reflected second : Bool)(firstHeight outer target : ℝ)(htarget : -1≤target)
    (htargetEq : target=geometryAffineLowTarget g (Fintype.card N.slots) (nodeSourceAmp N)
      (frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8) C.slotMesh+(1-N.state.rowWidth))
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
      ¬2*(1+|firstHeight|+N.height+2*Real.pi*(|t0|+|u|)) ≤ N.localBase^g.τ →
      ∀(Bsrc : ℝ)(boxes : ℕ→Finset (Fin 4→ℤ)),
      ∃receipt : NativeNodeForestReceipt hH N Bsrc boxes,
        receipt.family=emptyReturnedForest ∧
        N.localBase^outer*mainLowPhysicalCompleteCost (Fintype.card N.slots) 1 (1/4) second
          (fun r : rows=>ordinarySecondDatum (datum r) (chi r) (Q r) (m r))
          (fun r=>geometryFirstHighMass reflected (N.input hH) N.state.puncture 1 W N.state.rowWidth N.localBase (nativeMu/64)
            (nativeDriverRate (Fintype.card alpha))
            (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin (firstIndex r.val.1).1.val/
            volume (geometryLowFirstChild reflected (N.input hH) N.state.puncture 1 (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
              (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin firstHeight (firstIndex r.val.1)))
          t0 u select ≤
        ((2+4*Real.pi)^(innerLowDegree (Fintype.card alpha) g.τ g.τ_pos smallDegree)*(Kold+Kcoarse))*
          ((N.profiles.control Sp)^2*geometryHighFactor reflected
            (geometrySupportConstant (Fintype.card N.slots) 1 (1/4) (1/4)) bin*
            (1+|firstHeight|+N.height)^(innerLowDegree (Fintype.card alpha) g.τ g.τ_pos smallDegree)*
            (1+|t0|)^(innerLowDegree (Fintype.card alpha) g.τ g.τ_pos smallDegree)*
            (1+|u|)^(innerLowDegree (Fintype.card alpha) g.τ g.τ_pos smallDegree))*N.localBase^(outer+target) :=by
  dsimp only
  letI : Cycle63.AffineLedger:=N.ledger
  intro g hmu hdelta Cs Kold Kcoarse hKold hKcoarse smallDegree coarse caps epsNode primitive
    Sp hzero reflected second firstHeight outer target htarget htargetEq bin firstIndex hf hinj
    W chi Q m t0 u e select hlarge Bsrc boxes
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
  have hs:=innerLowDegreeRule (Fintype.card alpha) g.τ g.τ_pos smallDegree
  have hb:=hs N.localBase target firstHeight N.height t0 u _ Kold Kcoarse
    ((N.profiles.control Sp)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card N.slots) 1 (1/4) (1/4)) bin) 1 0
    N.localBase_gt_one.le htarget N.height_nonneg hKold hKcoarse hcontrol le_rfl le_rfl
    (fun h=>False.elim (hlarge h)) (by simpa only [mul_assoc] using hcmax)
  refine ⟨native_empty_forest_receipt hH N Bsrc boxes,rfl,?_⟩
  have hraw:=mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (zero_lt_one.trans N.localBase_gt_one).le outer)
  apply hraw.trans_eq
  rw [Real.rpow_add (zero_lt_one.trans N.localBase_gt_one)]
  simp only [mul_zero,zero_mul,add_zero,innerLowDegree]
  ring

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_node_low_large_height_empty_return
