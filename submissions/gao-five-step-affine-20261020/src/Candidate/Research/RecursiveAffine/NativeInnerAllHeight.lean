/- Actual all-bin INNER RAW LOW source from genuine native source operators.
Copyright (c)2026 Zhongpai Gao. Native analytic operators by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerHeightSplice
import Candidate.Research.RecursiveAffine.NativeInnerPerBinAllHeight
import Candidate.Research.RecursiveAffine.NativeNodeRawLow

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RegionalLow
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily CanonicalQuadraticSieve
open CenteredMomentNaturalFixedRaySource CenteredMomentAllocatedRayDictionary
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentSectorLocalization CenteredMomentSourceLiveColumn
open CenteredMomentEnergyBands CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open Cycle63Moment Cycle63InitialMass Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity
open LocalMoment ConcretePrimeRowBridge CenteredMomentSecondHeightFamily Cycle153CanonicalLow
open Cycle153Reachable Cycle153RegionalLow Cycle153ContinuationUnit Cycle153SourceSchedule Cycle153SourceUniform
open Cycle153HighProvider Cycle153ReachableGeometry Cycle153.RegionalSchedule
open Cycle153LowPhysical Cycle153InnerLowSchedule
open Cycle153ActualColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstCanonicalFamily CenteredMomentSecondCanonicalScalar
open Cycle153ActualSourceGates CenteredMomentEnergyState CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondInputCapacitySource
open Cycle153SourceReturn Cycle153JointCount CenteredMomentWholeDivisorShell CenteredMomentLogDyadic
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
variable {hH : RayOrthogonality.globalUnits M≤H}
variable (N : ReachableNode C j)
attribute [local irreducible] ReachableNode.input

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

theorem actual_native_node_raw_low_at
    (hH : RayOrthogonality.globalUnits M≤H)(N : ReachableNode C j)
    (hj : j.val<3)(hQ0 : internalQ C.Q C.etaSeed≠0)(hQt : internalQ C.Q C.etaSeed≠⊤)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hBetaHigh : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule)(Cs epsNode : ℝ)(hepsNode : 0<epsNode)
    (hmu : g.μ=nativeMu)(hRate : g.δ=nativeDriverRate (Fintype.card alpha))
    (degreeTerminal degreeDirect : ℕ)(controlTerminal controlDirect : Finset (ℕ×ℕ))
    (Kterminal Cpay Kcol Cdirect C0 C1 Kdirect Kcoarse : ℝ)
    (Kchild : ℝ)(hKchild : 0≤Kchild)(controlChild : Finset (ℕ×ℕ))(degreeChild : ℕ)
    (source : Cycle153ActualColumn.InnerCanonicalNativeSpec hH N hj hQ0 hQt hbeta g Cs epsNode
      (postDictionaryRate C.Bnorm (Fintype.card alpha)) hepsNode
      (postDictionaryRate_budgets C.normCap_nonneg (Fintype.card alpha)).1
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect)
    (coarse : NativeLowCoarseSubsetAt N.slots (Fintype.card alpha) Cs Kcoarse N.localBase)
    (primitiveSource : ∀caps : letI : Cycle63.AffineLedger:=N.ledger;
      GeometryAffineLowSourceGates (N.input hH) N.profiles Cs N.localBase,
      letI : Cycle63.AffineLedger:=N.ledger;
      Nonempty (InnerSelectedPrimitivePacket hH C j N Cs caps epsNode (Fintype.card alpha)))
    (hphysical : innerPhysicalThreshold hH j (postDictionaryRate C.Bnorm (Fintype.card alpha))
      (postDictionaryRate_budgets C.normCap_nonneg (Fintype.card alpha)).1 N.slots≤N.localBase)
    (hscalar : actualSelectedScalarThreshold (Fintype.card alpha)
      (postDictionaryRate C.Bnorm (Fintype.card alpha))
      (postDictionaryRate_budgets C.normCap_nonneg (Fintype.card alpha)).1≤N.localBase)
    (hOld : actualSelectedOldThreshold C.Bnorm C.normCap_nonneg (Fintype.card alpha)
      (Fintype.card N.slots)≤N.localBase)
    (hHigh : ∀buffer : BufferIndex g.e,
      (3+(3*buffer.1.val+2:ℕ)*N.localBase^g.τ)^2≤(N.localBase^(31:ℝ))^(3:ℝ))
    (hCs : 1≤Cs)(hCpay : 1≤Cpay)(hCdirect : 1≤Cdirect)(hKt : 0≤Kterminal)
    (hKcol : 0≤Kcol)(hC0 : 0≤C0)(hC1 : 0≤C1)(hKdirect : 0≤Kdirect)(hKcoarse : 0≤Kcoarse)
    (Sp : Finset alpha→Finset (ℕ×ℕ))(degreeLow : Finset alpha→ℕ)(Klow : Finset alpha→ℝ)(Kreturn : ℝ)
    (hIH : ∀Nc : ReachableNode C (nextInner j hj),
      Nonempty (NodeOutput hH Nc Kchild (oldLoss epsNode) 250000 controlChild degreeChild
        (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha)))) :
    letI : Cycle63.AffineLedger:=N.ledger
    let Dsmall:=max (max degreeTerminal degreeChild) degreeDirect
    let D:=innerLowDegree (Fintype.card alpha) g.τ g.τ_pos Dsmall
    let Cg:=Cycle153ActualColumn.nativeColumnSourceConstant (Fintype.card N.slots) Cs Cpay Kterminal
      Kchild Kcol Cdirect C0 C1 Kdirect
    let Cu:=innerPhysicalConstant hH j (postDictionaryRate C.Bnorm (Fintype.card alpha))
      (postDictionaryRate_budgets C.normCap_nonneg (Fintype.card alpha)).1 N.slots
    let KrawOld:=innerRawOldConstant (Fintype.card N.slots) g.e Cu Cg
      (actualSelectedOldConstant C.Bnorm C.normCap_nonneg (Fintype.card alpha))
      (actualSelectedOldBoxConstant C.Bnorm C.normCap_nonneg (Fintype.card alpha) (Fintype.card N.slots))
    let KrawReturn:=innerRawReturnConstant (Fintype.card N.slots) g.e Cu Cg
    ∀(hSp : Sp N.slots=((controlTerminal∪controlChild)∪controlDirect)∪{(0,0)})
      (hdegree : degreeLow N.slots=D)
      (hKlow : Klow N.slots=(2+4*Real.pi)^D*(KrawOld+Kcoarse))
      (hKreturn : (2+4*Real.pi)^D*KrawReturn≤Kreturn)
      (hT : 2<N.localBase^g.τ),
      NativeNodeRawLowAt hH N hbeta g Cs Sp degreeLow Klow hT hBetaHigh
        (N.state.rowWidth+3*g.δ-nodeSourceAmp N+oldLoss epsNode) Kreturn 250000
        (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha))
 :=by
  dsimp only
  letI : Cycle63.AffineLedger:=N.ledger
  intro hSp hdegree hKlow hKreturn hT
  unfold NativeNodeRawLowAt
  intro caps hm hrow hfit hwL hwr hslots haff
  obtain ⟨primitive⟩:=primitiveSource caps
  unfold RegionalRawLowSelectedAt
  generalize hmuValue : g.μ=muValue
  have hmuValue' : muValue=nativeMu:=hmuValue.symm.trans hmu
  cases hmuValue'
  intro Label inst reflected second bin firstHeight firstIndex first amp omega
  have hampEq : amp=nodeSourceAmp N:=actual_input_amp_eq (hH:=hH) N
  clear_value amp
  subst amp
  intro hamp0 hamp homega htarget hf1 hinj hfirstproj
  intro rows datum chi0 m hm0 hml hm2 Psi t0 u
  let masks:=primitive.masks reflected second firstHeight bin firstIndex hf1
  refine ⟨(fun r=>(masks r).1),(fun r=>(masks r).2.1),?_,?_⟩
  · intro r
    simpa only [show (20:ℝ)+8=28 by norm_num] using (masks r).2.1
  · intro st left1 u0 units Tz hleft hu hunits mult hpresented canonical firstMass childSrc
    have hcard : Fintype.card N.slots≤Fintype.card alpha:=by
      simpa only [Fintype.card_coe,Finset.card_univ] using Finset.card_le_card (Finset.subset_univ N.slots)
    have hzero : (0,0)∈Sp N.slots:=by
      rw [hSp]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hSpSub : (controlTerminal∪controlChild)∪controlDirect⊆Sp N.slots:=by
      rw [hSp]
      exact Finset.subset_union_left
    have hTarget : -1≤geometryAffineLowTarget g (Fintype.card N.slots) (nodeSourceAmp N)
        (frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8) C.slotMesh+(1-N.state.rowWidth):=by
      linarith only [htarget,hrow]
    obtain ⟨receipt,hbound⟩:=actualInnerPerBinAllHeight hH N hj hQ0 hQt hbeta hBetaHigh
      g Cs epsNode hepsNode hcard hRate hmu degreeTerminal controlTerminal Kterminal Cpay Kcol
      degreeDirect controlDirect Cdirect C0 C1 Kdirect source caps primitive hm hphysical hscalar hOld
      hHigh hT reflected second firstHeight bin firstIndex hf1 hinj chi0 m hm0 hml hm2 Psi t0 u
      (fun _=>Kchild) (fun _=>oldLoss epsNode) (fun _=>250000) (fun _=>controlChild) (fun _=>degreeChild)
      hIH hKchild (oldLoss_pos hepsNode).le le_rfl rfl Kcoarse hKcoarse coarse (Sp N.slots) hzero
      hSpSub hTarget hCs hCpay hCdirect hKt hKcol hC0 hC1 hKdirect
    let target:=geometryAffineLowTarget g (Fintype.card N.slots) (nodeSourceAmp N)
      (frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8) C.slotMesh+(1-N.state.rowWidth)
    let outer:=N.state.rowWidth+3*g.δ-nodeSourceAmp N+oldLoss epsNode
    refine ⟨receipt,outer+target,?_,?_⟩
    · dsimp only [outer,target,omega]
      ring_nf
      exact le_rfl
    · have hsupport : geometrySupportConstant (Fintype.card alpha) 1 (1/4) (1/4)=
          geometrySupportConstant (Fintype.card N.slots) 1 (1/4) (1/4):=by
        norm_num [geometrySupportConstant]
      rw [hdegree,hKlow]
      have hv:=receipt.family.value_nonneg (zero_lt_one.trans N.localBase_gt_one).le
      have hfactor : 0≤(N.profiles.control (Sp N.slots))^2*geometryHighFactor reflected
          (geometrySupportConstant (Fintype.card N.slots) 1 (1/4) (1/4)) bin*
          (1+|firstHeight|+N.height)^(innerLowDegree (Fintype.card alpha) g.τ g.τ_pos (max (max degreeTerminal degreeChild) degreeDirect))*
          (1+|t0|)^(innerLowDegree (Fintype.card alpha) g.τ g.τ_pos (max (max degreeTerminal degreeChild) degreeDirect))*
          (1+|u|)^(innerLowDegree (Fintype.card alpha) g.τ g.τ_pos (max (max degreeTerminal degreeChild) degreeDirect)):=by
        have hp : 0≤geometryHighFactor reflected
            (geometrySupportConstant (Fintype.card N.slots) 1 (1/4) (1/4)) bin:=
          (geometry_high_factor_pos reflected _ bin
            (geometrySupportConstant_pos (Fintype.card N.slots) 1 (1/4) (1/4)
              (by norm_num) (by norm_num) (by norm_num))).le
        have hh:=N.height_nonneg
        positivity
      have hret:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKreturn hfactor) hv
      rw [hsupport] at hbound
      apply hbound.trans
      exact add_le_add le_rfl hret

end
end OAI.SevenEighths.Cycle153RegionalLow
#print axioms OAI.SevenEighths.Cycle153RegionalLow.actual_native_node_raw_low_at
