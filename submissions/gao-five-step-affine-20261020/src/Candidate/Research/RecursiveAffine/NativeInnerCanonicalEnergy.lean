/- The actual canonical INNER column producer, with genuine arithmetic callbacks.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerCanonicalInvoke
import Candidate.Research.RecursiveAffine.NativeInnerCanonicalEnergyResult
import Candidate.Research.RecursiveAffine.NativeCanonicalInnerPackage
import Candidate.Research.RecursiveAffine.NativeDirectCertificate

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
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
open Cycle153HighProvider Cycle153ReachableGeometry Cycle153AnalyticPrimitive Cycle153.RegionalSchedule
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
variable (hH : RayOrthogonality.globalUnits M ≤ H)(N : ReachableNode C j)(hj : j.val<3)

private theorem input_X1 : (N.input hH).X₁=N.X1:=rfl
private theorem input_X2 : (N.input hH).X₂=N.X2:=rfl
private theorem input_lower : 1≤(N.input hH).lower:=le_rfl
attribute [local irreducible] ReachableNode.input
attribute [local irreducible] NativeColumnOutputTrace nodeOfNativeContinuation
attribute [local irreducible] actualCanonicalInnerDaughterPackage
attribute [local irreducible] nativeSharedColumnFixed nativeColumnSourceConstant

/-- Apply the literal canonical source operator and construct all three
recursive callbacks from the SAME physical daughter. The primitive input
conditions are the actual native source fit, finite-error, canonical-row
and prefix gates; no column, daughter or node-energy bound is an input.
The only recursive input is availability of genuine strictly deeper
NodeOutputs, chosen before this source configuration. -/
def actualInnerCanonicalEnergy
    (hQ0 : internalQ C.Q C.etaSeed≠0)(hQt : internalQ C.Q C.etaSeed≠⊤)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (g : GeometryAffineLowSchedule)(Cs epsNode epsShell : ℝ)(hepsNode : 0<epsNode)(hShell : 0<epsShell)
    (degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))(Kterminal Cpay Kcol : ℝ)
    (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C0 C1 Kdirect : ℝ)
    (source : InnerCanonicalNativeSpec hH N hj hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect)
    (caps : letI : Cycle63.AffineLedger:=N.ledger
      GeometryAffineLowSourceGates (N.input hH) N.profiles Cs N.localBase)
    (hm : Matches M H hH (N.input hH) C.etaSeed (fun i=>C.theta i)
      (fun i=>C.originalWeight i/N.unit) (fun i=>C.sigma i) (fun i=>C.frequency i) C.W 2 N.localBase)
    (hSourceMesh : C.slotMesh≤localSlotMesh epsNode)
    (sourceHeight : ℝ)(buffer : BufferIndex g.e)(hp : 1≤buffer.1.val)
    (hSmallHeight : |sourceHeight|+N.height+N.localBase^g.τ/2≤5*N.localBase^g.τ)
    (hHigh : (3+(3*buffer.1.val+2:ℕ)*N.localBase^g.τ)^2≤(N.localBase^(31:ℝ))^(3:ℝ))
    (ch : Chain (N.input hH))(Mrow : ℝ)
    (gg : LiveMainGeometry (N.input hH) ch N.localBase Mrow (nodeSourceAmp N)
      (frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8) (nativeMu/64) (9/4) (Fintype.card N.slots))
    (ray : RayFourExpansion.RayCharacter)(hP : ch.R₂*ch.E₂≠0)
    (hPN : ((ch.R₂*ch.E₂).absNorm:ℝ)≤N.localBase^(28:ℝ))
    (Ds : Finset (Ideal O))(zs : Finset O)(T : ℝ)
    (hOwn : Supported ch.E₂)(seed : Ideal O)(hseed : seed∣ch.E₂)
    (hfit : Mrow+Real.logb N.localBase ((N.input hH).η.modulus.absNorm:ℝ)≤1+(nativeMu/8)/2)
    (hconstants : Real.logb N.localBase CenteredMomentFirstPhysicalSource.fixedPresentationCost+
      2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+Real.logb N.localBase 1+
      Real.logb N.localBase (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤(nativeMu/8)/2)
    (hslots : letI : Cycle63.AffineLedger:=N.ledger
      Cycle63.AffineLedger.slotFloor≤∑i,Real.logb N.localBase ((N.input hH).P i) ∧
      (∑i,Real.logb N.localBase ((N.input hH).P i))≤Cycle63.AffineLedger.slotTop)
    (haff : letI : Cycle63.AffineLedger:=N.ledger
      length N.localBase (N.input hH).X₁+length N.localBase (N.input hH).X₂+
      Cycle63.AffineLedger.lam*(∑i,Real.logb N.localBase ((N.input hH).P i))≤Cycle63.AffineLedger.B)
    (hpad : supportPadding (Fintype.card N.slots) (9/4) (N.input hH).b₁ (N.input hH).b₂ N.localBase≤nativeMu/8)
    (homega : frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8≤(1/1000000000000000:ℝ))
    (hdelta : nativeMu/8+(nativeMu/64)/2≤(1/1000000000000000:ℝ))
    (hT : 1≤T)(hDs : ∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T)
    (datum : SecondInputDatum N.slots)(second : Bool)
    (frame : CanonicalSourceFrame (N.input hH) ch gg datum second)
    (chi0 chi psi : RayFourExpansion.RayCharacter)(m : O)(hm0 : m≠0)
    (hml : goodLambda∣m)(hm2 : (2:O)∣m)
    (hTsource : 2<N.localBase^g.τ)(hBetaHigh : HeckeZeroSupremum.beta≤7/8)
    (hray : ray=(if second then psi⁻¹ else chi))
    (hR2 : ch.R₂=N.state.puncture*ch.C₁)
    (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
      (2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+
        Real.logb N.localBase (max 1 (N.input hH).b₁*max 1 (N.input hH).b₂)) ≤ 1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin) :
    InnerCanonicalEnergyAt hH N hj hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
      source caps hm hSourceMesh sourceHeight buffer hp hSmallHeight hHigh ch Mrow gg ray hP hPN Ds zs T
      hOwn seed hseed hfit hconstants hslots haff hpad homega hdelta hT hDs datum second frame
      chi0 chi psi m hm0 hml hm2 hTsource hBetaHigh hray hR2 hfinite hgrid :=by
  unfold InnerCanonicalEnergyAt
  intro s omega st u hunits hpDatum hnDatum ordinaryRows selector
    hzs P hPnorm constant eps Bsrc control degree boxes hIH hconstant heps hchild
    firstInput Daughter src J continues package childAt Trace SourceK Control slotLoss OldPaid
  letI : Cycle63.AffineLedger:=N.ledger
  let hmu : 0<nativeMu:=nativeMu_pos
  let hlog : (∑i : N.slots,Real.logb N.localBase (s.P i))=
      ∑i : N.slots,C.originalWeight i/N.unit :=by
    apply Finset.sum_congr rfl
    intro i _
    rw [hm.scale i]
    exact Real.logb_rpow (zero_lt_one.trans N.localBase_gt_one) N.localBase_gt_one.ne'
  let hamp : nodeSourceAmp N=Cycle63.AffineLedger.amp
      (Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell
        (∑i : N.slots,Real.logb N.localBase (s.P i)))) :=by
    rw [hlog,nodeSourceAmp_eq_native N]
  let hdel : nodeDetectorDeletion N=
      (Cycle63.AffineLedger.regionGap (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : N.slots,Real.logb N.localBase (s.P i))))+
      6*Cycle63.AffineLedger.intercept*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : N.slots,Real.logb N.localBase (s.P i)))))/
      (6*Cycle63.AffineLedger.price)+detectorExtra :=by
    rw [hlog]
    unfold nodeDetectorDeletion
    rw [regional_actual_cell N.positionFacts ⟨N.window.slots_ge,N.window.slots_le⟩]
    congr 1 <;> norm_num [detectorExtra]
  let hrate : Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)≤1/2 :=by
    change directNodeRate j≤1/2
    fin_cases j <;> norm_num [directNodeRate,innerStage,Cycle153.FixedStages.stage1,
      Cycle153.FixedStages.stage2,Cycle153.FixedStages.stage3,Cycle153.FixedStages.stage4,
      Cycle63.Optimization.slotPrice,Cycle63.Optimization.betaBound,
      Cycle153Geometry.Coordinates.q1,Cycle153Geometry.Coordinates.q2,
      Cycle153Geometry.Coordinates.q3,Cycle153Geometry.Coordinates.q4]
  let hq : Cycle63.AffineLedger.q=(innerStage j.val).q:=rfl
  let hcert:=by
    have hh:=actual_inner_direct_certificate N hj hgrid
      (1/1000000000000000) (nativeMu/8) (1/1000000000000000) (by
        norm_num [nativeMu,primitiveError])
    dsimp only at hh
    rw [←hlog,←hamp] at hh
    exact hh
  let hpadu : supportPadding (Fintype.card N.slots) (9/4) s.b₁ s.b₂ N.localBase≤nativeMu/8:=hpad
  let invoke:=actualInnerCanonicalInvocation hH N hj hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
    degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
    source caps hm hSourceMesh sourceHeight buffer hp hSmallHeight hHigh
  let canonical:=invoke ch Mrow (nodeSourceAmp N) omega (nativeMu/64) (9/4) (nativeMu/8) (nativeMu/8)
    (1/1000000000000000) (1/1000000000000000) (Fintype.card N.slots) gg ray
    (internalQ C.Q C.etaSeed) hP hPN Ds zs T (actualNodeLocalSourcePad (hH:=hH) N) hOwn seed hseed
    hamp hdel (by norm_num) caps.endpoints.1 hslots haff hfit hconstants
    (by positivity) (by positivity) (by
      exact add_nonneg (frequencyLoss_nonneg N.localBase 32 (nativeMu/64) N.localBase_gt_one
        (by norm_num) (by positivity)) (by positivity)) (by positivity) hpadu homega hdelta hrate
    (actual_node_canonical_scalar_gates N).1 (by
      simpa only [directNodeRate,hq,s,Cycle153Geometry.Coordinates.mu] using hcert)
    caps.endpoints.1 hT hDs hunits.2.2
    (by exact inf_le_left.trans C.Q_le_M) (by exact inf_le_right)
    datum second frame chi0 chi psi m hm0 hml hm2 C.fixed_small hTsource hBetaHigh hray rfl
    buffer rfl
  let completed:=canonical hzs
    (fun B _=>actual_inner_common_allowance (hH:=hH) N Cs caps ch (gg.datum.τ ray) sourceHeight B)
    u hunits.2.1 hunits.1 (by simp only [u,nativeUnit,mul_one,add_assoc]) (hunits.2.1.trans (by norm_num))
    N.profiles caps.profile₁ caps.profile₂
    (fun d=>actual_chain_raw_plain_cap s
      (commonContinuationChain s ch (gg.datum.τ ray) sourceHeight d.1)
      (gg.datum.τ ray) sourceHeight (N.localBase^(1:ℝ))
      (by simpa only [Real.rpow_one] using N.localBase_gt_one.le) caps.plainScales
      d.2.2.2 d.2.1.1 d.2.2.1.1 0)
    (fun d=>actual_chain_raw_plain_cap s
      (commonContinuationChain s ch (gg.datum.τ ray) sourceHeight d.1)
      (gg.datum.τ ray) sourceHeight (N.localBase^(1:ℝ))
      (by simpa only [Real.rpow_one] using N.localBase_gt_one.le) caps.plainScales
      d.2.2.2 d.2.1.1 d.2.2.1.1 1)
  have hret:=completed P hPnorm rfl constant eps Bsrc control degree boxes hIH hconstant heps hchild
    (fun d hn z hz R hR hsum hcov hc=>(package d hn z hz R hR hsum hcov hc).property.2)
    (fun d hn z hz R hR hsum hcov hc=>(package d hn z hz R hR hsum hcov hc).val)
    (fun d hn z hz R hR hsum hcov hc=>(package d hn z hz R hR hsum hcov hc).property.1)
  exact hret

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualInnerCanonicalEnergy
