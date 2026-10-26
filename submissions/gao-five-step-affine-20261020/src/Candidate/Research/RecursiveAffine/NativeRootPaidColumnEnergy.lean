/- The actual canonical ROOT column producer, with genuine arithmetic callbacks.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootPaidColumnEnergyInputs
import Candidate.Research.RecursiveAffine.NativeRootCoordinateReceipt
import Candidate.Research.RecursiveAffine.NativeRootColumnPaidResult
import Candidate.Research.RecursiveAffine.NativeChosenContinuationFields
import Candidate.Research.RecursiveAffine.NativeRootCanonicalEnvelope
import Candidate.Research.RecursiveAffine.NativeDirectCertificate

set_option autoImplicit false
set_option maxHeartbeats 900000
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
variable (hH : RayOrthogonality.globalUnits M ≤ H)(C : SourceContext (α:=alpha) M H)
noncomputable local instance rootPaidColumnEnergyLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
open Cycle153RootStep Cycle153JointCount
attribute [local irreducible] NativeColumnOutputTrace nodeOfNativeContinuation
attribute [local irreducible] actualCanonicalRootCoordinateReceipt
attribute [local irreducible] nativeSharedColumnFixed nativeColumnSourceConstant

/-- Apply the literal canonical source operator and construct all three
recursive callbacks from the SAME physical daughter. The primitive input
conditions are the actual native source fit, finite-error, canonical-row
and prefix gates; no column, daughter or node-energy bound is an input.
The only recursive input is availability of genuine strictly deeper
NodeOutputs, chosen before this source configuration. -/
def actualRootPaidColumnEnergy
    (hQ0 : internalQ C.Q C.etaSeed≠0)(hQt : internalQ C.Q C.etaSeed≠⊤)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (g : GeometryAffineLowSchedule)(Cs epsNode epsShell : ℝ)(hepsNode : 0<epsNode)(hShell : 0<epsShell)
    (degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))(Kterminal Cpay Kcol : ℝ)
    (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C0 C1 Kdirect : ℝ)
    (source : RootCanonicalNativeSpec hH C hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect)
    (s : Input alpha)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs C.globalBase)
    (hm : Matches M H hH s C.etaSeed (fun i=>C.theta i)
      (fun i=>C.originalWeight i) (fun i=>C.sigma i) (fun i=>C.frequency i) C.W 2 C.globalBase)
    (hwL : ∀i,C.originalWeight i ≤ Cycle25.Energy.commonMesh 2 28 1 (oldLoss epsNode))
    (hwr : ∀i,C.originalWeight i/31 ≤ 1)
    (hscale : ∀i,s.P i=C.globalBase^(C.originalWeight i))
    (hwindow : Cycle63.AffineLedger.PlainWindow
      (length C.globalBase s.X₁) (length C.globalBase s.X₂) (∑i,C.originalWeight i))
    (mesh : ℝ)(hmesh : 0 ≤ mesh)(hwm : ∀i,C.originalWeight i ≤ mesh)
    (height : ℝ)(hheight : 0 ≤ height)(hfreq : ∀i,|C.frequency i| ≤ height)
    (sourceHeight : ℝ)(buffer : BufferIndex g.e)(hp : 1≤buffer.1.val)
    (hSmallHeight : |sourceHeight|+height+C.globalBase^g.τ/2≤5*C.globalBase^g.τ)
    (hHigh : (3+(3*buffer.1.val+2:ℕ)*C.globalBase^g.τ)^2≤(C.globalBase^(31:ℝ))^(3:ℝ))
    (ch : Chain s)
    (gg : LiveMainGeometry s ch C.globalBase 1 (rootSourceAmp C.originalWeight)
      (frequencyLoss C.globalBase 32 (nativeMu/64)+nativeMu/8) (nativeMu/64) (9/4) (Fintype.card alpha))
    (ray : RayFourExpansion.RayCharacter)(hP : ch.R₂*ch.E₂≠0)
    (hPN : ((ch.R₂*ch.E₂).absNorm:ℝ)≤C.globalBase^(28:ℝ))
    (Ds : Finset (Ideal O))(zs : Finset O)(T : ℝ)
    (hOwn : Supported ch.E₂)(seed : Ideal O)(hseed : seed∣ch.E₂)
    (hfit : 1+Real.logb C.globalBase (s.η.modulus.absNorm:ℝ)≤1+(nativeMu/8)/2)
    (hconstants : Real.logb C.globalBase CenteredMomentFirstPhysicalSource.fixedPresentationCost+
      2*(Fintype.card alpha:ℝ)*Real.logb C.globalBase (9/4)+Real.logb C.globalBase 1+
      Real.logb C.globalBase (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤(nativeMu/8)/2)
    (hpad : supportPadding (Fintype.card alpha) (9/4) s.b₁ s.b₂ C.globalBase≤nativeMu/8)
    (homega : frequencyLoss C.globalBase 32 (nativeMu/64)+nativeMu/8≤(1/1000000000000000:ℝ))
    (hT : 1≤T)(hDs : ∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T)
    (datum : SecondInputDatum alpha)(second : Bool)
    (frame : CanonicalSourceFrame s ch gg datum second)
    (chi0 chi psi : RayFourExpansion.RayCharacter)(m : O)(hm0 : m≠0)
    (hml : goodLambda∣m)(hm2 : (2:O)∣m)
    (hTsource : 2<C.globalBase^g.τ)(hBetaHigh : HeckeZeroSupremum.beta≤7/8)
    (hray : ray=(if second then psi⁻¹ else chi))
    (hR2 : ch.R₂=(1:Ideal O)*ch.C₁)
    (hfinite : Real.logb C.globalBase 128+
      (2*(Fintype.card alpha:ℝ)*Real.logb C.globalBase (9/4)+
        Real.logb C.globalBase (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000)
    (paid : NativePaidPathNode C.globalBase)
    (hPaidUnit : paid.unit=1)(hPaidRow : paid.scale≤1)
    (hPaidLength : paid.length=Real.logb C.globalBase (volume s))
    (hPaidAmp : paid.amplification=rootSourceAmp C.originalWeight)
    (hPaidCommon : paid.commonLog=Real.logb C.globalBase (ch.C₁.absNorm:ℝ)+
      Real.logb C.globalBase (ch.E₂.absNorm:ℝ))
    (paidSource : paid.SourceGates)(paidFine : paid.FineSourceGates)
    (feeBudget : ℕ)
    (feeBound : ∀(R : Finset alpha)
      (hd : (∑i∈R,C.originalWeight i)≤rootDetectorDeletion C.originalWeight+mesh),
      let f:=actualRootNativeFeeAtMesh C s epsNode feeBudget R mesh hmesh hd
      f.amount≤1/1000000000000000 ∧
      (rootDetectorDeletion C.originalWeight≤∑i∈R,C.originalWeight i→
        f.junction*f.modelDeletion+f.amount≤2))
    (hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin) :
    NativeRootPaidColumnEnergyInputs hH C hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
      source s p caps hm hwL hwr hscale hwindow mesh hmesh hwm height hheight hfreq
      sourceHeight buffer hp hSmallHeight hHigh ch gg ray hP hPN Ds zs T hOwn seed hseed
      hfit hconstants hpad homega hT hDs datum second frame chi0 chi psi m hm0 hml hm2
      hTsource hBetaHigh hray hR2 hfinite paid hPaidUnit hPaidRow hPaidLength hPaidAmp hPaidCommon
      paidSource paidFine feeBudget feeBound hgrid :=by
  unfold NativeRootPaidColumnEnergyInputs
  intro omega st u width hpDatum hnDatum ordinaryRows selector hzs P hPnorm hrelative constant eps Bsrc
    control degree boxes hIH hconstant heps hchild
  let hmu : 0<nativeMu:=nativeMu_pos
  let hunits:=width
  let hlog : (∑i : alpha,Real.logb C.globalBase (s.P i))=∑i,C.originalWeight i:=by
    apply Finset.sum_congr rfl
    intro i _
    rw [hscale i]
    exact Real.logb_rpow (zero_lt_one.trans C.globalBase_gt_one) C.globalBase_gt_one.ne'
  let hslots : Cycle63.AffineLedger.slotFloor ≤ ∑i,Real.logb C.globalBase (s.P i) ∧
      (∑i,Real.logb C.globalBase (s.P i)) ≤ Cycle63.AffineLedger.slotTop:=by
    rw [hlog]
    exact ⟨hwindow.slots_ge,hwindow.slots_le⟩
  let haff : length C.globalBase s.X₁+length C.globalBase s.X₂+
      Cycle63.AffineLedger.lam*(∑i,Real.logb C.globalBase (s.P i)) ≤ Cycle63.AffineLedger.B:=by
    rw [hlog]
    exact hwindow.plane
  let hdelta : nativeMu/8+(nativeMu/64)/2 ≤ (1/1000000000000000:ℝ):=by
    norm_num [nativeMu,Cycle153.RegionalSchedule.primitiveError]
  let hamp : rootSourceAmp C.originalWeight=Cycle63.AffineLedger.amp
      (Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell
        (∑i : alpha,Real.logb C.globalBase (s.P i)))):=by
    rw [hlog]
    rfl
  let hdel : rootDetectorDeletion C.originalWeight=
      (Cycle63.AffineLedger.regionGap (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : alpha,Real.logb C.globalBase (s.P i))))+
      6*Cycle63.AffineLedger.intercept*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑i : alpha,Real.logb C.globalBase (s.P i)))))/
      (6*Cycle63.AffineLedger.price)+detectorExtra:=by
    rw [hlog]
    unfold rootDetectorDeletion rootSourceDeletion rootSourceAmp rootSourceCell
    norm_num only [Cycle153AnalyticPrimitive.detectorExtra]
  let henvelope:=actual_root_canonical_fixed_envelope C.originalWeight ⟨hwindow.slots_ge,hwindow.slots_le⟩
  let hrate : Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice) ≤ 1/2:=henvelope.1
  let hcert:=by
    have hh:=henvelope.2
    unfold rootSourceCell at hh
    rw [←hlog] at hh
    exact hh
  let hpadu : supportPadding (Fintype.card alpha) (9/4) s.b₁ s.b₂ C.globalBase≤nativeMu/8:=hpad
  let invoke:=actualRootCanonicalInvocation hH C hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
    degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
    source s p caps hm hwL hwr ⟨hwindow.slots_ge,hwindow.slots_le⟩
    mesh hmesh hwm height hheight hfreq sourceHeight buffer hp hSmallHeight hHigh
  let canonical:=invoke ch 1 (rootSourceAmp C.originalWeight) omega (nativeMu/64) (9/4) (nativeMu/8) (nativeMu/8)
    (1/1000000000000000) (1/1000000000000000) (Fintype.card alpha) gg ray
    (internalQ C.Q C.etaSeed) hP hPN Ds zs T (actualRootSourcePad C s) hOwn seed hseed
    hamp hdel (by norm_num) caps.endpoints.1 hslots haff hfit hconstants
    (by positivity) (by positivity) (by
      exact add_nonneg (frequencyLoss_nonneg C.globalBase 32 (nativeMu/64) C.globalBase_gt_one
        (by norm_num) (by positivity)) (by positivity)) (by positivity) hpadu homega hdelta hrate
    (actual_root_canonical_scalar_gates C.originalWeight ⟨hwindow.slots_ge,hwindow.slots_le⟩).1 (by simpa only [Cycle153Geometry.Coordinates.mu,hlog,rootSourceAmp,rootSourceCell] using hcert)
    caps.endpoints.1 hT hDs hunits.2.2
    (by exact inf_le_left.trans C.Q_le_M) (by exact inf_le_right)
    datum second frame chi0 chi psi m hm0 hml hm2 C.fixed_small hTsource hBetaHigh hray rfl
    buffer rfl
  let completed:=canonical hzs
    (fun B _=>actual_root_common_allowance (C:=C) s p Cs caps ch (gg.datum.τ ray) sourceHeight B)
    u hunits.2.1 hunits.1 (by simp only [u,nativeUnit,mul_one,add_assoc]) (hunits.2.1.trans (by norm_num))
    p caps.profile₁ caps.profile₂
    (fun d=>actual_chain_raw_plain_cap s
      (commonContinuationChain s ch (gg.datum.τ ray) sourceHeight d.1)
      (gg.datum.τ ray) sourceHeight (C.globalBase^(1:ℝ))
      (by simpa only [Real.rpow_one] using C.globalBase_gt_one.le) caps.plainScales
      d.2.2.2 d.2.1.1 d.2.2.1.1 0)
    (fun d=>actual_chain_raw_plain_cap s
      (commonContinuationChain s ch (gg.datum.τ ray) sourceHeight d.1)
      (gg.datum.τ ray) sourceHeight (C.globalBase^(1:ℝ))
      (by simpa only [Real.rpow_one] using C.globalBase_gt_one.le) caps.plainScales
      d.2.2.2 d.2.1.1 d.2.2.1.1 1)
  let package:=actualCanonicalRootCoordinateReceipt C s ch (gg.datum.τ ray) sourceHeight
    (Fintype.card alpha) (9/4) omega (nativeMu/64) (nativeMu/8) mesh gg
    (by norm_num) (le_refl _) caps.endpoints.1 (by rw [caps.lower])
    hscale hwindow (by simp only [omega,mul_one]) hR2 hP hfinite hgrid 28 st Ds
  have hret:=completed P hPnorm rfl constant eps Bsrc control degree boxes hIH hconstant heps hchild
    (fun d hn z hz R hR hsum hcov hc=>(package d hn z hz R hR hsum hcov hc).property.2.1)
    (fun d hn z hz R hR hsum hcov hc=>(package d hn z hz R hR hsum hcov hc).val)
    (fun d hn z hz R hR hsum hcov hc=>(package d hn z hz R hR hsum hcov hc).property.1)
  obtain ⟨Rdel,F,hsource,henergy⟩:=hret
  refine ⟨{deleted:=Rdel,family:=F,choice:=?_,energy_bound:=?_}⟩
  · by_cases hzF : F=emptyReturnedForest
    · exact Or.inl hzF
    · rcases hsource with hempty|⟨d,hn,trace⟩
      · exact False.elim (hzF hempty)
      · obtain ⟨hn,z,hz,hR,hsum,hcover,hc,out,hvalue⟩:=trace.live hzF
        let firstInput:=withHeight ch.first (gg.datum.τ ray) sourceHeight
        let src:=commonData firstInput ch.E₂ ch.R₂ d.1
        let J:=(CenteredMomentDivisorRaw.liveIndices d.2.1.1 d.2.2.1.1).map
          ((originalEmbedding ch.first ch.E₂ d.1).trans (originalEmbedding s ch.C₁ ch.B₁))
        let kept:=package d hn z hz Rdel hR hsum hcover hc
        let chosen:=nodeOfNativeContinuation C (0:Fin 4) C.globalBase 1 u 28
          (lt_of_lt_of_le (by norm_num : (0:ℝ)<397/1000) hc.1)
          (by rw [Real.rpow_one]) st width.1 kept.property.2.1
          ((J\Rdel).map (Function.Embedding.refl alpha)) p
          (rawDaughterScale src d.2.2.2 d.2.1.1 d.2.2.1.1 0)
          (rawDaughterScale src d.2.2.2 d.2.1.1 d.2.2.1.1 1)
          (raw_daughter_scale_pos src d.2.2.2 d.2.1.1 d.2.2.1.1 0)
          (raw_daughter_scale_pos src d.2.2.2 d.2.1.1 d.2.2.1.1 1)
          P hPnorm rfl sourceHeight height hheight (fun i=>hfreq i.val) kept.val kept.property.1
        have fields:=actual_chosen_continuation_fields C (0:Fin 4) C.globalBase 1 u 28
          (lt_of_lt_of_le (by norm_num : (0:ℝ)<397/1000) hc.1)
          (by rw [Real.rpow_one]) st width.1 kept.property.2.1
          ((J\Rdel).map (Function.Embedding.refl alpha)) p
          (rawDaughterScale src d.2.2.2 d.2.1.1 d.2.2.1.1 0)
          (rawDaughterScale src d.2.2.2 d.2.1.1 d.2.2.1.1 1)
          (raw_daughter_scale_pos src d.2.2.2 d.2.1.1 d.2.2.1.1 0)
          (raw_daughter_scale_pos src d.2.2.2 d.2.1.1 d.2.2.1.1 1)
          P hPnorm rfl sourceHeight height hheight (fun i=>hfreq i.val) kept.val kept.property.1
        have hdeleted : (∑i∈Rdel,C.originalWeight i)≤rootDetectorDeletion C.originalWeight+mesh:=by
          simpa only [Function.Embedding.refl_apply,div_one] using hsum
        have hcover0 : Rdel=J ∨ rootDetectorDeletion C.originalWeight≤∑i∈Rdel,C.originalWeight i:=by
          simpa only [Function.Embedding.refl_apply,div_one] using hcover
        have hproper : Rdel≠J:=hc.2.1
        let fee:=actualRootNativeFeeAtMesh C s epsNode feeBudget Rdel mesh hmesh hdeleted
        have hf:=feeBound Rdel hdeleted
        let nextChain:=commonContinuationChain s ch (gg.datum.τ ray) sourceHeight d.1
        let nextGeometry:=commonContinuationGeometry gg (gg.datum.τ ray) sourceHeight d.1 hn
        let scalePad:=Real.logb C.globalBase 4+2*(Fintype.card alpha:ℝ)*Real.logb C.globalBase (9/4)+(nativeMu/64)/2
        have hscaleFine : scalePad≤1/1000000000000:=by
          have hlog : Real.logb C.globalBase 4≤Real.logb C.globalBase 128:=
            (Real.logb_le_logb C.globalBase_gt_one (by norm_num : (0:ℝ)<4) (by norm_num : (0:ℝ)<128)).2 (by norm_num)
          have hends : 0≤Real.logb C.globalBase (max 1 s.b₁*max 1 s.b₂):=by
            apply Real.logb_nonneg C.globalBase_gt_one
            exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
          have hxi : nativeMu/64≤1/1000000000000000:=by norm_num [nativeMu,primitiveError]
          dsimp only [scalePad]
          linarith only [hlog,hends,hfinite,hxi]
        have hrel : chosen.unit*chosen.state.rowWidth+
            Real.logb C.globalBase ((Ideal.span {chosen.presentation.mult}).absNorm:ℝ)≤paid.coordinate 2+scalePad:=by
          rw [fields.2.2.2.1,one_mul,fields.2.2.1]
          exact hrelative
        obtain ⟨edge,hnode,hfee⟩:=actual_root_column_edge_at_chosen (hH:=hH) s nextChain (gg.datum.τ ray)
          sourceHeight (Fintype.card alpha) (9/4) 1 omega (nativeMu/64) (nativeMu/8) mesh nextGeometry
          (by norm_num) (le_refl _) caps.endpoints.1 (by rw [caps.lower]) hscale hwindow
          d.2.2.2 d.2.1.1 d.2.2.1.1 z hz Rdel hR hproper hcover0 hdeleted
          (by simp only [omega,mul_one]) hR2 hP hfinite paid hPaidUnit hPaidRow hPaidLength hPaidAmp hPaidCommon
          paidSource paidFine fee (by linarith only [hf.1]) (hf.2 (hcover0.resolve_left hproper))
          rfl rfl chosen (fields.2.1.trans kept.property.2.2) scalePad hscaleFine hrel
        refine Or.inr ⟨chosen,out,hdeleted,edge,fields.2.2.1,hnode,hfee,?_,?_,hvalue⟩
        · rw [hnode,hfee]
          exact root_native_paid_coefficient_eq C s paid epsNode feeBudget mesh hmesh Rdel hdeleted
        · rw [hnode]
          exact paid.lengthLift_coordinate_one _
  · simp only [Function.Embedding.refl_apply] at henergy
    convert henergy using 1 <;> ring

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualRootPaidColumnEnergy
