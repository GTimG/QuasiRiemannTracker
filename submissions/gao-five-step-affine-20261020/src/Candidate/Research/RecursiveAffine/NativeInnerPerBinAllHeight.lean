/- Actual INNER all-height source on one native bin, using the genuine small and coarse producers.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerSmallRaw
import Candidate.Research.RecursiveAffine.NativeInnerHeightSplice
import Candidate.Research.RecursiveAffine.NativeSmallPhysicalPayment
import Candidate.Research.RecursiveAffine.NativeSelectedOldActual
import Candidate.Research.RecursiveAffine.NativeSelectedOldLedgerPrice
import Candidate.Research.RecursiveAffine.NativeNodeSourceGates
import Candidate.Research.RecursiveAffine.InnerLowPhysicalMetadata
import Candidate.Research.RecursiveAffine.NativeInnerSelectedPrimitives
import Candidate.Research.RecursiveAffine.NativePhysicalHeightAliases
import Candidate.Research.RecursiveAffine.NativePhysicalPoolAliases
import Candidate.Research.RecursiveAffine.NativeSourceSide

set_option autoImplicit false
set_option maxHeartbeats 500000
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
open Cycle153HighProvider Cycle153ReachableGeometry Cycle153.RegionalSchedule
open Cycle153LowPhysical Cycle153InnerLowSchedule
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstCanonicalFamily CenteredMomentSecondCanonicalScalar
open Cycle153ActualSourceGates CenteredMomentEnergyState CenteredMomentFirstAmplificationChoice
open CenteredMomentSecondInputCapacitySource
open Cycle153SourceReturn Cycle153JointCount CenteredMomentWholeDivisorShell CenteredMomentLogDyadic
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
attribute [local irreducible] mainLowPhysicalCompleteCost nativeOldSelectedCost innerPhysicalConstant innerPhysicalThreshold
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

/-- Invoke the genuine residual/ray/buffer operator on actual selected
rows. Every local source is produced by the native completed-column
factory, with one SAME real returned forest. No energy or receipt bound
is an input. Primitive packets and fixed thresholds are independently
generated before the moving context by the native schedules. -/
def actualInnerPerBinAllHeight
    (hH : RayOrthogonality.globalUnits M≤H)(N : ReachableNode C j)(hj : j.val<3)
    (hQ0 : internalQ C.Q C.etaSeed≠0)(hQt : internalQ C.Q C.etaSeed≠⊤)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hBetaHigh : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule)(Cs epsNode : ℝ)(hepsNode : 0<epsNode)
    (hcard : Fintype.card N.slots≤Fintype.card alpha)
    (hRate : g.δ=nativeDriverRate (Fintype.card alpha))(hmu : g.μ=nativeMu)
    (degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))(Kterminal Cpay Kcol : ℝ)
    (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C0 C1 Kdirect : ℝ)
    (source : InnerCanonicalNativeSpec hH N hj hQ0 hQt hbeta g Cs epsNode
      (postDictionaryRate C.Bnorm (Fintype.card alpha)) hepsNode (postDictionaryRate_budgets C.normCap_nonneg (Fintype.card alpha)).1
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect)
    (caps : letI : Cycle63.AffineLedger:=N.ledger
      GeometryAffineLowSourceGates (N.input hH) N.profiles Cs N.localBase)
    (primitive : letI : Cycle63.AffineLedger:=N.ledger
      InnerSelectedPrimitivePacket hH C j N Cs caps epsNode (Fintype.card alpha))
    (hm : Matches M H hH (N.input hH) C.etaSeed (fun i=>C.theta i)
      (fun i=>C.originalWeight i/N.unit) (fun i=>C.sigma i) (fun i=>C.frequency i) C.W 2 N.localBase)
    (hphysical : innerPhysicalThreshold hH j (postDictionaryRate C.Bnorm (Fintype.card alpha))
      (postDictionaryRate_budgets C.normCap_nonneg (Fintype.card alpha)).1 N.slots≤N.localBase)
    (hlarge : actualSelectedScalarThreshold (Fintype.card alpha) (postDictionaryRate C.Bnorm (Fintype.card alpha))
      (postDictionaryRate_budgets C.normCap_nonneg (Fintype.card alpha)).1≤N.localBase)
    (hOld : actualSelectedOldThreshold C.Bnorm C.normCap_nonneg (Fintype.card alpha) (Fintype.card N.slots)≤N.localBase)
    (hHigh : ∀buffer : BufferIndex g.e,
      (3+(3*buffer.1.val+2:ℕ)*N.localBase^g.τ)^2≤(N.localBase^(31:ℝ))^(3:ℝ))
    (hTsource : 2<N.localBase^g.τ)
    (reflected second : Bool)(firstHeight : ℝ)(key : ℤ×(Fin 5→ℤ))
    {Label : Type}[Fintype Label]
    (firstIndex : Label→GeometryLowFirstIndex reflected (N.input hH) N.state.puncture 1
      (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key)
    (hf1 : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected (N.input hH) N.state.puncture 1 (N.localBase^N.state.rowWidth)
        N.localBase (nativeMu/64) (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key
        (firstIndex l).1.val) N.state.puncture (N.input hH).ν (N.input hH).W (N.input hH).P≠0)
    (hinj : Function.Injective (fun l=>(geometryFirstLabel (N.input hH) N.state.puncture 1
      (N.localBase^N.state.rowWidth) N.localBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val,
      (firstIndex l).1.val.2.1.val)))
    (chi0 : letI : Cycle63.AffineLedger:=N.ledger
      NativeLowRows reflected (N.input hH) N.state.puncture 1 N.localBase N.state.rowWidth (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key caps.zero₁ caps.zero₂ firstIndex→RayFourExpansion.RayCharacter)
    (m : O)(hm0 : m≠0)(hml : goodLambda∣m)(hm2 : (2:O)∣m)(Psi : 𝓢(ℝ,ℂ))(t0 u : ℝ)
    (constant eps Bsrc : Fin 4→ℝ)(control : Fin 4→Finset (ℕ×ℕ))(degree : Fin 4→ℕ)
    (hIH : ∀Nc : ReachableNode C (nextInner j hj),Nonempty (NodeOutput hH Nc
      (constant (nextInner j hj)) (eps (nextInner j hj)) (Bsrc (nextInner j hj))
      (control (nextInner j hj)) (degree (nextInner j hj))
      (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha))))
    (hconstant : 0≤constant (nextInner j hj))(heps : 0≤eps (nextInner j hj))
    (hchild : eps (nextInner j hj)≤oldLoss epsNode)(hBsrc : Bsrc (nextInner j hj)=250000)
    (Kcoarse : ℝ)(hKcoarse : 0≤Kcoarse)
    (coarse : NativeLowCoarseSubsetAt N.slots (Fintype.card alpha) Cs Kcoarse N.localBase)
    (Sp : Finset (ℕ×ℕ))(hzero : (0,0)∈Sp)
    (hSp : (controlTerminal∪control (nextInner j hj))∪controlDirect⊆Sp)
    (hTarget : letI : Cycle63.AffineLedger:=N.ledger;
      -1≤geometryAffineLowTarget g (Fintype.card N.slots) (nodeSourceAmp N)
        (frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8) C.slotMesh+(1-N.state.rowWidth))
    (hCs : 1≤Cs)(hCpay : 1≤Cpay)(hCdirect : 1≤Cdirect)(hKt : 0≤Kterminal)
    (hKcol : 0≤Kcol)(hC0 : 0≤C0)(hC1 : 0≤C1)(hKdirect : 0≤Kdirect) :=
  letI : Cycle63.AffineLedger:=N.ledger
  let Z:=N.localBase
  let s:=N.input hH
  let r:=postDictionaryRate C.Bnorm (Fintype.card alpha)
  let hr:=(postDictionaryRate_budgets C.normCap_nonneg (Fintype.card alpha)).1
  let box:=rootNativeDyadBox C.globalBase (Fintype.card alpha)
  let rows:=NativeLowRows reflected s N.state.puncture 1 Z N.state.rowWidth (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key caps.zero₁ caps.zero₂ firstIndex
  let datum:=fun q : rows=>geometryLowSecondDatum reflected s N.state.puncture 1 Z N.state.rowWidth
    (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key (firstIndex q.val.1) caps.zero₁ caps.zero₂ q.val.2
  let masks:=primitive.masks reflected second firstHeight key firstIndex hf1
  let ordinary:=fun q : rows=>ordinarySecondDatum (datum q) (chi0 q) (internalQ C.Q C.etaSeed) m
  let select:=fun (q : rows)(chi psi : RayFourExpansion.RayCharacter)=>
    mainLowCanonicalSelector M H hH (datum q) (chi0 q) chi psi (internalQ C.Q C.etaSeed) C.fixed_small m hm0 hml hm2
      Z 28 N.localBase_gt_one second (masks q).1 (masks q).2.1 C.etaSeed
      (inf_le_left.trans C.Q_le_M) inf_le_right g.e (Z^g.τ) g.e_pos hTsource hbeta hBetaHigh
  let mass:=fun l=>geometryFirstHighMass reflected s N.state.puncture 1 Psi N.state.rowWidth Z (nativeMu/64) g.δ
    (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val
  let child:=fun l=>geometryLowFirstChild reflected s N.state.puncture 1 (Z^N.state.rowWidth) Z (nativeMu/64)
    (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key firstHeight (firstIndex l)
  let coefficient:=fun q : rows=>mass q.val.1/volume (child q.val.1)
  let Cg:=nativeColumnSourceConstant (Fintype.card N.slots) Cs Cpay Kterminal (constant (nextInner j hj))
    Kcol Cdirect C0 C1 Kdirect
  let sourceHeight:=nativePhysicalSourceHeight second firstHeight t0 u
  let fixed:=(N.profiles.control ((controlTerminal∪control (nextInner j hj))∪controlDirect))^2*
    (1+|sourceHeight|+N.height)^(max (max degreeTerminal (degree (nextInner j hj))) degreeDirect)
  let physical:=geometryHighFactor reflected (geometrySupportConstant (Fintype.card alpha) 1 (1/4) (1/4)) key
  let common:=nativeMu/8+(nativeMu/64)/2-Cycle63.AffineLedger.lowReserve+nativeMu/64+
    2*g.δ*31*(Fintype.card N.slots:ℝ)+Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)*
      (frequencyLoss Z 32 (nativeMu/64)+nativeMu/8+nativeMu/8)+Cycle63.AffineLedger.q*C.slotMesh
  let oldBase:=nativeOldSelectedCost reflected second s N.state.puncture Z N.state.rowWidth
    (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots) N.localBase_gt_one
    key caps.zero₁ caps.zero₂ firstIndex Psi g.δ r (common+actualNodeLocalSourcePad (hH:=hH) N) Cg fixed
  let outer:=N.state.rowWidth+3*g.δ-nodeSourceAmp N+oldLoss epsNode
  let sourceConstant:=Z^(-outer)*(Cg*fixed*physical)
  let Cu:=innerPhysicalConstant hH j r hr N.slots
  let pref:=innerPhysicalPrefactor (Fintype.card N.slots) g.e
  let Kold:=actualSelectedOldConstant C.Bnorm C.normCap_nonneg (Fintype.card alpha)
  let Kbox:=actualSelectedOldBoxConstant C.Bnorm C.normCap_nonneg (Fintype.card alpha) (Fintype.card N.slots)
  let target:=geometryAffineLowTarget g (Fintype.card N.slots) (nodeSourceAmp N)
    (frequencyLoss Z 32 (nativeMu/64)+nativeMu/8) C.slotMesh+(1-N.state.rowWidth)
  let Dsmall:=max (max degreeTerminal (degree (nextInner j hj))) degreeDirect
  let Hcombined:=2*(1+|firstHeight|+N.height+2*Real.pi*(|t0|+|u|))
  let baseControl:=(N.profiles.control ((controlTerminal∪control (nextInner j hj))∪controlDirect))^2*physical
  let Ksmall:=innerRawOldConstant (Fintype.card N.slots) g.e Cu Cg Kold Kbox
  let Kret:=innerRawReturnConstant (Fintype.card N.slots) g.e Cu Cg
  let Dall:=innerLowDegree (Fintype.card alpha) g.τ g.τ_pos Dsmall
  let controlAll:=(N.profiles.control Sp)^2*physical*
    (1+|firstHeight|+N.height)^Dall*(1+|t0|)^Dall*(1+|u|)^Dall
  show ∃receipt : NativeNodeForestReceipt hH N (Bsrc (nextInner j hj)) (fun _=>box),
    Z^outer*mainLowPhysicalCompleteCost (Fintype.card N.slots) 1 (1/4) second ordinary coefficient t0 u select≤
      ((2+4*Real.pi)^Dall*(Ksmall+Kcoarse))*controlAll*Z^(outer+target)+
      ((2+4*Real.pi)^Dall*Kret)*controlAll*receipt.family.value from by
    have hZ0:=zero_lt_one.trans N.localBase_gt_one
    have hheight:=N.height_nonneg
    have hCg : 0≤Cg:=by
      have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
      have hCs0:=zero_le_one.trans hCs
      have hCp0:=zero_le_one.trans hCpay
      have hCd0:=zero_le_one.trans hCdirect
      dsimp only [Cg,nativeColumnSourceConstant]
      positivity
    have hp0 : 0≤physical:=(geometry_high_factor_pos reflected _ key
      (geometrySupportConstant_pos (Fintype.card alpha) 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
    have hCu : 0≤Cu:=(innerPhysicalConstant_pos hH j r hr N.slots).le
    have hKo : 0≤Kold:=(actualSelectedOldConstant_pos C.Bnorm C.normCap_nonneg (Fintype.card alpha)).le
    have hKb : 0≤Kbox:=(actualSelectedOldBoxConstant_pos C.Bnorm C.normCap_nonneg (Fintype.card alpha) (Fintype.card N.slots)).le
    have hsmallK : 0≤Ksmall:=innerRawOldConstant_nonnegative _ _ _ _ _ _ hCu hCg hKo hKb
    have hretK : 0≤Kret:=innerRawReturnConstant_nonnegative _ _ _ _ hCu hCg
    have hphysCard : geometrySupportConstant (Fintype.card N.slots) 1 (1/4) (1/4)=
        geometrySupportConstant (Fintype.card alpha) 1 (1/4) (1/4):=by norm_num [geometrySupportConstant]
    let ctrl:=(N.profiles.control Sp)^2*physical
    have hctrl : 0≤ctrl:=mul_nonneg (sq_nonneg _) hp0
    by_cases hsmall : Hcombined≤Z^g.τ
    · obtain ⟨receipt,hraw⟩:=actualInnerSmallRaw hH N hj hQ0 hQt hbeta hBetaHigh g Cs epsNode hepsNode
        (Fintype.card alpha) hcard hRate hmu degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
        source caps primitive hm hphysical hlarge hOld hHigh hTsource reflected second firstHeight key firstIndex hf1 hinj
        chi0 m hm0 hml hm2 Psi t0 u hsmall constant eps Bsrc control degree hIH hconstant heps hchild hBsrc
        hCs hCpay hCdirect hKt hKcol hC0 hC1 hKdirect
      have hv:=receipt.family.value_nonneg hZ0.le
      have hctrlMono : baseControl≤ctrl:=mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (N.profiles.control_nonneg _) (Cycle63Physical.profile_control_mono N.profiles hSp) 2) hp0
      have hraw' : Z^outer*mainLowPhysicalCompleteCost (Fintype.card N.slots) 1 (1/4) second ordinary coefficient t0 u select≤
          (Ksmall*Z^(outer+target)+Kret*receipt.family.value)*ctrl*Hcombined^Dsmall:=by
        exact hraw.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hctrlMono (by positivity)) (pow_nonneg (by positivity) _))
      have hnormalized:=normalize_raw_small_source Z outer target _ Ksmall Kret receipt.family.value ctrl
        (Hcombined^Dsmall) hZ0 hraw'
      have hc:=actual_node_native_coarse_bound N Cs Kcoarse hKcoarse coarse caps epsNode primitive Sp hzero
        reflected second firstHeight key firstIndex hf1 hinj Psi chi0 (fun _=>internalQ C.Q C.etaSeed)
        (fun _=>m) t0 u g.e select
      have hc' : mainLowPhysicalCompleteCost (Fintype.card N.slots) 1 (1/4) second ordinary coefficient t0 u select≤
          Kcoarse*ctrl*Z^(nativeLowCoarseExponent (Fintype.card alpha) (Fintype.card alpha)):=by
        simpa only [←hRate,hphysCard,ctrl,physical,mul_assoc] using hc
      refine ⟨receipt,?_⟩
      exact splice_actual_raw_physical (Fintype.card alpha) g.τ g.τ_pos Dsmall
        Z outer target firstHeight N.height t0 u _ Ksmall Kcoarse Kret ctrl receipt.family.value
        N.localBase_gt_one hTarget N.height_nonneg hsmallK hKcoarse hretK hctrl hv
        (fun _=>hnormalized) hc'
    · obtain ⟨receipt,hempty,hlargeRaw⟩:=actual_node_low_large_height_empty_return N g hmu hRate
        Cs Ksmall Kcoarse hsmallK hKcoarse Dsmall coarse caps epsNode primitive Sp hzero
        reflected second firstHeight outer target hTarget rfl key firstIndex hf1 hinj
        Psi chi0 (fun _=>internalQ C.Q C.etaSeed) (fun _=>m) t0 u g.e select hsmall
        (Bsrc (nextInner j hj)) (fun _=>box)
      have hlargeRaw' : Z^outer*mainLowPhysicalCompleteCost (Fintype.card N.slots) 1 (1/4) second ordinary coefficient t0 u select≤
          ((2+4*Real.pi)^Dall*(Ksmall+Kcoarse))*controlAll*Z^(outer+target):=by
        simpa only [←hRate,hphysCard,Dall,controlAll,physical,mul_assoc] using hlargeRaw
      have hv:=receipt.family.value_nonneg hZ0.le
      have hcontrolAll : 0≤controlAll:=by
        dsimp only [controlAll]
        positivity
      have hpow : 0≤(2+4*Real.pi)^Dall:=pow_nonneg (by positivity) _
      exact ⟨receipt,hlargeRaw'.trans (le_add_of_nonneg_right
        (mul_nonneg (mul_nonneg (mul_nonneg hpow hretK) hcontrolAll) hv))⟩

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualInnerPerBinAllHeight
