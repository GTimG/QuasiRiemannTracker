/- Genuine small-height INNER physical LOW source, before final OLD payment.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerSmallPhysical
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
def actualInnerSmallRaw
    (hH : RayOrthogonality.globalUnits M≤H)(N : ReachableNode C j)(hj : j.val<3)
    (hQ0 : internalQ C.Q C.etaSeed≠0)(hQt : internalQ C.Q C.etaSeed≠⊤)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hBetaHigh : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule)(Cs epsNode : ℝ)(hepsNode : 0<epsNode)
    (rateBudget : ℕ)(hcard : Fintype.card N.slots≤rateBudget)
    (hRate : g.δ=nativeDriverRate rateBudget)(hmu : g.μ=nativeMu)
    (degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))(Kterminal Cpay Kcol : ℝ)
    (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C0 C1 Kdirect : ℝ)
    (source : InnerCanonicalNativeSpec hH N hj hQ0 hQt hbeta g Cs epsNode
      (postDictionaryRate C.Bnorm rateBudget) hepsNode (postDictionaryRate_budgets C.normCap_nonneg rateBudget).1
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect)
    (caps : letI : Cycle63.AffineLedger:=N.ledger
      GeometryAffineLowSourceGates (N.input hH) N.profiles Cs N.localBase)
    (primitive : letI : Cycle63.AffineLedger:=N.ledger
      InnerSelectedPrimitivePacket hH C j N Cs caps epsNode rateBudget)
    (hm : Matches M H hH (N.input hH) C.etaSeed (fun i=>C.theta i)
      (fun i=>C.originalWeight i/N.unit) (fun i=>C.sigma i) (fun i=>C.frequency i) C.W 2 N.localBase)
    (hphysical : innerPhysicalThreshold hH j (postDictionaryRate C.Bnorm rateBudget)
      (postDictionaryRate_budgets C.normCap_nonneg rateBudget).1 N.slots≤N.localBase)
    (hlarge : actualSelectedScalarThreshold rateBudget (postDictionaryRate C.Bnorm rateBudget)
      (postDictionaryRate_budgets C.normCap_nonneg rateBudget).1≤N.localBase)
    (hOld : actualSelectedOldThreshold C.Bnorm C.normCap_nonneg rateBudget (Fintype.card N.slots)≤N.localBase)
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
    (hsmall : 2*(1+|firstHeight|+N.height+2*Real.pi*(|t0|+|u|))≤N.localBase^g.τ)
    (constant eps Bsrc : Fin 4→ℝ)(control : Fin 4→Finset (ℕ×ℕ))(degree : Fin 4→ℕ)
    (hIH : ∀Nc : ReachableNode C (nextInner j hj),Nonempty (NodeOutput hH Nc
      (constant (nextInner j hj)) (eps (nextInner j hj)) (Bsrc (nextInner j hj))
      (control (nextInner j hj)) (degree (nextInner j hj))
      (fun _=>rootNativeDyadBox C.globalBase rateBudget)))
    (hconstant : 0≤constant (nextInner j hj))(heps : 0≤eps (nextInner j hj))
    (hchild : eps (nextInner j hj)≤oldLoss epsNode)(hBsrc : Bsrc (nextInner j hj)=250000)
    (hCs : 1≤Cs)(hCpay : 1≤Cpay)(hCdirect : 1≤Cdirect)(hKt : 0≤Kterminal)
    (hKcol : 0≤Kcol)(hC0 : 0≤C0)(hC1 : 0≤C1)(hKdirect : 0≤Kdirect) :=
  letI : Cycle63.AffineLedger:=N.ledger
  let Z:=N.localBase
  let s:=N.input hH
  let r:=postDictionaryRate C.Bnorm rateBudget
  let hr:=(postDictionaryRate_budgets C.normCap_nonneg rateBudget).1
  let box:=rootNativeDyadBox C.globalBase rateBudget
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
  let physical:=geometryHighFactor reflected (geometrySupportConstant rateBudget 1 (1/4) (1/4)) key
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
  let Kold:=actualSelectedOldConstant C.Bnorm C.normCap_nonneg rateBudget
  let Kbox:=actualSelectedOldBoxConstant C.Bnorm C.normCap_nonneg rateBudget (Fintype.card N.slots)
  let target:=geometryAffineLowTarget g (Fintype.card N.slots) (nodeSourceAmp N)
    (frequencyLoss Z 32 (nativeMu/64)+nativeMu/8) C.slotMesh+(1-N.state.rowWidth)
  let Dsmall:=max (max degreeTerminal (degree (nextInner j hj))) degreeDirect
  let Hcombined:=2*(1+|firstHeight|+N.height+2*Real.pi*(|t0|+|u|))
  let baseControl:=(N.profiles.control ((controlTerminal∪control (nextInner j hj))∪controlDirect))^2*physical
  show ∃receipt : NativeNodeForestReceipt hH N (Bsrc (nextInner j hj)) (fun _=>box),
    Z^outer*mainLowPhysicalCompleteCost (Fintype.card N.slots) 1 (1/4) second ordinary coefficient t0 u select≤
      (innerRawOldConstant (Fintype.card N.slots) g.e Cu Cg Kold Kbox*Z^(outer+target)+
        innerRawReturnConstant (Fintype.card N.slots) g.e Cu Cg*receipt.family.value)*baseControl*Hcombined^Dsmall from by
    have hZ0:=zero_lt_one.trans N.localBase_gt_one
    have hCg : 0≤Cg:=by
      have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
      have hCs0:=zero_le_one.trans hCs
      have hCp0:=zero_le_one.trans hCpay
      have hCd0:=zero_le_one.trans hCdirect
      dsimp only [Cg,nativeColumnSourceConstant]
      positivity
    have hfixed : 0≤fixed:=by have hh:=N.height_nonneg;dsimp only [fixed];positivity
    have hp0 : 0≤physical:=(geometry_high_factor_pos reflected _ key
      (geometrySupportConstant_pos rateBudget 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
    have hCu : 0≤Cu:=(innerPhysicalConstant_pos hH j r hr N.slots).le
    have hpref : 0≤pref:=innerPhysicalPrefactor_nonnegative _ _
    have hKo : 0≤Kold:=(actualSelectedOldConstant_pos C.Bnorm C.normCap_nonneg rateBudget).le
    have hKb : 0≤Kbox:=(actualSelectedOldBoxConstant_pos C.Bnorm C.normCap_nonneg rateBudget (Fintype.card N.slots)).le
    have hrow1 : N.state.rowWidth≤1:=by
      have hw:=N.width_le_one
      unfold NaturalState.width at hw
      linarith only [hw,N.state.character_nonneg]
    have hamp0:=(actual_node_canonical_scalar_gates N).2.1
    have hamp1 : nodeSourceAmp N≤1:=by rw [←nodeSourceAmp_eq_native N];exact N.actual_amp_le_one
    have hamp4 : |nodeSourceAmp N|≤4:=by rw [abs_of_nonneg hamp0];linarith only [hamp1]
    have homega0 : 0≤frequencyLoss Z 32 (nativeMu/64)+nativeMu/8:=by
      have hf:=frequencyLoss_nonneg Z 32 (nativeMu/64) N.localBase_gt_one (by norm_num)
        (div_nonneg nativeMu_pos.le (by norm_num))
      linarith only [hf,nativeMu_pos]
    have homega4 : |frequencyLoss Z 32 (nativeMu/64)+nativeMu/8|≤4:=by
      rw [abs_of_nonneg homega0]
      exact primitive.omega.trans (by norm_num)
    have hOldRaw:=actualSelectedOldTargetAt C.Bnorm C.normCap_nonneg rateBudget (Fintype.card N.slots) hcard
      Z N.localBase_gt_one hOld g hmu (actualNodePrice_le_native N) s N.profiles Cs caps le_rfl
      reflected second N.state.puncture N.state.rowWidth (nodeSourceAmp N) firstHeight (oldLoss epsNode)
      C.slotMesh (actualNodeLocalSourcePad (hH:=hH) N) N.state.row_nonneg hrow1 hamp0 hamp4 homega4
      primitive.pad key caps.zero₁ caps.zero₂ firstIndex hf1 hinj Psi Cg fixed hCg hfixed
    let fee:=r+3*(((Fintype.card N.slots:ℝ)+2)*3)*r
    have hfee : (1+9*((Fintype.card N.slots:ℝ)+2))*postDictionaryRate C.Bnorm rateBudget=fee:=by
      dsimp only [fee,r]
      ring
    have hOldPaid : Z^outer*Z^fee*oldBase≤(Kold*Cg*Kbox)*fixed*physical*Z^(outer+target):=by
      have h:=hOldRaw
      have hh : (N.state.rowWidth+3*g.δ-nodeSourceAmp N+oldLoss epsNode)+
          geometryAffineLowTarget g (Fintype.card N.slots) (nodeSourceAmp N)
            (frequencyLoss Z 32 (nativeMu/64)+nativeMu/8) C.slotMesh+(1-N.state.rowWidth)=outer+target:=by
        dsimp only [outer,target]
        ring
      rw [hfee,hh] at h
      simpa only [oldBase,outer,target,Kold,Kbox,physical,common,r,actualSelectedOldConstant,
        show geometrySupportConstant rateBudget 1 (1/4) (1/4)=(64:ℝ) by norm_num [geometrySupportConstant],
        mul_assoc,mul_left_comm,mul_comm] using h
    obtain ⟨receipt,hcost⟩:=actualInnerSmallPhysical hH N hj hQ0 hQt hbeta hBetaHigh g Cs epsNode hepsNode
      rateBudget hcard hRate degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
      source caps primitive hm hphysical hlarge hHigh hTsource reflected second firstHeight key firstIndex hf1 hinj
      chi0 m hm0 hml hm2 Psi t0 u hsmall constant eps Bsrc control degree hIH hconstant heps hchild hBsrc
      hCs hCpay hCdirect hKt hKcol hC0 hC1 hKdirect
    have hcost' : mainLowPhysicalCompleteCost (Fintype.card N.slots) 1 (1/4) second ordinary coefficient t0 u select≤
        pref*(max 0 oldBase*(Cu*Z^fee)+2*(Cu*(Z^(-outer)*(Cg*fixed*physical)))*receipt.family.value):=by
      change mainLowPhysicalCompleteCost (Fintype.card N.slots) 1 (1/4) second ordinary coefficient t0 u select≤
        (1/lowerFactor (Fintype.card N.slots) 1 (1/4))*
          ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(Fintype.card (BufferIndex g.e):ℝ)*
            (max 0 oldBase*(Cu*Z^fee)+2*(Cu*(Z^(-outer)*(Cg*fixed*physical)))*receipt.family.value)) at hcost
      simpa only [pref,innerPhysicalPrefactor,mul_assoc] using hcost
    have hpaid:=native_small_physical_paid hZ0 hCu hpref (by positivity : 0≤Kold*Cg*Kbox) hfixed hp0 hcost' hOldPaid
    have hheight : fixed≤(N.profiles.control ((controlTerminal∪control (nextInner j hj))∪controlDirect))^2*Hcombined^Dsmall:=by
      exact mul_le_mul_of_nonneg_left
        (native_small_source_height_control second firstHeight N.height t0 u N.height_nonneg Dsmall) (sq_nonneg _)
    have hv:=receipt.family.value_nonneg hZ0.le
    refine ⟨receipt,hpaid.trans ?_⟩
    calc
      _=((pref*Cu*(Kold*Cg*Kbox))*physical*Z^(outer+target)+
          (pref*(2*(Cu*Cg)))*physical*receipt.family.value)*fixed:=by ring
      _≤((pref*Cu*(Kold*Cg*Kbox))*physical*Z^(outer+target)+
          (pref*(2*(Cu*Cg)))*physical*receipt.family.value)*
          ((N.profiles.control ((controlTerminal∪control (nextInner j hj))∪controlDirect))^2*Hcombined^Dsmall):=
        mul_le_mul_of_nonneg_left hheight (by positivity)
      _=_:=by
        dsimp only [innerRawOldConstant,innerRawReturnConstant,pref,baseControl]
        ring

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualInnerSmallRaw
