/- The actual canonical ROOT column producer, with genuine arithmetic callbacks.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootCanonicalInvoke
import Candidate.Research.RecursiveAffine.NativeRootCoordinateReceipt
import Candidate.Research.RecursiveAffine.NativeRootColumnPaidResult
import Candidate.Research.RecursiveAffine.NativeRootCanonicalEnvelope
import Candidate.Research.RecursiveAffine.NativeDirectCertificate

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedVariables false
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153ActualColumn
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily CanonicalQuadraticSieve CenteredMomentEnergyState
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
noncomputable local instance rootPaidColumnEnergyInputsLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
open Cycle153RootStep Cycle153JointCount
attribute [local irreducible] NativeColumnOutputTrace nodeOfNativeContinuation
attribute [local irreducible] actualCanonicalRootCoordinateReceipt
attribute [local irreducible] CenteredMomentCommonProfile.liveIndices
attribute [local irreducible] CenteredMomentDivisorRaw.liveIndices originalEmbedding commonData rawDaughterScale
attribute [local irreducible] nativeSharedColumnFixed nativeColumnSourceConstant

/-- Apply the literal canonical source operator and construct all three
recursive callbacks from the SAME physical daughter. The primitive input
conditions are the actual native source fit, finite-error, canonical-row
and prefix gates; no column, daughter or node-energy bound is an input.
The only recursive input is availability of genuine strictly deeper
NodeOutputs, chosen before this source configuration. -/
def NativeRootPaidColumnEnergyInputs
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
    (hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin) : Prop :=
  let omega:=frequencyLoss C.globalBase 32 (nativeMu/64)+nativeMu/8
  let st:=retainedState C.globalBase 28 C.globalBase_gt_one (gg.datum.τ ray)
    (internalQ C.Q C.etaSeed) (ch.R₂*ch.E₂) hP hPN gg.datum.radius gg.datum.C gg.datum.D gg.datum.inactive
  let u:=nativeUnit 1 C.globalBase (rootSourceAmp C.originalWeight) omega (nativeMu/8) (nativeMu/64)
    ch.C₁ gg.D₁ gg.datum.C gg.datum.D gg.datum.inactive
  let width:=actual_root_source_unit C s ch omega (nativeMu/64) (nativeMu/8) (9/4)
    (Fintype.card alpha) gg (actual_root_canonical_scalar_gates C.originalWeight
      ⟨hwindow.slots_ge,hwindow.slots_le⟩).2.1 (by norm_num)
    ray (internalQ C.Q C.etaSeed) hP hPN hfit hconstants rfl
  let hpDatum : datum.R*(if second then datum.D else datum.C)≠0:=by
    simpa only [frame.puncture_eq,frame.own_eq] using hP
  let hnDatum : ((datum.R*(if second then datum.D else datum.C)).absNorm:ℝ)≤C.globalBase^(28:ℝ):=by
    simpa only [frame.puncture_eq,frame.own_eq] using hPN
  let ordinaryRows:=mainLowSourceRows second (ordinarySecondDatum datum chi0 (internalQ C.Q C.etaSeed) m) (fun _=>True)
  let selector:=mainLowCanonicalSelector M H hH datum chi0 chi psi (internalQ C.Q C.etaSeed) C.fixed_small
    m hm0 hml hm2 C.globalBase 28 C.globalBase_gt_one second hpDatum hnDatum C.etaSeed
    (inf_le_left.trans C.Q_le_M) inf_le_right g.e (C.globalBase^g.τ) g.e_pos hTsource hbeta hBetaHigh
  ∀(hzs : ∀z∈zs,z∈mainLowPaymentRows ordinaryRows selector buffer)
    (P : PrefixHighPresentation (prefixDictionary (0:Fin 4).val C.etaSeed) st.character st.puncture)
    (hPnorm : ((Ideal.span {P.mult}).absNorm:ℝ)≤C.globalBase^prefixCap (0:Fin 4).val)
    (hrelative : st.rowWidth+Real.logb C.globalBase ((Ideal.span {P.mult}).absNorm:ℝ)≤
      paid.coordinate 2+(Real.logb C.globalBase 4+2*(Fintype.card alpha:ℝ)*Real.logb C.globalBase (9/4)+(nativeMu/64)/2))
    (constant eps Bsrc : Fin 4→ℝ)(control : Fin 4→Finset (ℕ×ℕ))
    (degree : Fin 4→ℕ)(boxes : Fin 4→ℕ→Finset (Fin 4→ℤ))
    (hIH : ∀Nc : ReachableNode C (0:Fin 4),Nonempty (NodeOutput hH Nc
      (constant (0:Fin 4)) (eps (0:Fin 4)) (Bsrc (0:Fin 4))
      (control (0:Fin 4)) (degree (0:Fin 4)) (boxes (0:Fin 4))))
    (hconstant : 0≤constant (0:Fin 4))(heps : 0≤eps (0:Fin 4))
    (hchild : eps (0:Fin 4)≤oldLoss epsNode),
  let firstInput:=withHeight ch.first (gg.datum.τ ray) sourceHeight
  let SourceK:=nativeColumnSourceConstant (Fintype.card alpha) Cs Cpay Kterminal
    (constant (0:Fin 4)) Kcol Cdirect C0 C1 Kdirect
  let Control:=p.control ((controlTerminal∪control (0:Fin 4))∪controlDirect)^2*
    (1+|sourceHeight|+height)^(max (max degreeTerminal (degree (0:Fin 4))) degreeDirect)*(2*T)^(3*epsShell)
  let slotLoss:=2*g.δ*31*(Fintype.card alpha:ℝ)
  let OldPaid:=secondNominal 1 C.globalBase (rootSourceAmp C.originalWeight) omega ch.C₁ gg.D₁
    gg.datum.C gg.datum.D gg.datum.inactive+rootSourceAmp C.originalWeight+
    (nativeMu/8+(nativeMu/64)/2-Cycle63.AffineLedger.lowReserve+nativeMu/64+slotLoss+
      Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)*(omega+nativeMu/8)+Cycle63.AffineLedger.q*mesh)+
    lowAllowance C.globalBase ch.C₁ gg.D₁ gg.datum.C gg.datum.D ch.E₂
  Nonempty (RootColumnPaidResult (hH:=hH) C s paid epsNode feeBudget mesh hmesh P.mult
    (constant (0:Fin 4)) (eps (0:Fin 4)) (Bsrc (0:Fin 4))
    (control (0:Fin 4)) (degree (0:Fin 4)) (boxes (0:Fin 4))
    (∑D∈Ds,∑z∈zs,(1:ℝ)*‖CenteredMomentCommonPairedSource.normalizedColumn firstInput ch.E₂ hOwn ch.R₂ seed D z‖^2)
    (SourceK*Control*(ch.E₂.absNorm:ℝ)^(epsShell-1)*C.globalBase^(actualRootSourcePad C s))
    (C.globalBase^OldPaid)
    (fun R=>C.globalBase^(slotLoss+Cycle63.AffineLedger.q*((∑i∈R,C.originalWeight i/1)+mesh))))

end
end OAI.SevenEighths.Cycle153ActualColumn
