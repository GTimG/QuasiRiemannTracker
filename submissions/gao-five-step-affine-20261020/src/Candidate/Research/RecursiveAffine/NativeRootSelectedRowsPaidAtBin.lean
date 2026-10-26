/- The literal ROOT selected row returns the SAME physical source/output.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootSelectedRowsPaidResidual
import Candidate.Research.RecursiveAffine.NativeSourceSide
import Candidate.Research.RecursiveAffine.NativeRootPaidRowsResidual
import Candidate.Research.RecursiveAffine.NativeRootAnalyticFee
import Candidate.Research.RecursiveAffine.NativeRootResidualNormalization
import Candidate.Research.RecursiveAffine.NativeRootPaidRowsReceiptWithLoss
import Candidate.Research.RecursiveAffine.NativeRootSelectedPaidGateAtBin
import Candidate.Research.RecursiveAffine.NativeRootSelectedFamilyPrefix

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
open Cycle153HighProvider Cycle153ReachableGeometry Cycle153AnalyticPrimitive Cycle153.RegionalSchedule
open CenteredMomentFirstDiscardedEnergy CenteredMomentOriginalCommonHarmonic CenteredMomentNaturalRowSource
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable (hH : RayOrthogonality.globalUnits M ≤ H)(C : SourceContext (α:=alpha) M H)
noncomputable local instance rootSelectedRowsPaidAtBinLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
open CenteredMomentEnergyState CenteredMomentFirstAmplificationChoice
open Cycle153RootStep Cycle153JointCount Cycle153ActualRootSourceGates Cycle153ActualSourceGates
attribute [local irreducible] NativeColumnOutputTrace nodeOfNativeContinuation
attribute [local irreducible] nativeSharedColumnFixed nativeColumnSourceConstant
attribute [local irreducible] actualRootSelectedRowsPaidVector

/-- Use the genuine native selected family and its literal prefix on each
ROOT row. The only recursive premise is availability of completed inner
NodeOutputs; there is no assumed column/energy/count/prefix constructor. -/
def actualRootSelectedRowsPaidAtBin
    (hQ0 : internalQ C.Q C.etaSeed≠0)(hQt : internalQ C.Q C.etaSeed≠⊤)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (g : GeometryAffineLowSchedule)(Cs epsNode epsShell : ℝ)(hepsNode : 0<epsNode)(hShell : 0<epsShell)
    (degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))(Kterminal Cpay Kcol : ℝ)
    (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C0 C1 Kdirect : ℝ)
    (source : RootCanonicalNativeSpec hH C hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect)
    (s : Input alpha)(p : Profiles (1/4) (9/4))
    (F0 : NaturalRow C.etaSeed 1)(R0 : Ideal O)(hparent : ParentPresentation s.η F0 R0)
    (caps : GeometryAffineLowSourceGates s p Cs C.globalBase)
    (feeBudget : ℕ)
    (gates : ActualRootPaidGateAtBinPackage C.globalBase C.globalBase_gt_one feeBudget s C.originalWeight p Cs caps)
    (hm : Matches M H hH s C.etaSeed (fun i=>C.theta i) (fun i=>C.originalWeight i)
      (fun i=>C.sigma i) (fun i=>C.frequency i) C.W 2 C.globalBase)
    (hwL : ∀i,C.originalWeight i≤Cycle25.Energy.commonMesh 2 28 1 (oldLoss epsNode))
    (hwr : ∀i,C.originalWeight i/31≤1)
    (hscale : ∀i,s.P i=C.globalBase^(C.originalWeight i))
    (hwindow : Cycle63.AffineLedger.PlainWindow
      (length C.globalBase s.X₁) (length C.globalBase s.X₂) (∑i,C.originalWeight i))
    (mesh : ℝ)(hmesh : 0≤ mesh)(hwm : ∀i,C.originalWeight i≤ mesh)
    (feeBound : ∀(R : Finset alpha)
      (hd : (∑i∈R,C.originalWeight i)≤rootDetectorDeletion C.originalWeight+mesh),
      let f:=actualRootNativeFeeAtMesh C s epsNode feeBudget R mesh hmesh hd
      f.amount≤1/1000000000000000 ∧
      (rootDetectorDeletion C.originalWeight≤∑i∈R,C.originalWeight i→
        f.junction*f.modelDeletion+f.amount≤2))
    (height : ℝ)(hheight : 0≤height)(hfreq : ∀i,|C.frequency i|≤height)
    (sourceHeight : ℝ)(buffer : BufferIndex g.e)(hp : 1≤buffer.1.val)
    (hSmallHeight : |sourceHeight|+height+C.globalBase^g.τ/2≤5*C.globalBase^g.τ)
    (hHigh : (3+(3*buffer.1.val+2:ℕ)*C.globalBase^g.τ)^2≤(C.globalBase^(31:ℝ))^(3:ℝ))
    (reflected second : Bool)(firstHeight epsV : ℝ)(hepsV0 : 0≤epsV)(hepsV : epsV≤1)
    (hepsVCoeff : epsV≤nativeDriverRate feeBudget)
    (hprefixSmall : Real.logb C.globalBase 4+2*(Fintype.card alpha:ℝ)*Real.logb C.globalBase (9/4)+(nativeMu/64)/2≤1)
    (key : ℤ×(Fin 5→ℤ)){Label : Type}[Fintype Label]
    (hz1 : s.W₁ 0=0)(hz2 : s.W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key)
    (hf1 : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val)
      1 s.ν s.W s.P≠0)
    (Ds : Finset (Ideal O))(T : ℝ)
    (hMask : ∀r : NativeLowRows reflected s 1 1 C.globalBase 1 (rootSourceAmp C.originalWeight)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card alpha)
      C.globalBase_gt_one key hz1 hz2 firstIndex,
      let datum:=geometryLowSecondDatum reflected s 1 1 C.globalBase 1 (rootSourceAmp C.originalWeight)
        (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card alpha)
        C.globalBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2
      let E:=if second then datum.D else datum.C
      datum.R*E≠0 ∧ ((datum.R*E).absNorm:ℝ)≤C.globalBase^(28:ℝ) ∧ Supported E ∧ datum.seed∣E)
    (hfit : 1+Real.logb C.globalBase (s.η.modulus.absNorm:ℝ)≤1+(nativeMu/8)/2)
    (hconstants : Real.logb C.globalBase CenteredMomentFirstPhysicalSource.fixedPresentationCost+
      2*(Fintype.card alpha:ℝ)*Real.logb C.globalBase (9/4)+Real.logb C.globalBase 1+
      Real.logb C.globalBase (4*(CenteredMomentSecondRadicalBudget.fixedFactor:ℝ))≤(nativeMu/8)/2)
    (hpad : supportPadding (Fintype.card alpha) (9/4) s.b₁ s.b₂ C.globalBase≤nativeMu/8)
    (homega : frequencyLoss C.globalBase 32 (nativeMu/64)+nativeMu/8≤(1/1000000000000000:ℝ))
    (hT : 1≤T)(hDs : ∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T)
    (chi0 : NativeLowRows reflected s 1 1 C.globalBase 1 (rootSourceAmp C.originalWeight)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card alpha)
      C.globalBase_gt_one key hz1 hz2 firstIndex→RayFourExpansion.RayCharacter)
    (chi psi : RayFourExpansion.RayCharacter)(m : O)(hm0 : m≠0)
    (hml : goodLambda∣m)(hm2 : (2:O)∣m)
    (hTsource : 2<C.globalBase^g.τ)(hBetaHigh : HeckeZeroSupremum.beta≤7/8)
    (hfinite : Real.logb C.globalBase 128+
      (2*(Fintype.card alpha:ℝ)*Real.logb C.globalBase (9/4)+
        Real.logb C.globalBase (max 1 s.b₁*max 1 s.b₂))≤1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin)
    (constant eps Bsrc : Fin 4→ℝ)(control : Fin 4→Finset (ℕ×ℕ))
    (degree : Fin 4→ℕ)(boxes : Fin 4→ℕ→Finset (Fin 4→ℤ))
    (hIH : ∀Nc : ReachableNode C (0:Fin 4),Nonempty (NodeOutput hH Nc
      (constant (0:Fin 4)) (eps (0:Fin 4)) (Bsrc (0:Fin 4))
      (control (0:Fin 4)) (degree (0:Fin 4)) (boxes (0:Fin 4))))
    (hconstant : 0≤constant (0:Fin 4))(heps : 0≤eps (0:Fin 4))
    (hchild : eps (0:Fin 4)≤oldLoss epsNode)
    (rootBox : Finset (Fin 4→ℤ))(hBsrc : 0≤Bsrc (0:Fin 4))
    (hfirst : Function.Injective (fun l=>(geometryFirstLabel s 1 1 (C.globalBase^(1:ℝ)) C.globalBase
      (nativeMu/64) (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key
      (firstIndex l).1.val,(firstIndex l).1.val.2.1.val)))
    (sourceFacts : ∀r : NativeLowRows reflected s 1 1 C.globalBase 1 (rootSourceAmp C.originalWeight)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card alpha)
      C.globalBase_gt_one key hz1 hz2 firstIndex,
      DecoratedFacts (fun _ : Unit=>(1:O)) (!reflected)
        (fun _ l=>(firstDictionaryUnit (!reflected) C.etaSeed 1 F0 R0 l:O))
        C.globalBase (Bsrc (0:Fin 4)) rootBox
        ((),nativeLowHistoryCode reflected s 1 1 C.globalBase 1 (rootSourceAmp C.originalWeight)
          (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card alpha)
          C.globalBase_gt_one key hz1 hz2 firstIndex r))
    (Psi : 𝓢(ℝ,ℂ))
    (hepsVpos : 0<epsV)
    (hlarge : actualSelectedScalarThreshold (Fintype.card alpha) epsV hepsVpos≤C.globalBase)
    (hCs : 1≤Cs)(hCpay : 1≤Cpay)(hCdirect : 1≤Cdirect)(hKt : 0≤Kterminal)
    (hKcol : 0≤Kcol)(hC0 : 0≤C0)(hC1 : 0≤C1)(hKdirect : 0≤Kdirect)
    (hdelta : g.δ=nativeDriverRate feeBudget)
    (hVrate : epsV=postDictionaryRate C.Bnorm feeBudget)
    (hShellrate : epsShell=postDictionaryRate C.Bnorm feeBudget) :
    let Z:=C.globalBase
    let amp:=rootSourceAmp C.originalWeight
    let Rows:=NativeLowRows reflected s 1 1 Z 1 amp (nativeMu/64) (nativeMu/8) (9/4)
      firstHeight (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2 firstIndex
    let datum:=fun r : Rows=>geometryLowSecondDatum reflected s 1 1 Z 1 amp (nativeMu/64) (nativeMu/8)
      (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2
    let selector:=fun r : Rows=>mainLowCanonicalSelector M H hH (datum r) (chi0 r) chi psi
      (internalQ C.Q C.etaSeed) C.fixed_small m hm0 hml hm2 Z 28 C.globalBase_gt_one
      second (hMask r).1 (hMask r).2.1 C.etaSeed (inf_le_left.trans C.Q_le_M) inf_le_right
      g.e (Z^g.τ) g.e_pos hTsource hbeta hBetaHigh
    let zs:=fun r : Rows=>mainLowPaymentRows
      (mainLowSourceRows second (ordinarySecondDatum (datum r) (chi0 r) (internalQ C.Q C.etaSeed) m) (fun _=>True))
      (selector r) buffer
    let mass:=fun l=>geometryFirstHighMass reflected s 1 1 Psi 1 Z (nativeMu/64) g.δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val
    let childSrc:=fun l=>geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key firstHeight (firstIndex l)
    let coefficient:=selectedPhysicalCoefficient datum (fun r=>mass r.val.1) (fun r=>volume (childSrc r.val.1))
    let sourceEnergy:=∑r : Rows,∑D∈Ds,Cycle153LowPhysical.nativeResidualCost second
      (fun r=>ordinarySecondDatum (datum r) (chi0 r) (internalQ C.Q C.etaSeed) m) coefficient
      (fun _=>if second then psi⁻¹ else chi) (fun _=>sourceHeight) zs (fun _ _=>1) r D
    let Cg:=nativeColumnSourceConstant (Fintype.card alpha) Cs Cpay Kterminal (constant (0:Fin 4)) Kcol Cdirect C0 C1 Kdirect
    let baseFixed:=(p.control (controlTerminal∪control (0:Fin 4)∪controlDirect))^2*
      (1+|sourceHeight|+height)^(max (max degreeTerminal (degree (0:Fin 4))) degreeDirect)
    let physical:=geometryHighFactor reflected (geometrySupportConstant (Fintype.card alpha) 1 (1/4) (1/4)) key
    let common:=nativeMu/8+(nativeMu/64)/2-Cycle63.AffineLedger.lowReserve+nativeMu/64+
      2*g.δ*31*(Fintype.card alpha:ℝ)+Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)*
        (frequencyLoss Z 32 (nativeMu/64)+nativeMu/8+nativeMu/8)+Cycle63.AffineLedger.q*mesh
    let oldBase:=Cycle153LowPhysical.nativeOldSelectedCost reflected second s 1 Z 1 amp
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2 firstIndex
      Psi g.δ epsShell (common+actualRootSourcePad C s) Cg baseFixed
    let outer:=1+3*g.δ-amp+oldLoss epsNode
    let wholeBoxes : ℕ→Finset (Fin 4→ℤ):=fun k=>Nat.casesOn k rootBox (boxes (0:Fin 4))
    ∃receipt : NativeRootForestReceipt (hH:=hH) (C:=C) (Bsrc (0:Fin 4)) wholeBoxes,
      (∀d pc,(receipt.family.part d pc).loss≤5/1000000000000) ∧
      sourceEnergy≤(oldBase+Z^(-outer)*(Cg*baseFixed*physical)*receipt.family.value)*(2*T)^(3*epsShell) :=by
  obtain ⟨exponent,sideLower,hbin⟩:=actual_first_bin_side_cancellation s 1 1 (C.globalBase^(1:ℝ))
    C.globalBase (nativeMu/64) 3 (Real.logb C.globalBase (volume s))
    (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) C.globalBase_gt_one
    squarefree_one hz1 hz2 caps.sourceCap key reflected
  let hside : ∀l : FirstColumnIndex (geometryFirstSource s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key),
      (3*nativeDriverRate feeBudget-sideLower)+lowLabelSide reflected C.globalBase (Real.logb C.globalBase (volume s))
        (geometryFirstLabel s 1 1 (C.globalBase^(1:ℝ)) C.globalBase (nativeMu/64)
          (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key l)≤actualSideError C.globalBase feeBudget:=
    fun l=>(hbin.2 l).2.2.2 (3*nativeDriverRate feeBudget)
  exact actualRootSelectedRowsPaidResidual hH C hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
    degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
    source s p F0 R0 hparent caps feeBudget gates hm hwL hwr hscale hwindow mesh hmesh hwm feeBound
    height hheight hfreq sourceHeight buffer hp hSmallHeight hHigh reflected second firstHeight epsV hepsV0 hepsV
    hepsVCoeff hprefixSmall key hz1 hz2 firstIndex sideLower hside hf1 Ds T hMask
    hfit hconstants hpad homega hT hDs chi0 chi psi m hm0 hml hm2 hTsource hBetaHigh hfinite hgrid
    constant eps Bsrc control degree boxes hIH hconstant heps hchild rootBox hBsrc hfirst sourceFacts
    Psi (fun l=>(hbin.2 (firstIndex l).1.val).2.2.1) hepsVpos hlarge hCs hCpay hCdirect hKt hKcol hC0 hC1 hKdirect
    hdelta hVrate hShellrate

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualRootSelectedRowsPaidAtBin
