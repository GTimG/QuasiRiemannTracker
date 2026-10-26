/- The literal ROOT selected row returns the SAME physical source/output.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootSelectedPhysicalRaw
import Candidate.Research.RecursiveAffine.NativeRootLargeHeight
import Candidate.Research.RecursiveAffine.NativeSelectedOldActual
import Candidate.Research.RecursiveAffine.NativeSelectedOldLedgerPrice
import Candidate.Research.RecursiveAffine.NativeRootPhysicalThreshold
import Candidate.Research.RecursiveAffine.NativePhysicalPoolAliases
import Candidate.Research.RecursiveAffine.NativeSourceSide
import Candidate.Research.RecursiveAffine.NativeRootPaidRowsResidual
import Candidate.Research.RecursiveAffine.NativeRootAnalyticFee
import Candidate.Research.RecursiveAffine.NativeRawOldExponent
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
noncomputable local instance rootSelectedAllHeightLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
open CenteredMomentEnergyState CenteredMomentFirstAmplificationChoice
open Cycle153RootStep Cycle153JointCount Cycle153ActualRootSourceGates Cycle153ActualSourceGates
open CenteredMomentSecondCanonicalScalar CenteredMomentCommonPairedSource
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSecondEnergySplit
open CenteredMomentSecondInputCapacitySource
attribute [local irreducible] NativeColumnOutputTrace nodeOfNativeContinuation
private theorem actual_root_column_constant_nonneg
    (n : ℕ)(Cs Cpay Kterminal Kchild Kcol Cdirect C0 C1 Kdirect : ℝ)
    (hCs : 1≤Cs)(hCpay : 1≤Cpay)(hCdirect : 1≤Cdirect)
    (hKt : 0≤Kterminal)(hchild : 0≤Kchild)(hKcol : 0≤Kcol)
    (hC0 : 0≤C0)(hC1 : 0≤C1)(hKdirect : 0≤Kdirect) :
    0≤nativeColumnSourceConstant n Cs Cpay Kterminal Kchild Kcol Cdirect C0 C1 Kdirect:=by
  have hdiag:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
  have hcs0:=zero_le_one.trans hCs
  have hcp0:=zero_le_one.trans hCpay
  have hcd0:=zero_le_one.trans hCdirect
  unfold nativeColumnSourceConstant
  exact mul_nonneg (mul_nonneg (by positivity) hdiag)
    (add_nonneg (mul_nonneg (mul_nonneg hKcol (pow_nonneg hcp0 _)) (add_nonneg hKt hchild))
      (mul_nonneg (mul_nonneg hKdirect (pow_nonneg hcd0 _)) (add_nonneg hC0 hC1)))

attribute [local irreducible] nativeSharedColumnFixed nativeColumnSourceConstant
attribute [local irreducible] actualRootSelectedRowsPaidVector

def actualRootSelectedAllHeightRaw
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
    (feeBudget : ℕ)(hcardBudget : Fintype.card alpha≤feeBudget)
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
    (chi0 : NativeLowRows reflected s 1 1 C.globalBase 1 (rootSourceAmp C.originalWeight)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card alpha)
      C.globalBase_gt_one key hz1 hz2 firstIndex→RayFourExpansion.RayCharacter)
    (m : O)(hm0 : m≠0)
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
    (hShellrate : epsShell=postDictionaryRate C.Bnorm feeBudget)
    (t0 u : ℝ)
    (hHigh : ∀buffer : BufferIndex g.e,
      (3+(3*buffer.1.val+2:ℕ)*C.globalBase^g.τ)^2≤(C.globalBase^(31:ℝ))^(3:ℝ))
    (hOperator : actualRootPhysicalThreshold (alpha:=alpha) hH C.Bnorm C.normCap_nonneg feeBudget
      (Fintype.card alpha)≤C.globalBase)
    (hOld : actualSelectedOldThreshold C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha)≤C.globalBase)
    (hmu : g.μ=nativeMu)
    (Kcoarse : ℝ)(hKcoarse : 0≤Kcoarse)
    (coarse : MainLowCompleteCoarseSpec (α:=alpha) (Fintype.card alpha) 4 Cs (9/4) (9/4)
      (2*Real.log (9/4)) 4 1 (1/4) (nativeDriverRate feeBudget) (nativeMu/64) 3
      (nativeLowCoarseExponent (Fintype.card alpha) feeBudget) Kcoarse C.globalBase)
    (htarget : -1≤geometryAffineLowTarget g (Fintype.card alpha) (rootSourceAmp C.originalWeight)
      (frequencyLoss C.globalBase 32 (nativeMu/64)+nativeMu/8) mesh) :
    let Z:=C.globalBase
    let amp:=rootSourceAmp C.originalWeight
    let Rows:=NativeLowRows reflected s 1 1 Z 1 amp (nativeMu/64) (nativeMu/8) (9/4)
      firstHeight (Fintype.card alpha) C.globalBase_gt_one key hz1 hz2 firstIndex
    let datum:=fun r : Rows=>geometryLowSecondDatum reflected s 1 1 Z 1 amp (nativeMu/64) (nativeMu/8)
      (9/4) firstHeight (Fintype.card alpha) C.globalBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2
    let ordinary:=fun r : Rows=>ordinarySecondDatum (datum r) (chi0 r) (internalQ C.Q C.etaSeed) m
    let selector:=fun (r : Rows)(chi psi : RayFourExpansion.RayCharacter)=>
      mainLowCanonicalSelector M H hH (datum r) (chi0 r) chi psi
        (internalQ C.Q C.etaSeed) C.fixed_small m hm0 hml hm2 Z 28 C.globalBase_gt_one
        second (hMask r).1 (hMask r).2.1 C.etaSeed (inf_le_left.trans C.Q_le_M) inf_le_right
        g.e (Z^g.τ) g.e_pos hTsource hbeta hBetaHigh
    let mass:=fun l=>geometryFirstHighMass reflected s 1 1 Psi 1 Z (nativeMu/64) g.δ
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key (firstIndex l).1.val
    let childSrc:=fun l=>geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans C.globalBase_gt_one) _) key firstHeight (firstIndex l)
    let coefficient:=fun r : Rows=>mass r.val.1/volume (childSrc r.val.1)
    let sourceHeight:=nativePhysicalSourceHeight second firstHeight t0 u
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
    let shellFee:=epsShell+9*((Fintype.card alpha:ℝ)+2)*epsShell
    let Cu:=actualRootPhysicalConstant (alpha:=alpha) hH C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha)
    let target:=geometryAffineLowTarget g (Fintype.card alpha) amp
      (frequencyLoss Z 32 (nativeMu/64)+nativeMu/8) mesh
    let Dall:=max (max degreeTerminal (degree (0:Fin 4))) degreeDirect
    let controlAll:=(p.control (controlTerminal∪control (0:Fin 4)∪controlDirect))^2*physical*
      (1+|firstHeight|+height)^Dall*(1+|t0|)^Dall*(1+|u|)^Dall
    let Kold:=actualSelectedOldConstant C.Bnorm C.normCap_nonneg feeBudget
    let Kbox:=actualSelectedOldBoxConstant C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha)
    let fixedOperator:=(1/lowerFactor (Fintype.card alpha) 1 (1/4))*
      ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(Fintype.card (BufferIndex g.e):ℝ))
    let Kall:=fixedOperator*Cu*Kold*Cg*Kbox*(2+4*Real.pi)^Dall
    let Kreturn:=fixedOperator*2*Cu*Cg*(2+4*Real.pi)^Dall
    let Dlarge:=nativeLowLargeHeightDegree feeBudget g.τ g.τ_pos
    let Dfull:=max Dall Dlarge
    let SpFull:=insert (0,0) (controlTerminal∪control (0:Fin 4)∪controlDirect)
    let controlFull:=(p.control SpFull)^2*physical*
      (1+|firstHeight|+height)^Dfull*(1+|t0|)^Dfull*(1+|u|)^Dfull
    let Klarge:=(2+4*Real.pi)^Dlarge*Kcoarse
    ∃receipt : NativeRootForestReceipt (hH:=hH) (C:=C) (Bsrc (0:Fin 4)) wholeBoxes,
      Z^outer*mainLowPhysicalCompleteCost (Fintype.card alpha) 1 (1/4) second ordinary coefficient t0 u selector≤
        ((Kall+Klarge)*Z^(outer+target)+Kreturn*receipt.family.value)*controlFull :=by
  intro Z amp Rows datum ordinary selector mass childSrc coefficient sourceHeight Cg baseFixed physical common oldBase outer wholeBoxes shellFee Cu
    target Dall controlAll Kold Kbox fixedOperator Kall Kreturn Dlarge Dfull SpFull controlFull Klarge
  have hZ:=C.globalBase_gt_one
  have hZ0:=zero_lt_one.trans hZ
  have hCg : 0≤Cg:=actual_root_column_constant_nonneg _ _ _ _ _ _ _ _ _ _ hCs hCpay hCdirect hKt hconstant hKcol hC0 hC1 hKdirect
  have hCu : 0≤Cu:=(actualRootPhysicalConstant_pos (alpha:=alpha) hH C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha)).le
  have hKold : 0≤Kold:=(actualSelectedOldConstant_pos C.Bnorm C.normCap_nonneg feeBudget).le
  have hKbox : 0≤Kbox:=(actualSelectedOldBoxConstant_pos C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha)).le
  have hphysical : 0≤physical:=(geometry_high_factor_pos reflected _ key
    (geometrySupportConstant_pos _ _ _ _ (by norm_num) (by norm_num) (by norm_num))).le
  have hoperator : 0≤fixedOperator:=by
    dsimp only [fixedOperator]
    have hh:=(lowerFactor_pos (Fintype.card alpha) 1 (1/4) (by norm_num) (by norm_num)).le
    positivity
  have hKall : 0≤Kall:=by dsimp only [Kall];positivity
  have hKreturn : 0≤Kreturn:=by dsimp only [Kreturn];positivity
  have hKlarge : 0≤Klarge:=by dsimp only [Klarge];positivity
  have hcontrol0 : 0≤controlAll:=by dsimp only [controlAll];positivity
  have hcontrolFull : 0≤controlFull:=by dsimp only [controlFull];positivity
  have hcontrolMono : controlAll≤controlFull:=by
    have hc:=pow_le_pow_left₀ (p.control_nonneg _) (Cycle63Physical.profile_control_mono p
      (Finset.subset_insert (0,0) (controlTerminal∪control (0:Fin 4)∪controlDirect))) 2
    have h1:=pow_le_pow_right₀ (by linarith only [hheight,abs_nonneg firstHeight] : (1:ℝ)≤1+|firstHeight|+height) (Nat.le_max_left Dall Dlarge)
    have h2:=pow_le_pow_right₀ (by linarith only [abs_nonneg t0] : (1:ℝ)≤1+|t0|) (Nat.le_max_left Dall Dlarge)
    have h3:=pow_le_pow_right₀ (by linarith only [abs_nonneg u] : (1:ℝ)≤1+|u|) (Nat.le_max_left Dall Dlarge)
    dsimp only [controlAll,controlFull,Dfull,SpFull]
    exact mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hc hphysical) h1 (by positivity) (by positivity)) h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
  by_cases hsmall : 2*(1+|firstHeight|+height+2*Real.pi*(|t0|+|u|))≤Z^g.τ
  · obtain ⟨receipt,hraw⟩:=actualRootSelectedPhysicalRaw hH C hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
      source s p F0 R0 hparent caps feeBudget hcardBudget gates hm hwL hwr hscale hwindow mesh hmesh hwm feeBound
      height hheight hfreq reflected second firstHeight epsV hepsV0 hepsV hepsVCoeff hprefixSmall key hz1 hz2 firstIndex hf1
      hMask hfit hconstants hpad homega chi0 m hm0 hml hm2 hTsource hBetaHigh hfinite hgrid
      constant eps Bsrc control degree boxes hIH hconstant heps hchild rootBox hBsrc hfirst sourceFacts Psi
      hepsVpos hlarge hCs hCpay hCdirect hKt hKcol hC0 hC1 hKdirect hdelta hVrate hShellrate t0 u hsmall hHigh hOperator hOld hmu
    have hf0:=receipt.family.value_nonneg hZ0.le
    refine ⟨receipt,hraw.trans ?_⟩
    apply (mul_le_mul_of_nonneg_left hcontrolMono (add_nonneg
      (mul_nonneg hKall (Real.rpow_nonneg hZ0.le _)) (mul_nonneg hKreturn hf0))).trans
    apply mul_le_mul_of_nonneg_right _ hcontrolFull
    exact add_le_add (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hKlarge) (Real.rpow_nonneg hZ0.le _)) le_rfl
  · have hcell:=Cycle63.AffineLedger.originalCell_mem ⟨hwindow.slots_ge,hwindow.slots_le⟩
    have hamp0 : 0≤amp:=(Cycle63.AffineLedger.amp_pos (Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1)).le
    have hamp1 : amp≤1:=(Cycle63.AffineLedger.amp_bounds (Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1)).2.trans Cycle63.AffineLedger.amplifierCap_le_one
    have hamp4 : |amp|≤4:=by rw [abs_of_nonneg hamp0];linarith only [hamp1]
    have homega0 : 0≤frequencyLoss Z 32 (nativeMu/64)+nativeMu/8:=by
      have hh:=frequencyLoss_nonneg Z 32 (nativeMu/64) hZ (by norm_num) (div_nonneg nativeMu_pos.le (by norm_num))
      linarith only [hh,nativeMu_pos]
    have homega4 : |frequencyLoss Z 32 (nativeMu/64)+nativeMu/8|≤4:=by rw [abs_of_nonneg homega0];exact homega.trans (by norm_num)
    obtain ⟨receipt,hempty,hraw⟩:=actual_native_root_large_height_empty_return (hH:=hH) (C:=C) feeBudget hcardBudget g.τ g.τ_pos Cs Kcoarse hKcoarse
      coarse s p height hheight caps SpFull (Finset.mem_insert_self _ _) reflected second 1 1 squarefree_one
      1 amp (nativeMu/8) firstHeight outer target (by norm_num) (by norm_num) hamp0 hamp4 homega4
      (div_nonneg nativeMu_pos.le (by norm_num)) htarget key firstIndex hf1 hfirst Psi chi0
      (fun _=>internalQ C.Q C.etaSeed) (fun _=>m) t0 u g.e selector hsmall (Bsrc (0:Fin 4)) wholeBoxes
    have hcontrolLarge : (p.control SpFull)^2*physical*(1+|firstHeight|+height)^Dlarge*(1+|t0|)^Dlarge*(1+|u|)^Dlarge≤controlFull:=by
      have h1:=pow_le_pow_right₀ (by linarith only [hheight,abs_nonneg firstHeight] : (1:ℝ)≤1+|firstHeight|+height) (Nat.le_max_right Dall Dlarge)
      have h2:=pow_le_pow_right₀ (by linarith only [abs_nonneg t0] : (1:ℝ)≤1+|t0|) (Nat.le_max_right Dall Dlarge)
      have h3:=pow_le_pow_right₀ (by linarith only [abs_nonneg u] : (1:ℝ)≤1+|u|) (Nat.le_max_right Dall Dlarge)
      dsimp only [controlFull,Dfull]
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
    have hraw' : Z^outer*mainLowPhysicalCompleteCost (Fintype.card alpha) 1 (1/4) second ordinary coefficient t0 u selector≤
        Klarge*((p.control SpFull)^2*physical*(1+|firstHeight|+height)^Dlarge*(1+|t0|)^Dlarge*(1+|u|)^Dlarge)*Z^(outer+target):=by
      simpa only [Klarge,Dlarge,physical,coefficient,mass,hdelta] using hraw
    have hf0:=receipt.family.value_nonneg hZ0.le
    refine ⟨receipt,hraw'.trans ?_⟩
    calc
      _≤Klarge*controlFull*Z^(outer+target):=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcontrolLarge hKlarge) (Real.rpow_nonneg hZ0.le _)
      _=(Klarge*Z^(outer+target))*controlFull:=by ring
      _≤((Kall+Klarge)*Z^(outer+target)+Kreturn*receipt.family.value)*controlFull:=
        mul_le_mul_of_nonneg_right (le_trans
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hKall) (Real.rpow_nonneg hZ0.le _))
          (le_add_of_nonneg_right (mul_nonneg hKreturn hf0))) hcontrolFull

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualRootSelectedAllHeightRaw
