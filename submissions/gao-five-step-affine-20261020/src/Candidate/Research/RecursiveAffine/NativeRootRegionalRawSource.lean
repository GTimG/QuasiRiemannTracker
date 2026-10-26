/- The literal ROOT selected row returns the SAME physical source/output.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootSelectedAllHeightRaw
import Candidate.Research.RecursiveAffine.NativeRootAllRowThreshold
import Candidate.Research.RecursiveAffine.NativeRootAllRowAt
import Candidate.Research.RecursiveAffine.NativeRootSelectedPrimitives
import Candidate.Research.RecursiveAffine.NativeRootParentPresentation
import Candidate.Research.RecursiveAffine.NativeRootRawLow
import Candidate.Research.RecursiveAffine.NativeRootRawAtAmp
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
noncomputable local instance rootRegionalRawSourceLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
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

private def root_receipt_rebox {Bsrc : ℝ}{boxes boxes' : ℕ→Finset (Fin 4→ℤ)}
    (F : NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes)(heq : boxes=boxes') :
    NativeRootForestReceipt (hH:=hH) (C:=C) Bsrc boxes' where
  family:=F.family
  chronology:=by rw [←heq];exact F.chronology
  path:=F.path
  terminalLoss:=F.terminalLoss
  terminalSource:=F.terminalSource
  classCap:=F.classCap

/-- The actual all-height native ROOT LOW source. All per-row licences
come from genuine pre-source arithmetic packets; the only recursion is
availability of the completed first-inner source on the surviving slots. -/
def actualRootRegionalRawSource
    (hQ0 : internalQ C.Q C.etaSeed≠0)(hQt : internalQ C.Q C.etaSeed≠⊤)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hBetaHigh : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule)(Cs epsNode epsShell : ℝ)(hepsNode : 0<epsNode)(hShell : 0<epsShell)
    (degreeTerminal : ℕ)(controlTerminal : Finset (ℕ×ℕ))(Kterminal Cpay Kcol : ℝ)
    (degreeDirect : ℕ)(controlDirect : Finset (ℕ×ℕ))(Cdirect C0 C1 Kdirect : ℝ)
    (source : RootCanonicalNativeSpec hH C hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
      degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect)
    (s : Input alpha)(p : Profiles (1/4) (9/4))
    (caps : GeometryAffineLowSourceGates s p Cs C.globalBase)
    (heta : C.etaSeed.modulus≤Ideal.span {fixedBadMask})(hsEta : s.η=C.etaSeed)
    (feeBudget : ℕ)(hcardBudget : Fintype.card alpha≤feeBudget)
    (hm : Matches M H hH s C.etaSeed C.theta C.originalWeight C.sigma C.frequency C.W 2 C.globalBase)
    (hwLsmall : ∀i,C.originalWeight i≤Cycle25.Energy.commonMesh 2 28 1 (oldLoss epsNode))
    (hwL : ∀i,C.originalWeight i≤Cycle25.Energy.commonMesh 2 28 1 (g.μ/8))
    (hwr : ∀i,C.originalWeight i/31≤1)
    (hscale : ∀i,s.P i=C.globalBase^(C.originalWeight i))
    (hwindow : Cycle63.AffineLedger.PlainWindow
      (length C.globalBase s.X₁) (length C.globalBase s.X₂) (∑i,C.originalWeight i))
    (mesh : ℝ)(hmesh : 0≤ mesh)(hwm : ∀i,C.originalWeight i≤ mesh)
    (prim : RootSelectedPrimitivePacket C s p Cs caps epsNode feeBudget mesh hmesh)
    (height : ℝ)(hheight : 0≤height)(hfreq : ∀i,|C.frequency i|≤height)
    (hTsource : 2<C.globalBase^g.τ)
    (hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin)
    (constant eps : Fin 4→ℝ)(control : Fin 4→Finset (ℕ×ℕ))(degree : Fin 4→ℕ)
    (hIH : ∀Nc : ReachableNode C (0:Fin 4),Nonempty (NodeOutput hH Nc
      (constant (0:Fin 4)) (eps (0:Fin 4)) 250000 (control (0:Fin 4)) (degree (0:Fin 4))
      (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha))))
    (hconstant : 0≤constant (0:Fin 4))(heps : 0≤eps (0:Fin 4))
    (hchild : eps (0:Fin 4)≤oldLoss epsNode)
    (hlarge : actualSelectedScalarThreshold (Fintype.card alpha) epsShell hShell≤C.globalBase)
    (hCs : 1≤Cs)(hCpay : 1≤Cpay)(hCdirect : 1≤Cdirect)(hKt : 0≤Kterminal)
    (hKcol : 0≤Kcol)(hC0 : 0≤C0)(hC1 : 0≤C1)(hKdirect : 0≤Kdirect)
    (hdelta : g.δ=nativeDriverRate feeBudget)(hmu : g.μ=nativeMu)
    (hShellrate : epsShell=postDictionaryRate C.Bnorm feeBudget)
    (hHigh : ∀buffer : BufferIndex g.e,
      (3+(3*buffer.1.val+2:ℕ)*C.globalBase^g.τ)^2≤(C.globalBase^(31:ℝ))^(3:ℝ))
    (hOperator : actualRootPhysicalThreshold (alpha:=alpha) hH C.Bnorm C.normCap_nonneg feeBudget
      (Fintype.card alpha)≤C.globalBase)
    (hOld : actualSelectedOldThreshold C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha)≤C.globalBase)
    (hAllRows : actualRootAllRowThreshold (Fintype.card alpha)≤C.globalBase)
    (Kcoarse : ℝ)(hKcoarse : 0≤Kcoarse)
    (coarse : MainLowCompleteCoarseSpec (α:=alpha) (Fintype.card alpha) 4 Cs (9/4) (9/4)
      (2*Real.log (9/4)) 4 1 (1/4) (nativeDriverRate feeBudget) (nativeMu/64) 3
      (nativeLowCoarseExponent (Fintype.card alpha) feeBudget) Kcoarse C.globalBase)
    (hzslot : Cycle63.AffineLedger.slotFloor≤∑i,Real.logb C.globalBase (s.P i) ∧
      (∑i,Real.logb C.globalBase (s.P i))≤Cycle63.AffineLedger.slotTop)
    (haff : length C.globalBase s.X₁+length C.globalBase s.X₂+
      Cycle63.AffineLedger.lam*(∑i,Real.logb C.globalBase (s.P i))≤Cycle63.AffineLedger.B) :
    let Dall:=max (max degreeTerminal (degree (0:Fin 4))) degreeDirect
    let Dlarge:=nativeLowLargeHeightDegree feeBudget g.τ g.τ_pos
    let Dfull:=max Dall Dlarge
    let SpFull:=insert (0,0) (controlTerminal∪control (0:Fin 4)∪controlDirect)
    let Cg:=nativeColumnSourceConstant (Fintype.card alpha) Cs Cpay Kterminal (constant (0:Fin 4)) Kcol Cdirect C0 C1 Kdirect
    let Cu:=actualRootPhysicalConstant (alpha:=alpha) hH C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha)
    let Kold:=actualSelectedOldConstant C.Bnorm C.normCap_nonneg feeBudget
    let Kbox:=actualSelectedOldBoxConstant C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha)
    let fixedOperator:=(1/lowerFactor (Fintype.card alpha) 1 (1/4))*
      ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(Fintype.card (BufferIndex g.e):ℝ))
    let Kall:=fixedOperator*Cu*Kold*Cg*Kbox*(2+4*Real.pi)^Dall+(2+4*Real.pi)^Dlarge*Kcoarse
    let Kreturn:=fixedOperator*2*Cu*Cg*(2+4*Real.pi)^Dall
    RegionalRawLowSelectedAt M H hH C.W hbeta g 2 (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs
      (fun _ _ _=>True) (fun _ _ _ _ _=>True) SpFull Dfull Kall C.etaSeed C.Q C.Q_le_M C.fixed_small
      C.globalBase (1+3*g.δ-rootSourceAmp C.originalWeight+oldLoss epsNode) Kreturn
      (NativeRootForestReceipt (hH:=hH) (C:=C) 250000 (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha)))
      (fun receipt=>receipt.family.value) C.globalBase_gt_one s p caps C.theta C.originalWeight C.sigma C.frequency hm
      1 1 0 1 one_ne_zero squarefree_one (by norm_num) (by simp) (by norm_num) le_rfl
      (by rw [hmu];linarith only [prim.fit]) trivial height mesh C.originalWeight_nonneg hwL hwr hmesh hwm C.sigma_fixed
      hheight hfreq hTsource hBetaHigh hzslot haff :=by
  rcases g with ⟨mu,delta,tau,e,kappa,vslot,hmuPos,hmuCap,hdeltaPos,hdeltaCap,htau,he,heCap,hkappa,hvslot,hBudget,hCutoff⟩
  dsimp only at hmu
  subst mu
  let g : GeometryAffineLowSchedule:=⟨nativeMu,delta,tau,e,kappa,vslot,hmuPos,hmuCap,hdeltaPos,hdeltaCap,htau,he,heCap,hkappa,hvslot,hBudget,hCutoff⟩
  have hmu : g.μ=nativeMu:=rfl
  intro Dall Dlarge Dfull SpFull Cg Cu Kold Kbox fixedOperator Kall Kreturn
  have hZ:=C.globalBase_gt_one
  have hZ0:=zero_lt_one.trans hZ
  have hlogsum : (∑i,Real.logb C.globalBase (s.P i))=∑i,C.originalWeight i:=by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hscale i,Real.logb_rpow hZ0 (ne_of_gt hZ)]
  have hampAlias : (1:ℝ)*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑i,Real.logb C.globalBase (s.P i))/(1:ℝ))))=rootSourceAmp C.originalWeight:=by
    rw [hlogsum,div_one,one_mul]
    rfl
  let F0:=actualRootParentRow C.etaSeed heta
  have hparent : ParentPresentation s.η F0 1:=actual_root_parent_presentation C.etaSeed heta s hsEta
  have hr0 : 0≤epsShell:=hShell.le
  have hr1 : epsShell≤1:=by rw [hShellrate];exact (postDictionaryRate_budgets C.normCap_nonneg feeBudget).2.1.trans (by norm_num [nativeMu,primitiveError])
  have hrDriver : epsShell≤nativeDriverRate feeBudget:=by rw [hShellrate];exact postDictionaryRate_le_native _ _
  unfold RegionalRawLowSelectedAt
  intro Label inst reflected second bin firstHeight firstIndex
  change RootRawAtAmp M H hH hbeta g SpFull Dfull Kall C.etaSeed C.Q C.Q_le_M C.fixed_small
    C.globalBase (1+3*g.δ-rootSourceAmp C.originalWeight+oldLoss epsNode) Kreturn
    (NativeRootForestReceipt (hH:=hH) (C:=C) 250000 (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha)))
    (fun receipt=>receipt.family.value) C.globalBase_gt_one s p caps.zero₁ caps.zero₂ height mesh
    hTsource hBetaHigh reflected second bin firstHeight firstIndex _
  rw [hampAlias]
  unfold RootRawAtAmp
  intro first omega hamp0 hamp homega htarget hf1 hinj hfirstproj rows datum chi0 m hm0 hml hm2 Psi t0 u
  have hvolume3 : volume s≤C.globalBase^(3:ℝ):=caps.volume.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num))
  have hmask:=actualRootAllRowMasksAt (Fintype.card alpha) C.globalBase hAllRows hZ reflected second s p Cs caps
    le_rfl (rootSourceAmp C.originalWeight) firstHeight bin firstIndex hf1
  let hP:=fun r=>(hmask r).1
  let hPN:=fun r=>(hmask r).2.2.1
  let hPNc:=fun r=>(hmask r).2.1
  refine ⟨hP,hPN,hPNc,?_⟩
  intro st left u0 unit Tz hleft hu0 hunits hpresented canonical firstMass childSrc
  let hMask:=fun r=>And.intro (hmask r).1 (And.intro (hmask r).2.2.1
    (And.intro (hmask r).2.2.2.2.2.1 (hmask r).2.2.2.2.2.2))
  have hcell:=Cycle63.AffineLedger.originalCell_mem ⟨hwindow.slots_ge,hwindow.slots_le⟩
  have hamp1 : rootSourceAmp C.originalWeight≤1:=(Cycle63.AffineLedger.amp_bounds
    (Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1)).2.trans Cycle63.AffineLedger.amplifierCap_le_one
  have sourceFacts:=actualRootAllRowFactsAt (Fintype.card alpha) C.globalBase hAllRows hZ reflected s p Cs caps
    le_rfl (rootSourceAmp C.originalWeight) firstHeight bin firstIndex hf1 hamp0 hamp1
    (fun l=>(firstDictionaryUnit (!reflected) C.etaSeed 1 F0 1 l:O)) (fun l=>Units.isUnit _)
  have ret:=actualRootSelectedAllHeightRaw hH C hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
    degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
    source s p F0 1 hparent caps feeBudget hcardBudget prim.gates hm hwLsmall hwr hscale hwindow mesh hmesh hwm prim.fee
    height hheight hfreq reflected second firstHeight epsShell hr0 hr1 hrDriver prim.prefixSmall bin caps.zero₁ caps.zero₂ firstIndex hf1
    hMask prim.fit prim.constants prim.pad prim.omega chi0 m hm0 hml hm2 hTsource hBetaHigh prim.finite hgrid
    constant eps (fun _=>250000) control degree (fun _ _=>rootNativeDyadBox C.globalBase (Fintype.card alpha)) hIH
    hconstant heps hchild (rootNativeDyadBox C.globalBase (Fintype.card alpha)) (by norm_num) hinj sourceFacts Psi
    hShell hlarge hCs hCpay hCdirect hKt hKcol hC0 hC1 hKdirect hdelta hShellrate hShellrate t0 u hHigh hOperator hOld hmu
    Kcoarse hKcoarse coarse htarget
  obtain ⟨receipt,hbound⟩:=ret
  let receipt':=root_receipt_rebox hH C receipt (boxes':=fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha))
    (by funext k;cases k<;>rfl)
  refine ⟨receipt',1+3*g.δ-rootSourceAmp C.originalWeight+oldLoss epsNode+
    geometryAffineLowTarget g (Fintype.card alpha) (rootSourceAmp C.originalWeight)
      (frequencyLoss C.globalBase 32 (nativeMu/64)+nativeMu/8) mesh,?_,?_⟩
  · simp only [g,omega,rootSourceAmp,rootSourceCell,sub_self,add_zero,le_refl]
  · apply hbound.trans_eq
    dsimp only [Dall,Dlarge,Dfull,SpFull,Cg,Cu,Kold,Kbox,fixedOperator,Kall,Kreturn,receipt',root_receipt_rebox,g,omega]
    ring

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualRootRegionalRawSource
