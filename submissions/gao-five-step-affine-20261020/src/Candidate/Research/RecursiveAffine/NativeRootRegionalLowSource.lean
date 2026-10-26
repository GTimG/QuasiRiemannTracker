/- The literal ROOT selected row returns the SAME physical source/output.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRootRegionalRawSource
import Candidate.Research.RecursiveAffine.NativeRootAnalyticReturnConstant
import Candidate.Research.RecursiveAffine.NativeRootReturnThresholdAllBudgets
import Candidate.Research.RecursiveAffine.NativeRootAllRowThreshold
import Candidate.Research.RecursiveAffine.NativeRootAllRowAt
import Candidate.Research.RecursiveAffine.NativeRootSelectedPrimitives
import Candidate.Research.RecursiveAffine.NativeRootParentPresentation
import Candidate.Research.RecursiveAffine.NativeRootRawLow
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
noncomputable local instance rootRegionalLowSourceLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
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

def actualRootRegionalLowSource
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
      Cycle63.AffineLedger.lam*(∑i,Real.logb C.globalBase (s.P i))≤Cycle63.AffineLedger.B)
    (countCap : ℝ)(hcountCap : 0<countCap)
    (hbudget : ∀d : SuffixDepth 4,(rootHistoryDepth d:ℝ)*250000≤C.Bnorm)
    (hTz0 : 0≤C.Tz)
    (hTz : C.Tz≤C.globalBase^(actualRootReturnTauAllBudgets M H hH C.etaSeed C.Bnorm countCap
      C.normCap_nonneg hcountCap hbudget))
    (hcountThreshold : actualRootReturnThresholdAllBudgets M H hH C.etaSeed C.Bnorm countCap
      C.normCap_nonneg hcountCap hbudget (Fintype.card alpha) C.highClassCap C.highClassCap_nonneg
      (actualRootAnalyticReturnCoefficient (alpha:=alpha) hH C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha) g.e
        Cs Cpay Kterminal (constant (0:Fin 4)) Kcol Cdirect C0 C1 Kdirect
        (max (max degreeTerminal (degree (0:Fin 4))) degreeDirect))
      (actualRootAnalyticReturnCoefficient_nonneg (alpha:=alpha) hH C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha) g.e
        Cs Cpay Kterminal (constant (0:Fin 4)) Kcol Cdirect C0 C1 Kdirect
        (max (max degreeTerminal (degree (0:Fin 4))) degreeDirect)
        hCs hCpay hCdirect hKt hconstant hKcol hC0 hC1 hKdirect)≤C.globalBase) :
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
    RegionalLowSelectedAt M H hH C.W hbeta g 2 (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs
      (fun _ _ _=>True) (fun _ _ _ _ _=>True) SpFull Dfull Kall C.etaSeed C.Q C.Q_le_M C.fixed_small
      C.globalBase (C.globalBase^(rootSourceAmp C.originalWeight-3*g.δ)) C.globalBase_gt_one s p caps C.theta C.originalWeight C.sigma C.frequency hm
      1 1 0 1 one_ne_zero squarefree_one (by norm_num) (by simp) (by norm_num) le_rfl
      (by rw [hmu];linarith only [prim.fit]) trivial height mesh C.originalWeight_nonneg hwL hwr hmesh hwm C.sigma_fixed
      hheight hfreq hTsource hBetaHigh hzslot haff :=by
  intro Dall Dlarge Dfull SpFull Cg Cu Kold Kbox fixedOperator Kall Kreturn
  have hRaw:=@actualRootRegionalRawSource alpha inferInstance inferInstance M inferInstance H hH C hQ0 hQt hbeta hBetaHigh g Cs epsNode epsShell hepsNode hShell
    degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
    source s p caps heta hsEta feeBudget hcardBudget hm hwLsmall hwL hwr hscale hwindow mesh hmesh hwm prim
    height hheight hfreq hTsource hgrid constant eps control degree hIH hconstant heps hchild hlarge
    hCs hCpay hCdirect hKt hKcol hC0 hC1 hKdirect hdelta hmu hShellrate hHigh hOperator hOld hAllRows
    Kcoarse hKcoarse coarse hzslot haff
  have hreturn:=actualRootAnalyticReturnCoefficient_nonneg (alpha:=alpha) hH C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha) g.e
    Cs Cpay Kterminal (constant (0:Fin 4)) Kcol Cdirect C0 C1 Kdirect Dall
    hCs hCpay hCdirect hKt hconstant hKcol hC0 hC1 hKdirect
  have after:=actualRootReturnAfterAllBudgets M H hH C.etaSeed C.Bnorm countCap C.normCap_nonneg hcountCap hbudget (Fintype.card alpha)
    C.highClassCap C.highClassCap_nonneg
    (actualRootAnalyticReturnCoefficient (alpha:=alpha) hH C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha) g.e
      Cs Cpay Kterminal (constant (0:Fin 4)) Kcol Cdirect C0 C1 Kdirect Dall)
    hreturn C.globalBase hcountThreshold
  have hcount:=after.2 C rfl rfl rfl rfl hTz0 hTz
  change ∀receipt : NativeRootForestReceipt (hH:=hH) (C:=C) 250000
    (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha)),Kreturn*receipt.family.value≤C.globalBase at hcount
  have hCg : 0≤Cg:=actual_root_column_constant_nonneg _ _ _ _ _ _ _ _ _ _ hCs hCpay hCdirect hKt hconstant hKcol hC0 hC1 hKdirect
  have hCu : 0≤Cu:=(actualRootPhysicalConstant_pos (alpha:=alpha) hH C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha)).le
  have hKold : 0≤Kold:=(actualSelectedOldConstant_pos C.Bnorm C.normCap_nonneg feeBudget).le
  have hKbox : 0≤Kbox:=(actualSelectedOldBoxConstant_pos C.Bnorm C.normCap_nonneg feeBudget (Fintype.card alpha)).le
  have hoperator : 0≤fixedOperator:=by
    dsimp only [fixedOperator]
    have hh:=(lowerFactor_pos (Fintype.card alpha) 1 (1/4) (by norm_num) (by norm_num)).le
    positivity
  have hKall : 0≤Kall:=by dsimp only [Kall];positivity
  have hdriver : 0≤oldLoss epsNode:=(oldLoss_pos hepsNode).le
  exact @root_low_selected_of_actual_raw_source alpha inferInstance inferInstance M inferInstance H hH rootRegionalLowSourceLedger C.W hbeta g 2 (Cycle25.Energy.commonMesh 2 28 1 (g.μ/8)) Cs
    (fun _ _ _=>True) (fun _ _ _ _ _=>True) SpFull Dfull Kall C.etaSeed C.Q C.Q_le_M C.fixed_small
    C.globalBase (rootSourceAmp C.originalWeight) (oldLoss epsNode) Kreturn 250000 (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha))
    C C.globalBase_gt_one s p caps C.theta C.originalWeight C.sigma C.frequency hm
    1 1 0 1 one_ne_zero squarefree_one (by norm_num) (by simp) (by norm_num) le_rfl
    (by rw [hmu];linarith only [prim.fit]) trivial height mesh C.originalWeight_nonneg hwL hwr hmesh hwm C.sigma_fixed
    hheight hfreq hTsource hBetaHigh hzslot haff rfl hdriver hKall hcount hRaw

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualRootRegionalLowSource
