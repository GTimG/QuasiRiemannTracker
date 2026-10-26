/- Genuine finite-depth ROOT LOW before the moving initial source.
Copyright (c)2026 Zhongpai Gao. Native reductions by Hailey Collet. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeRecursiveRootHeight
import Candidate.Research.RecursiveAffine.NativeRootRegionalLowSource
import Candidate.Research.RecursiveAffine.RootLowQuantitativeMetadata
import Candidate.Research.RecursiveAffine.ActualInnerBackward
import Candidate.Research.RecursiveAffine.NativeSourceOldMesh
import Candidate.Research.RecursiveAffine.RootLiteralBudget
import Candidate.Research.RecursiveAffine.NativeCanonicalBufferThreshold

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153RootLowSchedule
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter Set HeckeFamily CanonicalQuadraticSieve
open CenteredMomentNaturalFixedRaySource CenteredMomentAllocatedRayDictionary
open CenteredMomentCommonRadialData CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentSecondHeightFamily
open Cycle63InitialSource Cycle63InitialMass Cycle63Moment LocalMoment Cycle153ActualSourceGates
open Cycle153Reachable Cycle153ActualColumn Cycle153ActualRootSourceGates Cycle153RegionalLow
open Cycle153SourceSchedule Cycle153SourceUniform Cycle153TerminalSchedule
open Cycle153RootInitialAssembly Cycle153RootStep Cycle153.RegionalSchedule
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}
noncomputable local instance recursiveRootLowLedger : Cycle63.AffineLedger:=Cycle153.Root.rootLedger
attribute [local irreducible] RegionalLowSelectedAt RootCanonicalSubsetAt

/-- The actual recursive ROOT source. The first INNER output is supplied
by the checked terminal-to-root finite induction. Canonical, coarse,
OLD, physical and count thresholds are chosen before the moving base,
profiles, ray data and original subset source. -/
theorem eventual_actual_recursive_root_low
    (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Icc 1 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
    (eta : Character)(heta : eta.modulus≤Ideal.span {fixedBadMask})
    (Q : Ideal O)(hQM : Q≤M)(hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
    (hQ72 : internalQ Q eta≤Ideal.span {(72:O)})
    (eps : ℝ)(heps : 0<eps)(mesh : ℝ)(hmesh : 0≤ mesh)(hmeshCap : mesh≤originalSlotMesh eps)
    (g : GeometryAffineLowSchedule)(hmu : g.μ=nativeMu)
    (hdelta : g.δ=nativeDriverRate (Fintype.card alpha))
    (hcutoff : 2*g.τ<actualRecursiveRootTau M H hH eta)
    (bPhi Cs : ℝ)(hCs : 1≤Cs) :
    ∀T : Finset alpha,∃Sp : Finset (ℕ×ℕ),∃degree : ℕ,∃K : ℝ,0≤K ∧
      ∀ᶠZ : ℝ in atTop,RecursiveRootLowAt (α:=T) M H hH W hW.continuous hWs hbeta hbetaHi g
        eta eta Q hQM hQ72 bPhi mesh (actualRecursiveRootTau M H hH eta) Cs Sp degree K Z hmesh :=by
  let B:=returnedNormCap 250000
  have hB : 0≤B:=actual_recursive_root_norm_nonneg
  let tau:=actualRecursiveRootTau M H hH eta
  have htau : 0<tau:=actualRecursiveRootTau_pos M H hH eta
  have htauOne : tau≤1:=actualRecursiveRootTau_le_one M H hH eta
  let r:=postDictionaryRate B (Fintype.card alpha)
  have hr : 0<r:=(postDictionaryRate_budgets hB (Fintype.card alpha)).1
  have children : ∀T : Finset alpha,∃Kclass constant : ℝ,1≤Kclass ∧0<constant ∧
      ∃(control : Finset (ℕ×ℕ))(degree : ℕ),∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀C : SourceContext (α:=T) M H,C.W=W→C.etaSeed=eta→C.Q=Q→C.globalBase=Z→
        C.gridDenominator=gridSize→C.slotMesh=localSlotMesh eps→C.Bnorm=B→C.Tz=Z^tau→
        Kclass≤C.highClassCap→∀N : ReachableNode C (0:Fin 4),
          Nonempty (NodeOutput hH N constant (oldLoss eps) 250000 control degree
            (fun _=>rootNativeDyadBox C.globalBase (Fintype.card T))) :=by
    intro T
    exact eventual_actual_first_inner_node_outputs (alpha:=T) hH W hW hWs hbeta hbetaHi
      eps tau heps htau htauOne eta Q hQM hQ0 hQt hQ72
  choose Kclass Kchild hclass hchild controlChild degreeChild hChildren using children
  obtain ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,Kcoarse,Sp,degreeLow,Klow,Kreturn,
      hpositive,hformula,hmetadata⟩:=actual_root_low_quantitative_metadata (alpha:=alpha)
    hH W hW hWs hbeta eta Q hQM hQ0 hQt hQ72 g Cs eps B hCs heps hB
    Kchild (fun T=>(hchild T).le) controlChild degreeChild
  have primitive : ∀T : Finset alpha,∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀(C : SourceContext (α:=T) M H)(s : Input T)(p : Profiles (1/4) (9/4))
        (caps : GeometryAffineLowSourceGates s p Cs C.globalBase),
        C.globalBase=Z→s.η=eta→s.b₁=(9/4:ℝ)→s.b₂=(9/4:ℝ)→
        C.slotMesh≤localSlotMesh eps→Fintype.card T≤Fintype.card alpha→
        (∀i,s.P i=C.globalBase^(C.originalWeight i))→
        Cycle63.AffineLedger.PlainWindow (length C.globalBase s.X₁) (length C.globalBase s.X₂)
          (∑i,C.originalWeight i)→∀(meshUsed : ℝ)(hmeshUsed : 0≤ meshUsed),meshUsed≤C.slotMesh→
          Nonempty (RootSelectedPrimitivePacket C s p Cs caps eps (Fintype.card alpha) meshUsed hmeshUsed) :=by
    intro T
    exact (eventually_actual_root_selected_primitives (alpha:=T) (M:=M) (H:=H)
      eta eps heps (Fintype.card alpha)).mono (fun _ hz=>⟨hz.1,fun C s p caps=>hz.2 C s p Cs caps⟩)
  have countThreshold : ∀T : Finset alpha,∀ᶠZ : ℝ in atTop,
      actualRootReturnThresholdAllBudgets M H hH eta B 1 hB (by norm_num)
        actual_recursive_root_history_budget T.card (Kclass T) ((hclass T).trans' (by norm_num))
        (Kreturn T) (hformula T).2.2.2.2.1≤Z:=by
    intro T
    exact eventually_ge_atTop _
  have hBuffer:=eventually_actual_canonical_buffer_high g.e g.τ (by linarith only [hcutoff,htauOne] : g.τ≤1)
  intro T
  refine ⟨Sp T,degreeLow T,Klow T,(hformula T).2.2.2.1,?_⟩
  filter_upwards [hmetadata,hChildren T,primitive T,countThreshold T,hBuffer] with Z hmeta hI hPrim hCount hBuffer
  intro hZ hT theta w sigma freq hsigma t height hw hwm hheight hfreq hcut Phi hsPhi hpPhi p X1 X2 hX1 hX2 hwindow
  intro state inp caps hm hfit hw' hwL hwr hwm' hheight' hfreq' hzslot haff
  let C:=sourceContext M H eps heps 250000 (Kclass T) (by norm_num)
    ((hclass T).trans' (by norm_num)) eta Q hQM hQ72 W hW hWs Z hZ (Z^tau)
    theta w sigma freq hw (fun i=>(hwm i).trans hmeshCap) hsigma
  have hCmesh : mesh≤C.slotMesh:=by
    change mesh≤localSlotMesh eps
    have hh:=(localSlotMesh_pos heps).le
    exact hmeshCap.trans (by unfold originalSlotMesh;linarith only [hh])
  have hscale : ∀i,inp.P i=C.globalBase^(C.originalWeight i):=fun i=>hm.scale i
  have hsEta : inp.η=C.etaSeed:=rfl
  have hb1 : inp.b₁=(9/4:ℝ):=rfl
  have hb2 : inp.b₂=(9/4:ℝ):=rfl
  have hwin : Cycle63.AffineLedger.PlainWindow (length C.globalBase inp.X₁)
      (length C.globalBase inp.X₂) (∑i,C.originalWeight i):=hwindow
  obtain ⟨prim⟩:=hPrim.2 C inp p caps rfl hsEta hb1 hb2 le_rfl
    (Fintype.card_le_of_injective (fun i : T=>i.val) Subtype.val_injective) hscale hwin mesh hmesh hCmesh
  obtain ⟨hKt,hCp,hKc,hCd,hC0,hC1,hKd,hKcoarse⟩:=hpositive T
  obtain ⟨hSp,hzero,hdegree,hKlow,hKret,hKformula,hReturn⟩:=hformula T
  obtain ⟨canonical,coarse,physical,old,scalar,allRows⟩:=hmeta.2 T
  unfold RootCanonicalSubsetAt at canonical
  have hsource:=canonical C rfl rfl rfl rfl hQ0 hQt
  have ih : ∀Nc : ReachableNode C (0:Fin 4),
      Nonempty (NodeOutput hH Nc (Kchild T) (oldLoss eps) 250000 (controlChild T) (degreeChild T)
        (fun _=>rootNativeDyadBox C.globalBase (Fintype.card T))) :=
    hI.2 C rfl rfl rfl rfl rfl rfl rfl rfl le_rfl
  have hwOld : ∀i,C.originalWeight i≤Cycle25.Energy.commonMesh 2 28 1 (oldLoss eps):=
    fun i=>((hwm i).trans hCmesh).trans (localSlotMesh_admits_old_source heps)
  have hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin:=by
    norm_num [C,sourceContext,gridSize,positionMargin]
  have hhigh : ∀buffer : BufferIndex g.e,
      (3+(3*buffer.1.val+2:ℕ)*C.globalBase^g.τ)^2≤(C.globalBase^(31:ℝ))^(3:ℝ):=by
    simpa only [C,sourceContext,Real.rpow_one] using hBuffer.2 1 (by norm_num)
  have hCoarse:=native_low_coarse_subset_receipt T recursiveRootLowLedger inferInstance
    (Fintype.card alpha) Cs (Kcoarse T) Z coarse
  have hCount' : actualRootReturnThresholdAllBudgets M H hH C.etaSeed C.Bnorm 1
      C.normCap_nonneg (by norm_num) actual_recursive_root_history_budget (Fintype.card T)
      C.highClassCap C.highClassCap_nonneg
      (actualRootAnalyticReturnCoefficient (alpha:=T) hH C.Bnorm C.normCap_nonneg (Fintype.card alpha)
        (Fintype.card T) g.e Cs (Cp T) (Kt T) (Kchild T) (Kc T) (Cd T) (C0 T) (C1 T) (Kd T)
        (max (max (dt T) (degreeChild T)) (dd T)))
      (actualRootAnalyticReturnCoefficient_nonneg (alpha:=T) hH C.Bnorm C.normCap_nonneg
        (Fintype.card alpha) (Fintype.card T) g.e Cs (Cp T) (Kt T) (Kchild T) (Kc T)
        (Cd T) (C0 T) (C1 T) (Kd T) (max (max (dt T) (degreeChild T)) (dd T))
        hCs hCp hCd hKt.le (hchild T).le hKc.le hC0.le hC1.le hKd.le)≤C.globalBase:=by
    simpa only [C,sourceContext,Fintype.card_coe,hReturn] using hCount
  have scalar' : actualSelectedScalarThreshold (Fintype.card T) r hr≤C.globalBase:=by
    simpa only [C,sourceContext,B,r,Fintype.card_coe] using scalar
  have physical' : actualRootPhysicalThreshold (alpha:=T) hH C.Bnorm C.normCap_nonneg
      (Fintype.card alpha) (Fintype.card T)≤C.globalBase:=by
    simpa only [C,sourceContext,B,Fintype.card_coe] using physical
  have old' : actualSelectedOldThreshold C.Bnorm C.normCap_nonneg (Fintype.card alpha)
      (Fintype.card T)≤C.globalBase:=by
    simpa only [C,sourceContext,B,Fintype.card_coe] using old
  have rows' : actualRootAllRowThreshold (Fintype.card T)≤C.globalBase:=by
    simpa only [C,sourceContext,Fintype.card_coe] using allRows
  have hlow:=@actualRootRegionalLowSource T inferInstance inferInstance M inferInstance H hH C hQ0 hQt
    hbeta hbetaHi g Cs eps r heps hr (dt T) (ct T) (Kt T) (Cp T) (Kc T) (dd T) (cd T)
    (Cd T) (C0 T) (C1 T) (Kd T) hsource inp p caps heta hsEta
    (Fintype.card alpha) (Fintype.card_le_of_injective (fun i : T=>i.val) Subtype.val_injective)
    hm hwOld hwL hwr hscale hwin mesh hmesh hwm prim height hheight hfreq hT hgrid
    (fun _=>Kchild T) (fun _=>oldLoss eps) (fun _=>controlChild T) (fun _=>degreeChild T)
    ih (hchild T).le (oldLoss_pos heps).le le_rfl scalar' hCs hCp hCd hKt.le hKc.le hC0.le hC1.le hKd.le
    hdelta hmu rfl hhigh physical' old' rows' (Kcoarse T) hKcoarse.le hCoarse hzslot haff
    1 (by norm_num) actual_recursive_root_history_budget (Real.rpow_nonneg (zero_le_one.trans hZ.le) _) le_rfl hCount'
  simpa only [hSp,hdegree,hKformula,rootLowPhysicalMultiplicity,C,sourceContext,B,rootSourceAmp,rootSourceCell,Fintype.card_coe] using hlow

end
end OAI.SevenEighths.Cycle153RootLowSchedule
#print axioms OAI.SevenEighths.Cycle153RootLowSchedule.eventual_actual_recursive_root_low
