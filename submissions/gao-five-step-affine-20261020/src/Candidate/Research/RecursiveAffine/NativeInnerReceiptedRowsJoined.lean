/- The actual canonical INNER column producer, with genuine arithmetic callbacks.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerSelectedRowsReceipted
import Candidate.Research.RecursiveAffine.NativeWholeSourceChoice
import Candidate.Research.RecursiveAffine.NativeSelectedRawColumnsSum
import Candidate.Research.RecursiveAffine.NativeSelectedScalarLabels

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
open CenteredMomentOriginalCommonHarmonic CenteredMomentFirstCanonicalFamily CenteredMomentSecondCanonicalScalar
open Cycle153ActualSourceGates CenteredMomentEnergyState CenteredMomentFirstAmplificationChoice
variable {alpha : Type} [Fintype alpha] [DecidableEq alpha]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}
variable (hH : RayOrthogonality.globalUnits M ≤ H)(N : ReachableNode C j)(hj : j.val<3)

/-- Choose all genuine receipted native columns once and sum their
literal reciprocal/source coefficients. The SAME whole family keeps
its actual empty-or-Chosen provenance together with its energy bound. -/
def actualInnerReceiptedRowsJoined
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
    (reflected second : Bool)(Mrow firstHeight : ℝ)(hMrow : Mrow≤2)(hMrowActual : Mrow=N.state.rowWidth)
    (epsV : ℝ)(hepsV0 : 0≤epsV)(hepsV : epsV≤1)
    (hprefixSmall : Real.logb N.localBase 4+2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+(nativeMu/64)/2≤1)
    (key : ℤ×(Fin 5→ℤ)){Label : Type}[Fintype Label]
    (hz1 : (N.input hH).W₁ 0=0)(hz2 : (N.input hH).W₂ 0=0)
    (firstIndex : Label→GeometryLowFirstIndex reflected (N.input hH) N.state.puncture 1
      (N.localBase^Mrow) N.localBase (nativeMu/64)
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key)
    (hf1 : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected (N.input hH) N.state.puncture 1 (N.localBase^Mrow) N.localBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val)
      N.state.puncture (N.input hH).ν (N.input hH).W (N.input hH).P≠0)
    (Ds : Finset (Ideal O))(T : ℝ)
    (hMask : ∀r : NativeLowRows reflected (N.input hH) N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex,
      let datum:=geometryLowSecondDatum reflected (N.input hH) N.state.puncture 1 N.localBase
        Mrow (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
        N.localBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2
      let E:=if second then datum.D else datum.C
      datum.R*E≠0 ∧ ((datum.R*E).absNorm:ℝ)≤N.localBase^(28:ℝ) ∧ Supported E ∧ datum.seed∣E)
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
    (chi0 : NativeLowRows reflected (N.input hH) N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex→RayFourExpansion.RayCharacter)
    (chi psi : RayFourExpansion.RayCharacter)(m : O)(hm0 : m≠0)
    (hml : goodLambda∣m)(hm2 : (2:O)∣m)
    (hTsource : 2<N.localBase^g.τ)(hBetaHigh : HeckeZeroSupremum.beta≤7/8)
    (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
      (2*(Fintype.card N.slots:ℝ)*Real.logb N.localBase (9/4)+
        Real.logb N.localBase (max 1 (N.input hH).b₁*max 1 (N.input hH).b₂)) ≤ 1/100000000000000000000)
    (hgrid : 500*(1/C.gridDenominator:ℝ)≤positionMargin)
    (rateBudget : ℕ)(box0 : Finset (Fin 4→ℤ))(massLoss sideError : ℝ)
    (hside : ∀l,massLoss+lowLabelSide reflected N.localBase (Real.logb N.localBase (volume (N.input hH)))
      (geometryFirstLabel (N.input hH) N.state.puncture 1 (N.localBase^Mrow) N.localBase (nativeMu/64)
        (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val) ≤ sideError)
    (hgridFine : (1/C.gridDenominator:ℝ)≤1/10000000000000000000000000000000000000000)
    (hsourcePaid : ∀r : NativeLowRows reflected (N.input hH) N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex, (actualSelectedPaidNode N reflected second (N.input hH) N.state.puncture 1 Mrow (nodeSourceAmp N)
        (nativeMu/64) (nativeMu/8) epsV (9/4) firstHeight (Fintype.card N.slots)
        key hz1 hz2 firstIndex massLoss sideError hside r).SourceGates)
    (hfinePaid : ∀r : NativeLowRows reflected (N.input hH) N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex, (actualSelectedPaidNode N reflected second (N.input hH) N.state.puncture 1 Mrow (nodeSourceAmp N)
        (nativeMu/64) (nativeMu/8) epsV (9/4) firstHeight (Fintype.card N.slots)
        key hz1 hz2 firstIndex massLoss sideError hside r).FineSourceGates)
    (hfee : ∀(R : Finset N.slots)(hsum : (∑i∈R,C.originalWeight i/N.unit)≤nodeDetectorDeletion N+C.slotMesh),
      (actualNodeGlobalFee (hH:=hH) N epsNode rateBudget R hsum).amount≤1/1000000000000000)
    (constant eps Bsrc : Fin 4→ℝ)(control : Fin 4→Finset (ℕ×ℕ))
    (degree : Fin 4→ℕ)
    (hIH : ∀Nc : ReachableNode C (nextInner j hj),Nonempty (NodeOutput hH Nc
      (constant (nextInner j hj)) (eps (nextInner j hj)) (Bsrc (nextInner j hj))
      (control (nextInner j hj)) (degree (nextInner j hj)) (fun _=>box0)))
    (hconstant : 0≤constant (nextInner j hj))(heps : 0≤eps (nextInner j hj))
    (hchild : eps (nextInner j hj)≤oldLoss epsNode)
    (budget : ℕ)(hcard : Fintype.card N.slots≤budget)(hepsVpos : 0<epsV)
    (hlarge : actualSelectedScalarThreshold budget epsV hepsVpos≤N.localBase)
    (Psi : 𝓢(ℝ,ℂ))(sideLower : ℝ)
    (hmassLoss : massLoss=3*g.δ-sideLower)
    (hmassSide : ∀l,sideLower≤geometryHighSide reflected (Real.logb N.localBase (volume (N.input hH)))
      (geometryExponents (N.input hH) N.state.puncture 1 (N.localBase^Mrow) N.localBase (nativeMu/64)
        (firstIndex l).1.val.1.val))
    (hCs : 1≤Cs)(hCpay : 1≤Cpay)(hCdirect : 1≤Cdirect)(hKt : 0≤Kterminal)
    (hKcol : 0≤Kcol)(hC0 : 0≤C0)(hC1 : 0≤C1)(hKdirect : 0≤Kdirect) :=
  letI : Cycle63.AffineLedger:=N.ledger
  let s:=N.input hH
  let Rows:=NativeLowRows reflected s N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
    (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key hz1 hz2 firstIndex
  let selected:=actualCanonicalSelectedFamily reflected second s N.state.puncture 1 N.localBase Mrow
    (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key hz1 hz2 firstIndex
  let ch:=fun r : Rows=>selected.chain reflected second s N.state.puncture 1 N.localBase Mrow
    (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key hz1 hz2 firstIndex r
  let gg:=fun r : Rows=>selected.geometry reflected second s N.state.puncture 1 N.localBase Mrow
    (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key hz1 hz2 firstIndex hf1 r
  let datum:=fun r : Rows=>geometryLowSecondDatum reflected s N.state.puncture 1 N.localBase Mrow
    (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
    N.localBase_gt_one key (firstIndex r.val.1) hz1 hz2 r.val.2
  let ordinaryRows:=fun r : Rows=>mainLowSourceRows second
    (ordinarySecondDatum (datum r) (chi0 r) (internalQ C.Q C.etaSeed) m) (fun _=>True)
  let selector:=fun r : Rows=>mainLowCanonicalSelector M H hH (datum r) (chi0 r) chi psi
    (internalQ C.Q C.etaSeed) C.fixed_small m hm0 hml hm2 N.localBase 28 N.localBase_gt_one
    second (hMask r).1 (hMask r).2.1 C.etaSeed (inf_le_left.trans C.Q_le_M) inf_le_right
    g.e (N.localBase^g.τ) g.e_pos hTsource hbeta hBetaHigh
  let zs:=fun r : Rows=>mainLowPaymentRows (ordinaryRows r) (selector r) buffer
  let first:=fun l=>geometryFirstLabel s N.state.puncture 1 (N.localBase^Mrow) N.localBase (nativeMu/64)
    (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val
  let label:=fun r : Rows=>actualSecondSupportedLabel _ _ _ _ _ _ _ r.val.2
    (actual_main_low_selected_inactive reflected s N.state.puncture 1 N.localBase Mrow (nodeSourceAmp N)
      (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex r)
  let nominal:=fun r : Rows=>secondNominal 1 N.localBase (nodeSourceAmp N)
    (frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8)
    (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
    (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
    (label r).1.1 (label r).1.2 (label r).2.val
  let allowance:=fun r : Rows=>lowAllowance N.localBase
    (if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)
    (if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)
    (label r).1.1 (label r).1.2 (if second then (label r).1.2 else (label r).1.1)
  let common:=nativeMu/8+(nativeMu/64)/2-Cycle63.AffineLedger.lowReserve+nativeMu/64+
    2*g.δ*31*(Fintype.card N.slots:ℝ)+Cycle63.AffineLedger.q/(6*Cycle63.Optimization.slotPrice)*
      (frequencyLoss N.localBase 32 (nativeMu/64)+nativeMu/8+nativeMu/8)+Cycle63.AffineLedger.q*C.slotMesh
  let mass:=fun l=>geometryFirstHighMass reflected s N.state.puncture 1 Psi Mrow N.localBase (nativeMu/64) g.δ
    (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex l).1.val
  let columnEnergy:=fun r : Rows=>∑D∈Ds,∑z∈zs r,(1:ℝ)*‖CenteredMomentCommonPairedSource.normalizedColumn
    (withHeight (ch r).first ((gg r).datum.τ (if second then psi⁻¹ else chi)) sourceHeight)
    (ch r).E₂ (hMask r).2.2.1 (ch r).R₂ (datum r).seed D z‖^2
  let Cg:=nativeColumnSourceConstant (Fintype.card N.slots) Cs Cpay Kterminal
    (constant (nextInner j hj)) Kcol Cdirect C0 C1 Kdirect
  let fixed:=N.profiles.control ((controlTerminal∪control (nextInner j hj))∪controlDirect)^2*
    (1+|sourceHeight|+N.height)^(max (max degreeTerminal (degree (nextInner j hj))) degreeDirect)*(2*T)^(3*epsShell)
  let physical:=geometryHighFactor reflected (geometrySupportConstant budget 1 (1/4) (1/4)) key
  let hRows:=actualInnerSelectedRowsReceipted hH N hj hQ0 hQt hbeta g Cs epsNode epsShell hepsNode hShell
    degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
    source caps hm hSourceMesh sourceHeight buffer hp hSmallHeight hHigh reflected second Mrow firstHeight
    hMrow hMrowActual epsV hepsV0 hepsV hprefixSmall key hz1 hz2 firstIndex hf1 Ds T hMask
    hfit hconstants hslots haff hpad homega hdelta hT hDs chi0 chi psi m hm0 hml hm2
    hTsource hBetaHigh hfinite hgrid rateBudget box0 massLoss sideError hside hgridFine
    hsourcePaid hfinePaid hfee constant eps Bsrc control degree hIH hconstant heps hchild
  let hSource:=choose_actual_source (Rows:=Rows) (A:=fun _=>Finset N.slots) hRows
  strengthen_actual_source hSource (fun deleted rawFamily hdata=>by
    have hCs0 : 0≤Cs:=zero_le_one.trans hCs
    have hCpay0 : 0≤Cpay:=zero_le_one.trans hCpay
    have hCdirect0 : 0≤Cdirect:=zero_le_one.trans hCdirect
    have hheight:=N.height_nonneg
    have hCg : 0≤Cg:=by
      have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
      dsimp only [Cg,nativeColumnSourceConstant]
      positivity
    have hfixed : 0≤fixed:=by dsimp only [fixed];positivity
    have hphysical : 0≤physical:=(geometry_high_factor_pos reflected
      (geometrySupportConstant budget 1 (1/4) (1/4)) key
      (geometrySupportConstant_pos budget 1 (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num))).le
    let hpay:=actual_selected_scalar_labels budget epsV hepsVpos N.localBase N.localBase_gt_one hlarge
      s N.profiles Cs caps hcard reflected second N.state.puncture 1 (by simp)
      Mrow (nodeSourceAmp N) firstHeight common (actualNodeLocalSourcePad (hH:=hH) N) epsShell hShell.le
      key firstIndex hf1
    exact actual_selected_raw_columns_sum reflected second s N.state.puncture 1 N.localBase Mrow
      (nodeSourceAmp N) (nativeMu/64) (nativeMu/8) epsV (9/4) firstHeight (Fintype.card N.slots)
      N.localBase_gt_one key hz1 hz2 firstIndex g.δ (oldLoss epsNode) common
      (actualNodeLocalSourcePad (hH:=hH) N) massLoss epsV 130 epsShell
      (2*g.δ*31*(Fintype.card N.slots:ℝ)) Cycle63.AffineLedger.q C.slotMesh
      Cg fixed physical hCg hfixed hphysical (fun i=>C.originalWeight i/N.unit) deleted _ rawFamily mass
      (fun r=>nominal r+nodeSourceAmp N+common+allowance r) allowance columnEnergy
      (fun r=>(datum r).hC) (fun r=>(datum r).hD)
      (fun r=>geometry_first_high_mass_nonneg reflected s N.state.puncture 1 Psi Mrow N.localBase
        (nativeMu/64) g.δ (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _)
        key (firstIndex r.val.1).1.val)
      (fun _=>CenteredMomentAmplificationChildInput.volume_pos _)
      (fun r=>(gg r).datum.K_pos.le) (fun _=>le_rfl) hpay
      (fun r=>by
        have hmass:=actual_geometry_low_uniform_mass reflected budget 1 (1/4) (by norm_num) (by norm_num)
          s N.state.puncture 1 Psi Mrow N.localBase (nativeMu/64) 3 g.δ sideLower N.localBase_gt_one
          (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) g.δ_pos.le hcard
          (by rw [caps.lower]) (by simp) hz1 hz2 caps.sourceCap caps.support₁ caps.support₂
          key (firstIndex r.val.1).1.val (hmassSide r.val.1)
        simpa only [hmassLoss] using hmass)
      (fun r=>(hdata r).2))

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualInnerReceiptedRowsJoined
