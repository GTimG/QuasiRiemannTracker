/- Genuine small-height INNER physical LOW source, before final OLD payment.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerReceiptedShell
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
attribute [local irreducible] innerPhysicalAfter innerPhysicalConstant innerPhysicalThreshold mainLowPhysicalCompleteCost
variable {C : SourceContext (α:=alpha) M H}{j : Fin 4}

/-- Invoke the genuine residual/ray/buffer operator on actual selected
rows. Every local source is produced by the native completed-column
factory, with one SAME real returned forest. No energy or receipt bound
is an input. Primitive packets and fixed thresholds are independently
generated before the moving context by the native schedules. -/
def actualInnerSmallPhysical
    (hH : RayOrthogonality.globalUnits M≤H)(N : ReachableNode C j)(hj : j.val<3)
    (hQ0 : internalQ C.Q C.etaSeed≠0)(hQt : internalQ C.Q C.etaSeed≠⊤)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hBetaHigh : HeckeZeroSupremum.beta≤7/8)
    (g : GeometryAffineLowSchedule)(Cs epsNode : ℝ)(hepsNode : 0<epsNode)
    (rateBudget : ℕ)(hcard : Fintype.card N.slots≤rateBudget)
    (hRate : g.δ=nativeDriverRate rateBudget)
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
  show ∃receipt : NativeNodeForestReceipt hH N (Bsrc (nextInner j hj)) (fun _=>box),
    mainLowPhysicalCompleteCost (Fintype.card N.slots) 1 (1/4) second ordinary coefficient t0 u select≤
      (1/lowerFactor (Fintype.card N.slots) 1 (1/4))*
        ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(Fintype.card (BufferIndex g.e):ℝ)*
          (max 0 oldBase*(innerPhysicalConstant hH j r hr N.slots*Z^(r+3*(((Fintype.card N.slots:ℝ)+2)*3)*r))+
            2*(innerPhysicalConstant hH j r hr N.slots*sourceConstant)*receipt.family.value)) from by
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
    have hsource0 : 0 ≤ sourceConstant:=mul_nonneg
      (Real.rpow_nonneg (zero_lt_one.trans N.localBase_gt_one).le _) (by positivity)
    have hcoefficient : ∀q : rows,0≤coefficient q*(ordinary q).K*
        normalizer (ordinary q).C (ordinary q).D (ordinary q).inactive:=by
      intro q
      have hm0:=geometry_first_high_mass_nonneg reflected s N.state.puncture 1 Psi N.state.rowWidth Z
        (nativeMu/64) g.δ (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) key (firstIndex q.val.1).1.val
      have hv:=(volume_pos (child q.val.1)).le
      have hk:=(datum q).K_pos.le
      have hn:=(normalizer_pos (datum q).C (datum q).D (datum q).hC (datum q).inactive).le
      exact mul_nonneg (mul_nonneg (div_nonneg hm0 hv) hk) hn
    have hpool : ∀q i I,I∈(ordinary q).input.pools i→(I.absNorm:ℝ)≤Z^(3:ℝ):=by
      intro q
      exact native_second_datum_pool_cap reflected s N.state.puncture 1 Z N.state.rowWidth (nodeSourceAmp N)
        (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots) N.localBase_gt_one key
        (firstIndex q.val.1) caps.zero₁ caps.zero₂ q.val.2 _ caps.poolCap
    have hpositive : ∀q chi psi p z,z∈mainLowPaymentRows
        (mainLowSourceRows second (ordinary q) (fun _=>True)) (select q chi psi) p→1≤p.1.val:=by
      intro q chi psi p z hz
      exact (actual_main_low_canonical_payment_bins M H hH (datum q) (chi0 q) chi psi
        (internalQ C.Q C.etaSeed) C.fixed_small m hm0 hml hm2 Z 28 N.localBase_gt_one second
        (masks q).1 (masks q).2.1 C.etaSeed (inf_le_left.trans C.Q_le_M) inf_le_right
        g.e (Z^g.τ) g.e_pos hTsource hbeta hBetaHigh p z hz).2.2.2.1
    obtain ⟨exponent,sideLower,hbin⟩:=actual_first_bin_side_cancellation s N.state.puncture 1 (Z^N.state.rowWidth)
      Z (nativeMu/64) 3 (Real.logb Z (volume s))
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) N.localBase_gt_one
      squarefree_one caps.zero₁ caps.zero₂ caps.sourceCap key reflected
    let hside:=fun l=>(hbin.2 l).2.2.2 (3*nativeDriverRate rateBudget)
    have hgate:=primitive.gates N.state.puncture 1 squarefree_one reflected key r hr.le
      (postDictionaryRate_le_native C.Bnorm rateBudget) sideLower hside second firstHeight firstIndex hf1
    have hMrow : N.state.rowWidth≤2:=primitive.rowCap
    have hr1 : r≤1:=((postDictionaryRate_budgets C.normCap_nonneg rateBudget).2.1).trans (by norm_num [nativeMu,primitiveError])
    have hshift : r+3*(((Fintype.card N.slots:ℝ)+2)*3)*r≤1/1000000000000:=by
      have hr0:=hr.le
      have hh:=actual_old_post_cost_paid C.normCap_nonneg rateBudget (Fintype.card N.slots) hcard
      have hnum : nativeMu/32≤(1/1000000000000:ℝ):=by norm_num [nativeMu,primitiveError]
      nlinarith only [hh,hr0,hnum]
    have sourceFacts:=primitive.decorated N.state.puncture 1 squarefree_one reflected key firstHeight firstIndex hf1
      ((nodeInputPresentation hH N).unit (!reflected)) (fun l=>Units.isUnit _)
    have localSource : ∀chi psi (p : BufferIndex g.e),1≤p.1.val→
        ∀n∈selectedShells (sharedProjectors (fun q : rows=>(ordinary q).block.divisors.filter Squarefree)),
        ∃receipt : NativeNodeForestReceipt hH N (Bsrc (nextInner j hj)) (fun _=>box),
          (∀d z,(receipt.family.part d z).loss+(r+3*(((Fintype.card N.slots:ℝ)+2)*3)*r)≤terminalLossCap j) ∧
          (∑q,∑D∈shell (sharedProjectors (fun q : rows=>(ordinary q).block.divisors.filter Squarefree)) n,
            nativeResidualCost second ordinary
              (fun q=>coefficient q*(ordinary q).K*normalizer (ordinary q).C (ordinary q).D (ordinary q).inactive)
              (fun _=>if second then psi⁻¹ else chi)
              (fun q=>(ordinary q).input.t+2*Real.pi*(u-(if second then -t0 else t0)))
              (fun q=>mainLowPaymentRows (mainLowSourceRows second (ordinary q) (fun _=>True)) (select q chi psi) p)
              (fun _ _=>1) q D)≤(max 0 oldBase+sourceConstant*receipt.family.value)*(2*dyadicScale n)^(3*r):=by
      intro chi psi p hp n hn
      let projectors:=sharedProjectors (fun q : rows=>(ordinary q).block.divisors.filter Squarefree)
      have hprojectors : ∀q : rows,∀D∈(ordinary q).block.divisors.filter Squarefree,
          (D.absNorm:ℝ)≤Z^(((Fintype.card N.slots:ℝ)+2)*3):=by
        intro q D hD
        exact (second_datum_projector_cap (ordinary q) (Fintype.card N.slots) Z 3
          (by simpa only [Finset.card_univ,Fintype.card_coe] using (Finset.card_le_card (Finset.subset_univ (ordinary q).slots)))
          N.localBase_gt_one.le (by norm_num) (hpool q) D (Finset.mem_filter.mp hD).1).2
      have hT:=(shared_projector_shell_scale (fun q : rows=>(ordinary q).block.divisors.filter Squarefree)
        Z (((Fintype.card N.slots:ℝ)+2)*3) hprojectors n hn).1
      have hDs : ∀D∈shell projectors n,Squarefree D ∧ dyadicScale n≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*dyadicScale n:=by
        intro D hD
        have hd:=shared_projector_shell_gates (fun q : rows=>(ordinary q).block.divisors.filter Squarefree) n D hD
        exact ⟨hd.1,hd.2.2⟩
      have smallSource:=native_physical_small_height second firstHeight N.height t0 u (Z^g.τ)
        (Real.rpow_nonneg (zero_lt_one.trans N.localBase_gt_one).le _) hsmall
      obtain ⟨deleted,rawFamily,hdata,receipt,hloss,hbound⟩:=actualInnerReceiptedShell hH N hj hQ0 hQt hbeta
        g Cs epsNode r hepsNode hr degreeTerminal controlTerminal Kterminal Cpay Kcol degreeDirect controlDirect Cdirect C0 C1 Kdirect
        source caps hm primitive.sourceMesh sourceHeight p hp smallSource (hHigh p) reflected second N.state.rowWidth firstHeight
        hMrow rfl r hr.le hr1 primitive.prefixSmall key caps.zero₁ caps.zero₂ firstIndex hf1
        (shell projectors n) (dyadicScale n) masks primitive.fit primitive.constants primitive.slotWindow primitive.affine
        primitive.pad primitive.omega primitive.widthError hT hDs chi0 chi psi m hm0 hml hm2 hTsource hBetaHigh
        primitive.finite primitive.gridMargin rateBudget box (3*nativeDriverRate rateBudget-sideLower)
        (actualSideError Z rateBudget) (fun l=>hside (firstIndex l).1.val) primitive.gridFine
        (fun q=>(hgate q).1) (fun q=>(hgate q).2) primitive.fee constant eps Bsrc control degree hIH
        hconstant heps hchild rateBudget hcard hr hlarge Psi sideLower
        (by rw [hRate]) (fun l=>(hbin.2 (firstIndex l).1.val).2.2.1)
        hCs hCpay hCdirect hKt hKcol hC0 hC1 hKdirect hRate rfl rfl
        (by rw [hBsrc];norm_num) hinj (by simpa only [hBsrc] using sourceFacts)
        (r+3*(((Fintype.card N.slots:ℝ)+2)*3)*r) hshift
      refine ⟨receipt,hloss,?_⟩
      have hheight : ∀q : rows,(ordinary q).input.t+2*Real.pi*(u-(if second then -t0 else t0))=sourceHeight:=by
        intro q
        exact congrArg (fun t=>t+2*Real.pi*(u-(if second then -t0 else t0)))
          (native_second_datum_time reflected s N.state.puncture 1 Z N.state.rowWidth (nodeSourceAmp N)
            (nativeMu/64) (nativeMu/8) (9/4) firstHeight (Fintype.card N.slots) N.localBase_gt_one key
            (firstIndex q.val.1) caps.zero₁ caps.zero₂ q.val.2)
      have hheightEq : (fun q : rows=>(ordinary q).input.t+2*Real.pi*(u-(if second then -t0 else t0)))=
          (fun _ : rows=>sourceHeight):=funext hheight
      rw [hheightEq]
      exact hbound.trans (mul_le_mul_of_nonneg_right
        (add_le_add (le_max_right 0 oldBase) le_rfl) (Real.rpow_nonneg (by positivity) _))
    have after:=innerPhysicalAfter hH j r hr N.slots Z hphysical
    have hcardActual : ∀q : rows,Fintype.card (ordinary q).slots≤N.slots.card:=by
      intro q
      simpa only [Finset.card_univ,Fintype.card_coe] using (Finset.card_le_card (Finset.subset_univ (ordinary q).slots))
    have result:=after.2 N.ledger C N rfl (Bsrc (nextInner j hj)) (fun _=>box)
      1 (1/4) second ordinary coefficient t0 u g.e select hcardActual
      hpool hcoefficient (max 0 oldBase) sourceConstant (le_max_left 0 oldBase) hsource0
      (lowerFactor_pos _ _ _ (by norm_num) (by norm_num)) hpositive
      (by simpa only [Fintype.card_coe] using localSource)
    simpa only [Fintype.card_coe,innerPhysicalConstant] using result

end
end OAI.SevenEighths.Cycle153ActualColumn
#print axioms OAI.SevenEighths.Cycle153ActualColumn.actualInnerSmallPhysical
