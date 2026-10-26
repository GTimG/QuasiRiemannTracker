/- Finite backward induction from the actual terminal source.
Copyright (c)2026 Zhongpai Gao. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.NativeInnerAllHeight
import Candidate.Research.RecursiveAffine.NativeInnerMetadataAtNode
import Candidate.Research.RecursiveAffine.InnerNativeUniform
import Candidate.Research.RecursiveAffine.TerminalNodeMovingBoxes
import Candidate.Research.RecursiveAffine.NativeCanonicalBufferThreshold

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 6000
set_option backward.isDefEq.respectTransparency true
namespace OAI.SevenEighths.Cycle153TerminalSchedule
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap HeckeNotation
open Filter HeckeFamily CenteredMomentNaturalFixedRaySource Cycle63InitialMass
open CenteredMomentSecondHeightFamily
open CenteredMomentEnergyBands
open LocalMoment
open Cycle153Reachable Cycle153RegionalLow Cycle153RegionalState
open Cycle153SourceSchedule Cycle153SourceUniform Cycle153InnerLowSchedule
open Cycle153ActualSourceGates Cycle153ActualColumn Cycle153.RegionalSchedule
variable {alpha : Type}[Fintype alpha][DecidableEq alpha]
variable {M : Ideal O}[NeZero M]{H : Subgroup (O⧸M)ˣ}

/-- A genuine recursive step. The only induction hypothesis concerns the
strictly deeper stage. The present stage's LOW source is built from the
native canonical, coarse, physical and OLD sources at the same node.
All constants precede the base and every moving source. -/
theorem eventual_actual_inner_stage_from_deeper
    (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
    (eps tau : ℝ)(heps : 0<eps)(htau : 0<tau)(htauOne : tau≤1)
    (eta : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
    (hQ72 : internalQ Q eta≤Ideal.span {(72:O)})(j : Fin 4)(hj : j.val<3)
    (KchildClass Kchild : ℝ)(hKchild : 0≤Kchild)
    (controlChild : Finset (ℕ×ℕ))(degreeChild : ℕ)
    (hChild : ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀C : SourceContext (α:=alpha) M H,C.W=W→C.etaSeed=eta→C.Q=Q→
        C.globalBase=Z→C.gridDenominator=gridSize→C.slotMesh=localSlotMesh eps→
        C.Bnorm=returnedNormCap 250000→C.Tz=Z^tau→KchildClass≤C.highClassCap→
      ∀Nc : ReachableNode C (nextInner j hj),
        Nonempty (NodeOutput hH Nc Kchild (oldLoss eps) 250000 controlChild degreeChild
          (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha)))) :
    ∃Kclass constant : ℝ,1≤Kclass ∧ 0<constant ∧
    ∃(control : Finset (ℕ×ℕ))(degree : ℕ),∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀C : SourceContext (α:=alpha) M H,C.W=W→C.etaSeed=eta→C.Q=Q→
        C.globalBase=Z→C.gridDenominator=gridSize→C.slotMesh=localSlotMesh eps→
        C.Bnorm=returnedNormCap 250000→C.Tz=Z^tau→Kclass≤C.highClassCap→
      ∀N : ReachableNode C j,
        Nonempty (NodeOutput hH N constant (oldLoss eps) 250000 control degree
          (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha))) :=by
  let B:=returnedNormCap 250000
  have hB : 0≤B :=le_trans (by norm_num) (returnedNormCap_large (by norm_num : (0:ℝ)≤250000))
  letI : Fintype (InnerGridIndex j):=Fintype.ofFinite _
  let S : ∀i : InnerGridIndex j,InnerNativeSchedule (alpha:=alpha) hH W hW hWs hbeta hbetaHi
      eps tau B heps eta Q hQM hQ72 j i :=fun i=>
    Classical.choice (inner_native_schedule_exists hH W hW hWs hbeta hbetaHi eps tau B heps htau
      eta Q hQM hQ0 hQt hQ72 j i)
  obtain ⟨dt,dd,ct,cd,Kt,Cp,Kc,Cd,C0,C1,Kd,Kcoarse,Sp,degreeLow,Klow,Kreturn,
      hpositive,hformula,hKreturn,hmetadata⟩:=
    actual_inner_low_grid_metadata hH W hW hWs hbeta hbetaHi eps tau B heps hB eta Q
      hQM hQ0 hQt hQ72 j hj S Kchild hKchild controlChild degreeChild
  have hKlow : ∀i T,0≤Klow i T:=fun i T=>(hformula i T).2.2.2.1
  obtain ⟨Kown,constant,hKown,hconstant,control,degree,hNative⟩:=
    eventual_actual_inner_node_outputs_from_raw_all_boxes hH W hW hWs hbeta hbetaHi
      eps tau B 250000 heps htau (by norm_num) rfl eta Q hQM hQ72 j S
      Sp degreeLow Klow hKlow Kreturn hKreturn
  have hPrimitive:=eventually_actual_inner_selected_primitives (alpha:=alpha) hH eta eps heps (Fintype.card alpha)
  have hScalar:=eventual_actual_inner_scalar_thresholds B hB (Fintype.card alpha)
  have hBuffers : ∀ᶠZ : ℝ in atTop,∀i : InnerGridIndex j,
      1<Z ∧∀U : ℝ,(1/50:ℝ)≤U→∀buffer : BufferIndex (S i).g.e,
        (3+(3*buffer.1.val+2:ℕ)*(Z^U)^(S i).g.τ)^2≤((Z^U)^(31:ℝ))^(3:ℝ) :=by
    apply Filter.eventually_all.mpr
    intro i
    apply eventually_actual_canonical_buffer_high
    have hc:=(S i).cutoff
    linarith only [hc,htauOne]
  refine ⟨max KchildClass Kown,constant,hKown.trans (le_max_right _ _),
    hconstant,control,degree,?_⟩
  filter_upwards [hChild,hmetadata,hNative,hPrimitive,hScalar,hBuffers] with Z hc hm hn hp hs hb
  refine ⟨hn.1,?_⟩
  intro C hCW hCeta hCQ hbase hgrid hmesh hnorm hheight hclass N
  have child : ∀Nc : ReachableNode C (nextInner j hj),
      Nonempty (NodeOutput hH Nc Kchild (oldLoss eps) 250000 controlChild degreeChild
        (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha))) :=
    hc.2 C hCW hCeta hCQ hbase hgrid hmesh hnorm hheight ((le_max_left _ _).trans hclass)
  apply hn.2 (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha)) C hCW hCeta hCQ hbase
    hgrid hmesh hnorm hheight ((le_max_right _ _).trans hclass) N
  intro i hledger hT
  letI : Cycle63.AffineLedger:=N.ledger
  have hQ0N : internalQ C.Q C.etaSeed≠0:=by simpa only [hCQ,hCeta] using hQ0
  have hQtN : internalQ C.Q C.etaSeed≠⊤:=by simpa only [hCQ,hCeta] using hQt
  obtain ⟨canonical,coarse,physical,old⟩:=actual_inner_low_metadata_at_node
    hH W hW hWs hbeta hbetaHi eps tau B heps hB eta Q hQM hQ0 hQt hQ72 j hj i (S i)
    (dt i) (dd i) (ct i) (cd i) (Kt i) (Cp i) (Kc i) (Cd i) (C0 i) (C1 i) (Kd i) (Kcoarse i)
    Z (hm.2 i) C hCW hCeta hCQ hbase N hledger hQ0N hQtN
  have scalar:=hs.2 N.unit N.unit_floor
  have buffer:=(hb i).2 N.unit N.unit_floor
  rw [←hbase,←N.localBase_eq] at scalar buffer
  have primitive : ∀caps : GeometryAffineLowSourceGates (N.input hH) N.profiles (S i).Cs N.localBase,
      Nonempty (InnerSelectedPrimitivePacket hH C j N (S i).Cs caps eps (Fintype.card alpha)) :=by
    intro caps
    exact hp.2 C j N (S i).Cs caps hbase hj hgrid (le_of_eq hmesh)
      (Fintype.card_le_of_injective (fun k : N.slots=>k.val) Subtype.val_injective)
  obtain ⟨hKt,hCp,hKc,hCd,hC0,hC1,hKd,hKcoarse⟩:=hpositive i N.slots
  obtain ⟨hSp,hzero,hdegree,hKlow,hKformula,hReturn⟩:=hformula i N.slots
  have raw:=actual_native_node_raw_low_at hH N hj hQ0N hQtN hbeta hbetaHi (S i).g (S i).Cs eps heps
    (S i).mu (S i).delta (dt i N.slots) (dd i N.slots) (ct i N.slots) (cd i N.slots)
    (Kt i N.slots) (Cp i N.slots) (Kc i N.slots) (Cd i N.slots) (C0 i N.slots) (C1 i N.slots)
    (Kd i N.slots) (Kcoarse i N.slots) Kchild hKchild controlChild degreeChild
    (by simpa only [hnorm] using canonical) coarse primitive
    (by simpa only [hnorm] using physical) (by simpa only [hnorm] using scalar)
    (by simpa only [hnorm,Fintype.card_coe] using old) buffer
    (S i).Cs_one hCp hCd hKt.le hKc.le hC0.le hC1.le hKd.le hKcoarse.le
    (Sp i) (degreeLow i) (Klow i) Kreturn child hSp hdegree
    (by simpa only [hnorm,Fintype.card_coe,hdegree] using hKformula)
    (by simpa only [hnorm,Fintype.card_coe,hdegree] using hReturn) hT
  simpa only [nodeSourceAmp_eq_native N] using raw

/-- All four INNER stages, starting from the genuine terminal source.
The three recursive steps introduce no analytic assumptions. The returned
forest uses the same global dyad box throughout the finite induction. -/
theorem eventual_actual_first_inner_node_outputs
    (hH : RayOrthogonality.globalUnits M≤H)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)(hbetaHi : HeckeZeroSupremum.beta≤7/8)
    (eps tau : ℝ)(heps : 0<eps)(htau : 0<tau)(htauOne : tau≤1)
    (eta : Character)(Q : Ideal O)(hQM : Q≤M)
    (hQ0 : internalQ Q eta≠0)(hQt : internalQ Q eta≠⊤)
    (hQ72 : internalQ Q eta≤Ideal.span {(72:O)}) :
    ∃Kclass constant : ℝ,1≤Kclass ∧ 0<constant ∧
    ∃(control : Finset (ℕ×ℕ))(degree : ℕ),∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀C : SourceContext (α:=alpha) M H,C.W=W→C.etaSeed=eta→C.Q=Q→
        C.globalBase=Z→C.gridDenominator=gridSize→C.slotMesh=localSlotMesh eps→
        C.Bnorm=returnedNormCap 250000→C.Tz=Z^tau→Kclass≤C.highClassCap→
      ∀N : ReachableNode C (0:Fin 4),
        Nonempty (NodeOutput hH N constant (oldLoss eps) 250000 control degree
          (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha))) :=by
  obtain ⟨K3,C3,hK3,hC3,S3,d3,terminal⟩:=eventual_actual_terminal_node_outputs_all_boxes (alpha:=alpha)
    hH W hW hWs hbeta hbetaHi eps tau (returnedNormCap 250000) 250000 heps htau
    eta Q hQM hQ0 hQt hQ72
  have base : ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀C : SourceContext (α:=alpha) M H,C.W=W→C.etaSeed=eta→C.Q=Q→
        C.globalBase=Z→C.gridDenominator=gridSize→C.slotMesh=localSlotMesh eps→
        C.Bnorm=returnedNormCap 250000→C.Tz=Z^tau→K3≤C.highClassCap→
      ∀N : ReachableNode C (3:Fin 4),
        Nonempty (NodeOutput hH N C3 (oldLoss eps) 250000 S3 d3
          (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha))) :=by
    filter_upwards [terminal] with Z hz
    refine ⟨hz.1,?_⟩
    intro C hCW hCeta hCQ hbase hgrid hmesh hnorm hheight hclass N
    exact hz.2 (fun _=>rootNativeDyadBox C.globalBase (Fintype.card alpha)) C
      hCW hCeta hCQ hbase hgrid hmesh hnorm hheight hclass N
  obtain ⟨K2,C2,hK2,hC2,S2,d2,stage2⟩:=eventual_actual_inner_stage_from_deeper
    hH W hW hWs hbeta hbetaHi eps tau heps htau htauOne eta Q hQM hQ0 hQt hQ72
    (2:Fin 4) (by decide) K3 C3 hC3.le S3 d3 base
  obtain ⟨K1,C1,hK1,hC1,S1,d1,stage1⟩:=eventual_actual_inner_stage_from_deeper
    hH W hW hWs hbeta hbetaHi eps tau heps htau htauOne eta Q hQM hQ0 hQt hQ72
    (1:Fin 4) (by decide) K2 C2 hC2.le S2 d2 stage2
  exact eventual_actual_inner_stage_from_deeper
    hH W hW hWs hbeta hbetaHi eps tau heps htau htauOne eta Q hQM hQ0 hQt hQ72
    (0:Fin 4) (by decide) K1 C1 hC1.le S1 d1 stage1

end
end OAI.SevenEighths.Cycle153TerminalSchedule
#print axioms OAI.SevenEighths.Cycle153TerminalSchedule.eventual_actual_inner_stage_from_deeper
#print axioms OAI.SevenEighths.Cycle153TerminalSchedule.eventual_actual_first_inner_node_outputs
