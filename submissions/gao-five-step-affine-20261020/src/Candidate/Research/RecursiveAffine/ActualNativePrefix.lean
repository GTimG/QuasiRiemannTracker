/- Actual native LOW continuation: literal prefix, source scale and norm propagation. Apache-2.0. -/
import Candidate.Research.RecursiveAffine.PrefixLowPresented
import Candidate.Research.RecursiveAffine.NativePrefixNorm
import Candidate.Research.RecursiveAffine.NativeContinuationSource
import Candidate.Cycle63.Physical.InitialMass.LowChildScale
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowNormalizedPayment

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve Cycle63Moment Cycle63InitialMass RayFourExpansion
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildSourceCaps
open CenteredMomentSecondInputCapacitySource Cycle63FinalNatural Cycle63FinalLow
open CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondHeightFamily CenteredMomentEnergyState
open CenteredMomentNaturalFixedRaySource CenteredMomentSourceLiveColumn Cycle153HighProvider Cycle153JointCount

variable {α : Type} [Fintype α] [DecidableEq α]
variable {β : Type} [Fintype β] [DecidableEq β]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {hH : RayOrthogonality.globalUnits M≤H}
variable {C : SourceContext (α:=α) M H} {j : Fin 4}

/-- Native geometry supplies the next masked prefix and its exact scale
bridge. The source cap is the actual radius bound3, not a bound on an
invented family. The residual allocation, character and retained puncture
are those of this SAME actual live geometry. -/
theorem actual_native_continuation_prefix (N : ReachableNode C j)
    (s : Input β) (R : Ideal O)
    (P0 : PrefixHighPresentation (prefixDictionary j.val C.etaSeed) s.η R)
    (hP0mult : P0.mult=N.presentation.mult)
    (reflected second : Bool) (Mrow amp xi reserve b t eps : ℝ) (budget : ℕ)
    (hMrow : Mrow≤2) (hamp : 0≤amp) (hloss : 0≤frequencyLoss N.localBase 32 xi+reserve)
    (heps0 : 0≤eps) (heps : eps≤1) (hb : 0<b)
    (hsmall : Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2≤1)
    (hsource : sourceRadius s≤N.localBase^(3:ℝ))
    (bin : ℤ×(Fin 5→ℤ))
    (q : GeometryLowFirstIndex reflected s R 1
      (N.localBase^Mrow) N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin)
    (hz1 : s.W₁ 0=0) (hz2 : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R 1 N.localBase Mrow amp xi reserve
      b t budget N.localBase_gt_one bin q) :
    let datum:=geometryLowSecondDatum reflected s R 1 N.localBase Mrow amp xi reserve b t
      budget N.localBase_gt_one bin q hz1 hz2 n
    let src:=geometryLowFirstChild reflected s R 1 (N.localBase^Mrow) N.localBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin t q
    ∀(allocation : actualAllocations src.pools (if second then datum.D else datum.C))
      (r : secondLiveRows (fun _:Unit=>datum.block))
      (hf1 : frozenCoefficient q.2.val (geometryColumnIdeal reflected s R 1
        (N.localBase^Mrow) N.localBase xi (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _)
        bin q.1.val) R s.ν s.W s.P≠0)
      (hf2 : frozenCoefficient allocation.val (if second then datum.D else datum.C)
        datum.R src.ν src.W src.P≠0) (chi : RayCharacter) (Bmask : ℝ),
    let chain:=geometryLowActualChain reflected s R 1 N.localBase Mrow amp xi reserve b t
      budget N.localBase_gt_one bin q hz1 hz2 n second allocation
    let g:=geometryLowActualGeometry reflected s R 1 N.localBase Mrow amp xi reserve b t
      budget N.localBase_gt_one bin q hz1 hz2 n second allocation r hf1 hf2
    ∀(hP : chain.R₂*chain.E₂≠0) (hPN : ((chain.R₂*chain.E₂).absNorm:ℝ)≤N.localBase^Bmask),
    let st:=retainedState N.localBase Bmask N.localBase_gt_one (g.datum.τ chi) (internalQ C.Q C.etaSeed)
      (chain.R₂*chain.E₂) hP hPN g.datum.radius g.datum.C g.datum.D g.datum.inactive
    let first:=geometryFirstLabel s R 1 (N.localBase^Mrow) N.localBase xi
      (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin q.1.val
    let label:=actualSecondArithmeticLabel _ _ _ _ _ _ _ n
    ∃ Next : PrefixHighPresentation (prefixDictionary (j.val+1) C.etaSeed) st.character st.puncture,
      Next.mult=Cycle63Moment.childMultiplier (!reflected) P0.mult (P0.unit (!reflected)) ⟨first,label⟩ ∧
      ((Ideal.span {Next.mult}).absNorm:ℝ)≤C.globalBase^prefixCap (j.val+1) ∧
      N.unit*st.rowWidth+Real.logb C.globalBase ((Ideal.span {Next.mult}).absNorm:ℝ)-
        Real.logb C.globalBase ((Ideal.span {P0.mult}).absNorm:ℝ) ≤
        N.unit*actualHighCoordinates reflected (!reflected) second first datum.C datum.D datum.inactive
          N.localBase Mrow (Real.logb N.localBase (volume s)) amp xi reserve eps 2+
        N.unit*(Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2) := by
  intro datum src allocation r hf1 hf2 chi Bmask chain g hP hPN st first label
  obtain ⟨Next,hmult⟩:=prefix_presented_low_child (prefixDictionary j.val C.etaSeed)
    reflected second s R 1 P0 N.localBase Mrow amp xi reserve b t
    budget N.localBase_gt_one bin q hz1 hz2 n allocation r hf1 hf2 chi Bmask hP hPN
  let localMult:=Cycle63Moment.childMultiplier (!reflected) 1 (P0.unit (!reflected)) ⟨first,label⟩
  have hfactor : Next.mult=P0.mult*localMult := by
    rw [hmult]
    dsimp only [localMult,Cycle63Moment.childMultiplier]
    ring
  have hlocal : localMult≠0 := by
    have hp:P0.mult*localMult≠0 := hfactor ▸ Next.hv
    exact right_ne_zero_of_mul hp
  let fs:=geometryFirstSource s R 1 (N.localBase^Mrow) N.localBase xi
    (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _) bin q.1.val.1
  have hfirstnorm : (first.1.1.absNorm:ℝ)≤N.localBase^(130:ℝ) := by
    have hg:=actual_main_low_first_source_gates reflected s R 1
      (N.localBase^Mrow) N.localBase xi 3 (Real.rpow_pos_of_pos (zero_lt_one.trans N.localBase_gt_one) _)
      (show Squarefree (1:Ideal O) from squarefree_one) hz1 hz2 hsource bin (fun _:Unit=>q) ()
    exact hg.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le N.localBase_gt_one.le (by norm_num))
  have hscale:=live_main_row_scale_le g N.localBase_gt_one hb reflected (!reflected) second first reserve eps
    fs.hC fs.hD fs.sameSupport rfl datum.C datum.D datum.inactive rfl rfl HEq.rfl 1
    (P0.unit (!reflected)) (fun l=>Units.isUnit _)
    (by simpa [normValue] using heps0)
    hlocal (g.datum.τ chi) (internalQ C.Q C.etaSeed) (chain.R₂*chain.E₂) hP hPN
  have hparentpos : (0:ℝ)<((Ideal.span {P0.mult}).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr P0.hv))
  have hlocalpos : (0:ℝ)<((Ideal.span {localMult}).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hlocal))
  have hnextpos : (0:ℝ)<((Ideal.span {Next.mult}).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr Next.hv))
  have hnormprod : ((Ideal.span {Next.mult}).absNorm:ℝ)=
      ((Ideal.span {P0.mult}).absNorm:ℝ)*((Ideal.span {localMult}).absNorm:ℝ) := by
    rw [hfactor,←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]
  have hlogprod : Real.logb C.globalBase ((Ideal.span {Next.mult}).absNorm:ℝ)=
      Real.logb C.globalBase ((Ideal.span {P0.mult}).absNorm:ℝ)+
      Real.logb C.globalBase ((Ideal.span {localMult}).absNorm:ℝ) := by
    rw [hnormprod,Real.logb_mul hparentpos.ne' hlocalpos.ne']
  have hlogbase : N.unit*Real.logb N.localBase ((Ideal.span {localMult}).absNorm:ℝ)=
      Real.logb C.globalBase ((Ideal.span {localMult}).absNorm:ℝ) := by
    rw [N.localBase_eq]
    unfold Real.logb
    rw [Real.log_rpow (zero_lt_one.trans C.globalBase_gt_one),mul_div_assoc',
      mul_div_mul_left _ _ N.unit_pos.ne']
  have hglobal : N.unit*st.rowWidth+Real.logb C.globalBase ((Ideal.span {Next.mult}).absNorm:ℝ)-
        Real.logb C.globalBase ((Ideal.span {P0.mult}).absNorm:ℝ) ≤
      N.unit*actualHighCoordinates reflected (!reflected) second first datum.C datum.D datum.inactive
        N.localBase Mrow (Real.logb N.localBase (volume s)) amp xi reserve eps 2+
      N.unit*(Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2) := by
    have hs:=mul_le_mul_of_nonneg_left hscale N.unit_pos.le
    change N.unit*(st.rowWidth+Real.logb N.localBase ((Ideal.span {localMult}).absNorm:ℝ))≤_ at hs
    rw [mul_add,hlogbase] at hs
    rw [hlogprod]
    nlinarith only [hs]
  let physical : NativePaidPathNode C.globalBase := {
    unit:=N.unit
    unit_pos:=N.unit_pos
    local_base:=Real.one_lt_rpow C.globalBase_gt_one N.unit_pos
    reflected:=reflected
    second:=second
    first:=first
    firstC:=fs.hC
    firstD:=fs.hD
    firstSupport:=fs.sameSupport
    C:=datum.C
    D:=datum.D
    hC:=datum.hC
    hD:=datum.hD
    secondSupport:=datum.sameSupport
    inactive:=datum.inactive
    rowWidth:=Mrow
    length:=Real.logb N.localBase (volume s)
    amp:=amp
    xi:=xi
    reserve:=reserve
    eps:=eps
    massLoss:=0
    sideError:=lowLabelSide reflected (C.globalBase^N.unit) (Real.logb N.localBase (volume s)) first
    side:=le_of_eq (zero_add (lowLabelSide reflected (C.globalBase^N.unit)
      (Real.logb N.localBase (volume s)) first)) }
  have hcoord : physical.coordinate 2=N.unit*actualHighCoordinates reflected (!reflected) second first
      datum.C datum.D datum.inactive N.localBase Mrow (Real.logb N.localBase (volume s)) amp xi reserve eps 2 := by
    dsimp only [NativePaidPathNode.coordinate,physical]
    rw [←N.localBase_eq]
  have hfirstphysical : (physical.first.1.1.absNorm:ℝ)≤(C.globalBase^physical.unit)^(130:ℝ) := by
    change (first.1.1.absNorm:ℝ)≤(C.globalBase^N.unit)^(130:ℝ)
    rw [←N.localBase_eq]
    exact hfirstnorm
  have hincrement:=native_prefix_increment physical hfirstphysical hMrow hamp
    (by change 0≤frequencyLoss (C.globalBase^N.unit) 32 xi+reserve; rw [←N.localBase_eq]; exact hloss)
    heps N.unit_le_one (N.unit*st.rowWidth)
    (Real.logb C.globalBase ((Ideal.span {Next.mult}).absNorm:ℝ))
    (Real.logb C.globalBase ((Ideal.span {P0.mult}).absNorm:ℝ))
    (N.unit*(Real.logb N.localBase 4+2*(budget:ℝ)*Real.logb N.localBase b+xi/2))
    (mul_nonneg N.unit_pos.le st.row_nonneg)
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall N.unit_pos.le)
    (by rw [hcoord]; exact hglobal)
  have hcap : ((Ideal.span {Next.mult}).absNorm:ℝ)≤C.globalBase^prefixCap (j.val+1) := by
    apply (Real.logb_le_iff_le_rpow C.globalBase_gt_one hnextpos).mp
    have hparentcap : ((Ideal.span {P0.mult}).absNorm:ℝ)≤C.globalBase^prefixCap j.val := by
      rw [hP0mult]
      exact N.presentation_global_norm
    have hp:=(Real.logb_le_iff_le_rpow C.globalBase_gt_one hparentpos).mpr hparentcap
    rw [prefixCap_succ]
    linarith only [hp,hincrement]
  exact ⟨Next,hmult,hcap,hglobal⟩

/-- The literal next state's row scale is unchanged in global units.
This binds the native retained-row scale above to the actual child node,
including widening and the chosen continuation-base change. -/
theorem native_continuation_global_row_scale {Z oldMask bPhi : ℝ}
    (st : CenteredMomentEnergyState.NaturalState Z oldMask bPhi) (parentUnit u : ℝ)
    (hu : 0<u) (hwide : st.width≤u)
    (hmask : (st.puncture.absNorm:ℝ)≤(Z^u)^(20:ℝ)) :
    (parentUnit*u)*(Cycle153RegionalLow.nativeContinuationState st u hu hwide hmask).rowWidth=
      parentUnit*st.rowWidth := by
  change (parentUnit*u)*(st.rowWidth/u)=parentUnit*st.rowWidth
  field_simp [hu.ne']

end
end OAI.SevenEighths.Cycle153Reachable

#print axioms OAI.SevenEighths.Cycle153Reachable.actual_native_continuation_prefix

#print axioms OAI.SevenEighths.Cycle153Reachable.native_continuation_global_row_scale
