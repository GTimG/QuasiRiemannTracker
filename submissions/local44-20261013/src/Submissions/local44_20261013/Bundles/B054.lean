/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B002
import Submissions.local44_20261013.Bundles.B003
import Submissions.local44_20261013.Bundles.B009
import Submissions.local44_20261013.Bundles.B013
import Submissions.local44_20261013.Bundles.B020
import Submissions.local44_20261013.Bundles.B041
import Submissions.local44_20261013.Bundles.B044
import Submissions.local44_20261013.Bundles.B045
import Submissions.local44_20261013.Bundles.B047
import Submissions.local44_20261013.Bundles.B048
import Submissions.local44_20261013.Bundles.B050
import Submissions.local44_20261013.Bundles.B051
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CanonicalLowPhysical
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.PositiveLowBandSource

/- BEGIN ORIGINAL MODULE Analytic.SubsetBufferedProduct ; sha256 b72d8d8b61cda0957603572dc177548ebba6dffbc883c704d5c5b37945ed308f -/
section


/-! A fixed original slot system supplies one finite powerset of possible
surviving systems. All tail orders and constants are selected over that
powerset before any live arithmetic label. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators ContDiff
open Set
namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorZeros HeckePrimeRay HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open ProbeHighRowFamily ConcretePrimeRowBridge LocalMoment CenteredExceptionalProfile
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

lemma relative_subset_maximum_le {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (η : Character) (η₀ : Slot → Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQM : Q ≤ M) (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
    (w : NonzeroElement) (hex : ¬FixedInducingRow η Q fixedBadMask 1 w.val)
    (J : Finset Slot) (T : ℝ) :
    zeroMaximum (fun label => (momentData (jointRelativeParent η
      (relativeSlotTranslate M H hH (fun j : J => η₀ j.val)) label)).character w)
      (jointRelativeMoment_nonprincipal η (relativeSlotTranslate M H hH (fun j : J => η₀ j.val))
        Q hQ72 (relativeSlotTranslate_fixedQ M H hH (fun j : J => η₀ j.val) Q hQM
          (fun j => hQη₀ j.val)) w hex) T ≤
    zeroMaximum (fun label => (momentData (jointRelativeParent η
      (relativeSlotTranslate M H hH η₀) label)).character w)
      (jointRelativeMoment_nonprincipal η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) w hex) T := by
  apply zeroMaximum_le_of_zero_inclusion
  intro label
  rcases label with ⟨parent,label⟩
  cases label with
  | none => exact ⟨(parent,none), fun _ _ h => h⟩
  | some jt => exact ⟨(parent,some (jt.1.val,jt.2)), fun _ _ h => h⟩

/-- One constant works for every subset of the original slots and every
live row. The full original dictionary controls the upper bin even when
the selected subset itself has no high zero. -/
theorem actual_subset_buffered_bound {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (η : Character) (η₀ : Slot → Character) (Q : Ideal O)
    (hQ72 : Q ≤ Ideal.span {(72 : O)}) (hQM : Q ≤ M) (hQη₀ : ∀ j, Q ≤ (η₀ j).modulus)
    (V : Slot → ℝ → ℂ) (A B : Slot → ℝ) (hA : ∀ j, 0 < A j)
    (hVs : ∀ j, Function.support (V j) ⊆ Icc (A j) (B j)) (hV : ∀ j, ContDiff ℝ ∞ (V j))
    (Rwidth dmax τ ε e κ ηaux σmin σmax loss : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hκone : κ ≤ 1) (hη : 0 ≤ ηaux)
    (hbudget : 12*e*(Rwidth+2)+8*κ+2*ηaux ≤ ε)
    (hprimebudget : 8*e*Rwidth+κ ≤ ε)
    (hloss : (2+2*(Fintype.card Slot : ℝ))*ε ≤ loss)
    (profileBound : ℕ → ℝ) (hprofile : ∀ k, 0 ≤ profileBound k) :
    ∃ (orders : Finset Slot → ℕ) (N : ℕ) (C : ℝ), (∀ J, orders J ≤ N) ∧ 0 < C ∧
      ∀ Z d : ℝ, 1 ≤ Z → 0 ≤ d → d ≤ dmax → 2 ≤ Z^d → 2 < Z^τ →
      ∀ (p : DensityWindow), p.upper < p.lower+2*e →
      ∀ (w : NonzeroElement)
        (R : JointRelativeLabel η (Option (Slot × RayQuotient.Characters M H)) → Ideal O)
        (hR : ∀ label, R label ≠ 0),
      jointRelativeSourceZeroBin η (relativeSlotTranslate M H hH η₀) Q hQ72
        (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) R hR
        p.lower p.upper p.height w →
      ∀ (J : Finset Slot) (D : JointBufferedProductData η w J (orders J) profileBound p.lower e),
      D.Admissible M H hH (fun j : J => η₀ j.val) (fun j : J => A j.val) (fun j : J => B j.val)
        Rwidth τ ηaux σmin σmax Z d p.height →
      ‖D.value M H (fun j : J => η₀ j.val) (fun j : J => V j.val) (fun j : J => B j.val) Z d‖^2 ≤
        C*(Z^d)^((2*p.lower-1)*D.length+loss) := by
  have hchoice (J : Finset Slot) := natural_buffered_product_bound M H hH
    (fun j : J => η₀ j.val) Q hQM (fun j => hQη₀ j.val)
    (fun j : J => V j.val) (fun j : J => A j.val) (fun j : J => B j.val)
    (fun j => hA j.val) (fun j => hVs j.val) (fun j => hV j.val)
    Rwidth dmax τ ε e κ ηaux σmin σmax loss hRw hdmax hτ hε he he' hκ hκone hη
    hbudget hprimebudget (by
      have hc : (Fintype.card J : ℝ) ≤ Fintype.card Slot := by
        exact_mod_cast (show Fintype.card J ≤ Fintype.card Slot by simpa using Finset.card_le_univ J)
      nlinarith) profileBound hprofile
  choose orders Cs hCs hbound using hchoice
  let C : ℝ := 1+∑ J : Finset Slot, Cs J
  have hC : 0 < C := by
    have hh := Finset.sum_nonneg (fun J (_ : J ∈ (Finset.univ : Finset (Finset Slot))) => (hCs J).le)
    dsimp [C]
    linarith
  have hCs_le (J : Finset Slot) : Cs J ≤ C := by
    have hh := Finset.single_le_sum
      (fun J (_ : J ∈ (Finset.univ : Finset (Finset Slot))) => (hCs J).le) (Finset.mem_univ J)
    dsimp [C]
    linarith
  refine ⟨orders,∑ J : Finset Slot, orders J,C,?_,hC,?_⟩
  · intro J
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ J)
  intro Z d hZ hd hdmax' hbase hT p hp w R hR hbin J D hD
  obtain ⟨hex,hlo,hhi⟩ := hbin
  have hmax : zeroMaximum (bufferedProductFamily M H hH (fun j : J => η₀ j.val)
      (excluded D.natural.character D.puncture))
      (bufferedProductFamily_nonprincipal M H hH (fun j : J => η₀ j.val)
        D.parent.val w.val D.natural Q D.puncture hQM (fun j => hQη₀ j.val)
        D.puncture_ne w.property (D.eligible Q hQ72 hex))
        (3*(D.bin+1 : ℕ)*Z^τ) < p.lower+2*e := by
    apply (zeroMaximum_mono _ _ hD.buffer_height).trans_lt
    apply (D.zeroMaximum_le M H hH (fun j : J => η₀ j.val) Q hQ72 hQM
      (fun j => hQη₀ j.val) hex p.height).trans_lt
    apply (relative_subset_maximum_le M H hH η η₀ Q hQ72 hQM hQη₀ w hex J p.height).trans_lt
    rw [← jointRelativeSource_zeroMaximum η (relativeSlotTranslate M H hH η₀) Q hQ72
      (relativeSlotTranslate_fixedQ M H hH η₀ Q hQM hQη₀) w hex R hR p.height]
    exact hhi.trans_lt hp
  have hb := hbound J Z d hZ hd hdmax' hbase hT D.parent.val w.val D.natural D.puncture
    D.puncture_ne w.property (D.eligible Q hQ72 hex) p.lower D.bin
    (by linarith [p.lower_bound]) (by linarith [p.upper_bound]) hmax
    D.plain₁ D.plain₂ D.r₁ D.r₂ D.r D.σ D.v D.t
    hD.r₁_nonneg hD.r₁_le hD.r₂_nonneg hD.r₂_le hD.slots hD.conductor
    hD.freq₁ hD.freq₂ hD.freq_slots hD.height_four hD.height_two hD.log_scale
  exact hb.trans (mul_le_mul_of_nonneg_right (hCs_le J) (Real.rpow_nonneg (by positivity) _))

#print axioms actual_subset_buffered_bound
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.SubsetBufferedProduct -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.NaturalLowPhysical ; sha256 e6ce989d30adc6ff0e4f411a5490d77cf0d13011ba53bffbc69daf51f1410eaf -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/NaturalLowPhysical.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/







namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyNaturalLowPhysical
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
open CenteredMomentEnergyNaturalLowSourceBound CenteredMomentEnergyPositiveLowBandSource
open CenteredMomentEnergyNaturalSourceAdmission
open Cycle25CenteredMomentEnergyPositiveHighParameters Cycle25CenteredMomentEnergyPositiveBalancedAdmission
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyStageReserveSchedule
open CenteredMomentEnergyStageMargins Cycle25CenteredMomentEnergyFirstSourceParameters
open CenteredMomentEnergyFirstLiveAdmission CenteredMomentEnergyNaturalInputMatches
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem actual_natural_low_physical
    (W:ℝ→ℂ)(hW:ContDiff ℝ ∞ W)(aslot bslot lo hi a b bΦ:ℝ)
    (haslot:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hbslot:0≤ bslot)(ha:0< a)(hb:0≤ b)
    (Mglobal A B Bmask Mparent Mchild Lgoal Lslot rho κ ε:ℝ)(k:ℕ)
    (hMg:0≤ Mglobal)(hA:0≤ A)(hB:0≤ B)(hBm:0≤ Bmask)
    (_hMp:0≤ Mparent)(hMc:0≤ Mchild)(hL:0≤ Lgoal)(hLs:0≤ Lslot)
    (hMA:Mparent≤ A)(hready:readyBudget A Bmask≤ B)
    (hκ:(7/10:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(hε:0<ε)
    (hslot:Lslot≤ mesh Mglobal B κ ε)
    (hdrop:Mparent-amplification ε/2≤ Mchild)
    (Ψ:(T:Finset α)→𝓢(ℝ,ℂ))(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,
    ∀η₀:Character,∀Q:Ideal O,Q≤ M→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
    ∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,1< Z ∧
    ∀εchild C₀ C₁:ℝ,εchild≤ stageLoss Mglobal B ε k→0≤ C₀→0≤ C₁→
      ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Mchild εchild Z degree S C₀→
      PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 (2*max Lgoal Mparent+reserve Mglobal B ε/4)
        Lslot lo hi Mchild εchild κ Z η₀ Q degree S C₁→
      PhysicalLowAt (α:=α) M H hH W hW.continuous aslot bslot lo hi haslot hWs
        a b bΦ Bmask Lgoal Lslot rho Mparent κ (reserve Mglobal B ε/4)
        (physicalLoss Mglobal B ε k) Z ha Ψ η₀ Q U J (C*(C₀+C₁+1)) := by
  let r:=reserve Mglobal B ε
  let N:=Fintype.card α
  let Mslot:=profileBound W hW.continuous aslot bslot lo hi haslot hWs
  let a0:=CenteredMomentSecondInputCapacitySource.lowerFactor N aslot a
  let lp:=(min 1 aslot)^N*a*a
  have hMslot:1≤ Mslot:=profileBound_ge_one W hW.continuous aslot bslot lo hi haslot hWs
  have ha0:0< a0:=CenteredMomentSecondInputCapacitySource.lowerFactor_pos N aslot a haslot ha
  have hlp:0< lp:=by dsimp [lp];positivity
  obtain ⟨hsigma,hsigma1,hr,hxi,hxi1,hes,hes1,hem,hmesh,hmesheta,heta,hetastrict,_,_⟩:=
    parameter_gates Mglobal A B κ ε hMg hA hB hκ hε
  have hrpos:0< r/4:=hr
  have hκsmall:(1/6:ℝ)≤κ:=by linarith
  have hLbase:0≤ max Lgoal Mparent:=hL.trans (le_max_left _ _)
  have hLphys:0≤2*max Lgoal Mparent+r/4:=by positivity
  obtain ⟨U,J,hphysical⟩:=CenteredMomentEnergyCanonicalLowPhysical.actual_low_physical (α:=α)
    M H hH W aslot bslot Mchild Lslot (r/4) lo hi κ a b Mslot (maskEpsilon Mglobal B ε)
    (zero_le_one.trans hMslot) hem ha hb (2*max Lgoal Mparent+r/4) hLphys degree S haslot hWs hW hMc hLs hr
    hκsmall hbeta hκbeta N aslot (max 1 bslot) a0 (r/4) haslot (le_max_left _ _) ha0 hr
    (fun _=> aslot) (fun _=> bslot) (fun _=> hbslot)
    (sourceEpsilon Mglobal A B ε) (r/4) (r/4) (A+1) (r/4) (2*amplification ε+1)
    hes hr hr hr (amplification ε) hsigma hxi A Bmask (amplification ε/12) (r/4) (r/4)
    hA hBm hetastrict hr hsigma1 hxi1 hr hes1 le_rfl Ψ (r/4) lp hr hlp
  refine ⟨U,J,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨C,hC,Z₀,hZ₀,hbound⟩:=hphysical η₀ Q hQM hQ0 hQt hQ72
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop Z₀,
    eventually_actual_four_fit Mglobal A Bmask B κ ε hMg hA hBm hB hready hκ hε,
    (Filter.tendsto_atTop.1 (tendsto_rpow_atTop (by linarith : 0<2*(r/4)))) (max 1 b*max 1 b),
    eventually_scale_admission b (max Lgoal Mparent) (r/4) hLbase hr]
    with Z hZZ hfit hclipPow hscale
  have hZ:1< Z:=hZ₀.trans_le hZZ
  have hclip:Real.logb Z (max 1 b*max 1 b)≤2*(r/4):=by
    have hh:=Real.logb_le_logb_of_le hZ (by positivity:0< max 1 b*max 1 b) hclipPow
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  refine ⟨hZ,?_⟩
  intro εchild C₀ C₁ hell hC₀ hC₁ hzero hpos T θ w σ freq t height hw hwL hσlo hσhi hheight hfreq state hQ hrho hstate
    p X₁ X₂ hX₁ hX₂ hc₁ hc₂ hcapacity hlow
  let inp:=zeroSourceInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂
  have hN:Fintype.card T≤ N:=Fintype.card_le_of_injective (fun i:T=> i.val) Subtype.val_injective
  have hm:=(both_matches M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂).2
  have hu:=hscale.2 T M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) Bmask bΦ a state p ha t X₁ X₂ hX₁ hX₂ κ
    hw hκsmall (hstate.trans (le_max_right _ _)) hcapacity
  have hg:max Lgoal Mparent≤2*max Lgoal Mparent+r/4:=by linarith
  have hu1:inp.X₁≤ Z^(2*max Lgoal Mparent+r/4):=
    hu.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hu2:inp.X₂≤ Z^(2*max Lgoal Mparent+r/4):=
    hu.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hg)
  have hp:=lower_product_admission M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ N hN
  have hlowV:Real.logb Z (volume inp)≤5*state.width/6:=
    (low_admission M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
      w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂ hZ hlow).2
  have hr:=CenteredMomentEnergyNaturalSourceAdmission.radial_admission state
  have hwidth:=actual_width_le state hZ
  have hh:=hbound T θ Z hZZ εchild C₀ C₁ hC₀ hC₁ hzero hpos w σ freq height (mesh Mglobal B κ ε)
    hmesh.le hw (fun i=>(hwL i).trans hslot)
    (fun i=>((hwL i).trans hslot).trans hmesheta) hwL hσlo hσhi hheight hfreq
    inp hm (fun _=> le_rfl) (fun _=> le_rfl) (fun _=> rfl) (fun _=> rfl) hN le_rfl (le_max_right _ _)
    hb hb (le_max_right _ _) (le_max_right _ _) hp.2.2 state.puncture 1 state.puncture_ne_zero
    state.puncture_bound (by simp) (by simp) state.radial.scale hr.1 p rfl rfl
    hu1 hu2 hu.2.2.2.2.2.2.1 hu.2.2.2.2.2.2.2 state.width state.width (r/4) (columnLoss Mglobal B ε k)
    hrpos.le (hstate.trans hMA) hcapacity hwidth hwidth (by linarith only [hstate,hdrop])
    hclip le_rfl hlowV (hfit.2 k εchild hell)
  have hcost:state.width+columnLoss Mglobal B ε k+r/4=state.width+physicalLoss Mglobal B ε k:=by
    rw [add_assoc]
    exact congrArg (state.width+·) (columnLoss_physical Mglobal B ε k)
  rw [hcost] at hh
  have ht:inp.t=t:=rfl
  have hv0:volume inp = volume (sourceInput M H hH η₀ θ W hW.continuous aslot bslot lo hi haslot hWs
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) state p ha t X₁ X₂ hX₁ hX₂):=rfl
  rw [ht,hv0] at hh
  simpa only [map_one,Nat.cast_one,div_one,mul_assoc] using hh

end SevenEighths.Cycle25CenteredMomentEnergyNaturalLowPhysical

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.NaturalLowPhysical -/

/- BEGIN ORIGINAL MODULE Cycle25.Energy.PositiveHighBound ; sha256 9d8fc7b8ef7f6b6a441c2574a5f4f577fe76fd535994f09494862bf47ce6f2aa -/
section
/-
Adapted from OpenAI/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Upstream source: Energy/PositiveHighBound.lean.
Licensed under Apache-2.0; see UPSTREAM_LICENSE.
Modifications: fresh namespace and the κ ≥ 7/10 comparison/clipping geometry.
-/











namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Cycle25CenteredMomentEnergyPositiveHighBound
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open Cycle25CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open Cycle25CenteredMomentEnergyPositiveHighSource (balancedInput)
open Cycle25CenteredMomentEnergyOriginalHighReflectionSymmetric (balanced_four_scale_gates)
open Cycle25CenteredMomentEnergyPositiveHighSourceBounded Cycle25CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
open CenteredMomentCommonRadialData CenteredMomentSourceRow
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
local instance : DecidableEq (α⊕Fin 2):=Classical.decEq _
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open Cycle25CenteredMomentEnergyPositiveHighAssembly (low_restrict)

open Cycle25CenteredMomentEnergyPositiveHighAssemblyBounded Cycle25CenteredMomentEnergyPositiveHighParameters
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyNaturalInputMatches

theorem actual_high_from_physical
    (Wslot:ℝ→ ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask εdiag ξ saving:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤ Mcap)(hBmask:0≤ Bmask)(hbslot:0≤ bslot)(hεdiag:0<εdiag)(hξ:0<ξ):
    ∃L:ℝ,0≤ L ∧ L≤ Mcap+Bmask+rho/100 ∧
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),∀Jmass:ℕ,∀Smass:Finset (ℕ×ℕ),
    ∃Jout:ℕ,∃U:Finset (ℕ×ℕ),∃Cfixed:ℝ,0< Cfixed ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(e emass efinal Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K Cmass:ℝ),
        0≤ e→0≤ K→0≤ Cmass→e+ε≤ efinal→emass≤ efinal→εdiag≤ efinal→-saving≤ efinal→
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K→
      ∀(θ:α→ RayQuotient.Characters M H)(w σ freq:α→ ℝ)(t height:ℝ),
      (∀i,0≤ w i)→ (∀i,w i≤ Lslot)→ ∀hσlo:(∀i,lo≤σ i),∀hσhi:(∀i,σ i≤ hi),
      0≤ height→ (∀i,|freq i|≤ height)→ 7/10≤κ→
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀→ rho≤ s.width→ s.width≤ Mcap→
      ∀(p:Profiles a b)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂),
      5*s.width/6≤ length Z X₁+length Z X₂+(∑i,w i)→
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width→
      let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂;
      ((Z^(s.width/4)≤ inp.X₁ ∧ Z^(s.width/4)≤ inp.X₂ ∧
        Z^(s.width/4)≤ inp.Y₁ ∧ Z^(s.width/4)≤ inp.Y₂) →
        physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume inp≤
          Cmass*(p.control Smass)^2*(1+|t|+height)^Jmass*Z^(s.width+emass)) →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1) inp.slots inp.toData.coefficient inp.P
        X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
          (1+|t|+height)^Jout*Z^(s.width+efinal) :=by
  obtain ⟨d,L,hd,hL,hLupper,Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hstage⟩:=
    actual_high_source_split (α:=α) M H hH Wslot aslot bslot lo hi haslot hsSlot hcSlot
      a b bΦ rho ε Mcap Bmask εdiag ξ saving ha hlo hhi hbΦ hrho hε hM hBmask hbslot hεdiag hξ
  refine ⟨L,hL,hLupper,Ψ,hsΨ,hnΨ,?_⟩
  intro degree S Jmass Smass
  obtain ⟨Ju,Jr,Uu,Ur,Cu,Cr,hCu,hCr,hbound⟩:=hstage degree S
  let U:Finset (ℕ×ℕ):=insert (0,0) (Smass∪Uu∪Ur)
  let Jout:ℕ:=Jmass+Ju+Jr
  let P:ℝ:=(profileBound Wslot hcSlot aslot bslot lo hi haslot hsSlot)^(2*Fintype.card α)
  let D:ℝ:=Cdiag*P*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  let T:ℝ:=Ctail*P*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hP:0≤ P:=pow_nonneg (zero_le_one.trans
    (profileBound_ge_one Wslot hcSlot aslot bslot lo hi haslot hsSlot)) _
  have hD:0≤ D:=by dsimp [D];positivity
  have hT:0≤ T:=by dsimp [T];positivity
  let Cfixed:ℝ:=Cu+2*Cr+2*D+2*T+2
  have hCfixed:0< Cfixed:=by dsimp [Cfixed];positivity
  refine ⟨Jout,U,Cfixed,hCfixed,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro e emass efinal Lslot κ η₀ Q K Cmass he hK hCmass hefinal hmassFinal hdiagFinal htailFinal
    hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ s hQ hwidthLo hwidth
    p X₁ X₂ hX₁ hX₂ hlarge hcap
  dsimp only
  intro hphysical
  let inp:=balancedInput M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
    w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
  have hh:=hZ.2 e Lslot κ η₀ Q K he hK hlow θ w σ freq t height hw hwL hσlo hσhi
    hheight hfreq hκ s hQ hwidthLo hwidth p X₁ X₂ hX₁ hX₂ hlarge hcap
  have hz:0< Z:=zero_lt_one.trans hZ.1
  have hscale:0≤ s.radial.scale:=s.radial.scale_pos.le
  have hdg:=diagonalControl_nonneg s.radial.profile
  have hbase:1≤1+|t|+height:=by linarith [abs_nonneg t]
  let F:ℝ:=(p.control U)^2*(1+|t|+height)^Jout*Z^(s.width+efinal)
  have hF:0≤ F:=by dsimp [F];positivity
  have henv (Sj:Finset (ℕ×ℕ))(jj:ℕ)(ej:ℝ)(hSj:Sj⊆U)(hjj:jj≤ Jout)(hej:ej≤ efinal):
      (p.control Sj)^2*(1+|t|+height)^jj*Z^(s.width+ej)≤ F:=by
    have hp:=profile_control_mono p hSj
    have hp0:=p.control_nonneg Sj
    have hj:=pow_le_pow_right₀ hbase hjj
    have hex:=Real.rpow_le_rpow_of_exponent_le hZ.1.le (show s.width+ej≤ s.width+efinal by linarith)
    dsimp [F]
    gcongr
  have hu:Uu⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hr:Ur⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hm:Smass⊆U:=by intro x hx;simp only [U,Finset.mem_insert,Finset.mem_union];tauto
  have hju:Ju≤ Jout:=by dsimp [Jout];omega
  have hjr:Jr≤ Jout:=by dsimp [Jout];omega
  have hjm:Jmass≤ Jout:=by dsimp [Jout];omega
  have huni:Cu*(K+1)≤ Cfixed*(K+Cmass+1):=by
    dsimp [Cfixed]
    nlinarith only [hCr.le,hD,hT,hK,mul_nonneg hCr.le hK,mul_nonneg hD hK,mul_nonneg hT hK,
      mul_nonneg hCmass hCfixed.le]
  rcases hh with hunbalanced|⟨hfour,hsource⟩
  · change _≤ Cu*(K+1)*diagonalControl s.radial.profile*(p.control Uu)^2*
        (1+|t|+height)^Ju*Z^(s.width+e+ε) at hunbalanced
    have heq:=henv Uu Ju (e+ε) hu hju hefinal
    have hh':=mul_le_mul_of_nonneg_left heq (show 0≤ Cu*(K+1)*diagonalControl s.radial.profile by positivity)
    have hc:=mul_le_mul_of_nonneg_right huni (mul_nonneg hdg hF)
    apply hunbalanced.trans
    dsimp [F] at hh' hc ⊢
    rw [show s.width+e+ε=s.width+(e+ε) by ring]
    nlinarith only [hh',hc]
  · have hmass:=hphysical hfour
    have hmEnv:=henv Smass Jmass emass hm hjm hmassFinal
    have hmass':physicalMass inp s.puncture 1 fixedBadMask 1 Ψ s.radial.scale Z ξ/
        CenteredMomentAmplificationChildInput.volume inp≤ Cmass*F:=by
      apply hmass.trans
      convert mul_le_mul_of_nonneg_left hmEnv hCmass using 1 ; ring
    have hplain:(plainControl inp (p.profile 0) (p.profile 1))^2≤ P*(p.control U)^2:=by
      have hc:=balanced_control (α:=α) M H hH η₀ θ Wslot hcSlot aslot bslot lo hi haslot hsSlot
        w σ freq (fun i=>⟨hσlo i,hσhi i⟩) s p ha t X₁ X₂ hX₁ hX₂
        (Fintype.card α) le_rfl U
      have h00:(0,0)∈U:=Finset.mem_insert_self _ _
      simpa only [Finset.insert_eq_of_mem h00] using hc
    have hheight1:1≤(1+|t|+height)^Jout:=one_le_pow₀ hbase
    have hscalePower (x:ℝ)(hx:x≤ efinal):s.radial.scale*Z^x≤ Z^(s.width+efinal):=by
      rw [s.scale_eq,←Real.rpow_add hz]
      exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by unfold NaturalState.width;linarith [s.character_nonneg])
    have hterm (c A x:ℝ)(hc:0≤ c)(hA:0≤ A)(hx:x≤ efinal):
        c*(plainControl inp (p.profile 0) (p.profile 1))^2*A*s.radial.scale*Z^x≤ c*P*A*F:=by
      calc
        _≤ c*(P*(p.control U)^2)*A*(s.radial.scale*Z^x):=by rw [←mul_assoc];gcongr
        _≤ c*(P*(p.control U)^2)*A*Z^(s.width+efinal):=by gcongr;exact hscalePower x hx
        _≤ c*P*A*F:=by
          calc
            _ = (c*P*A*(p.control U)^2*Z^(s.width+efinal))*1 := by ring
            _ ≤ (c*P*A*(p.control U)^2*Z^(s.width+efinal))*
                (1+|t|+height)^Jout := mul_le_mul_of_nonneg_left hheight1 (by positivity)
            _ = c*P*A*F := by dsimp [F]; ring
    have hdterm:=hterm Cdiag (Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) εdiag hCd.le (apply_nonneg _ _) hdiagFinal
    have htterm:=hterm Ctail (Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ) (-saving) hCt.le (apply_nonneg _ _) htailFinal
    have hrEnv:=henv Ur Jr (e+ε) hr hjr hefinal
    have href:=mul_le_mul_of_nonneg_left hrEnv (show 0≤2*Cr*(K+1)*diagonalControl s.radial.profile by positivity)
    have hsum:=mul_le_mul_of_nonneg_left (add_le_add (add_le_add hmass' hdterm) htterm)
      (show 0≤2*diagonalControl s.radial.profile by positivity)
    have hcoeff:2*Cmass+2*D+2*T+2*Cr*(K+1)≤ Cfixed*(K+Cmass+1):=by
      dsimp [Cfixed]
      nlinarith only [hCu.le,hK,mul_nonneg hCu.le hK,mul_nonneg hCu.le hCmass,mul_nonneg hCr.le hCmass,
        mul_nonneg hD hK,mul_nonneg hD hCmass,mul_nonneg hT hK,mul_nonneg hT hCmass]
    have hfinish:=mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hdg hF)
    apply hsource.trans
    change _≤ Cfixed*(K+Cmass+1)*diagonalControl s.radial.profile*(p.control U)^2*
      (1+|t|+height)^Jout*Z^(s.width+efinal)
    dsimp [D,T,F] at hsum href hfinish
    change _≤_ at hsum
    change 2*Cr*(K+1)*diagonalControl s.radial.profile*((p.control Ur)^2*
      (1+|t|+height)^Jr*Z^(s.width+(e+ε)))≤_ at href
    change 2*diagonalControl s.radial.profile*(_+_+_)+
      2*Cr*(K+1)*diagonalControl s.radial.profile*(p.control Ur)^2*
      (1+|t|+height)^Jr*Z^(s.width+e+ε)≤_
    have hex:s.width+e+ε=s.width+(e+ε):=by ring
    rw [hex]
    nlinarith only [hsum,href,hfinish]

end SevenEighths.Cycle25CenteredMomentEnergyPositiveHighBound

end

end OAI
end
/- END ORIGINAL MODULE Cycle25.Energy.PositiveHighBound -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.BoxGeometry ; sha256 83b0af1bb645fd02f94e7f3e84d68f66a4b6d866f9797bbbb75a09868da528b7 -/
section




/-! Exact scale and capacity bookkeeping for finite coefficient-dilation boxes. -/
noncomputable section
open scoped BigOperators Classical
open Filter
namespace Cycle25.Numerator

lemma physical_y_range (d:ℝ) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension) :
    (1/2:ℝ) < Cycle25.ly/d ∧ Cycle25.ly/d < 1 := by
  have hdp : 0 < d := by linarith
  constructor
  · apply (lt_div_iff₀ hdp).mpr
    have hh := Cycle25.extended_numerator_short
    linarith
  · apply (div_lt_one hdp).mpr
    exact Cycle25.ly_lt_half.trans_le hd

/-- The coarse finite box range suffices: the maximum reflected length remains
below the fixed L=2 empty-slot endpoint, uniformly in all actual high dyads. -/
theorem reflected_box_geometry (d v boxWidth annulusSlack:ℝ)
    (hd:(1/2:ℝ) ≤ d) (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension)
    (hv:0 ≤ v) (hvmax:v ≤ 1+boxWidth) (hbox:0 ≤ boxWidth)
    (hann:0 ≤ annulusSlack) (hsmall:2*boxWidth+annulusSlack ≤ 1/2) :
    0 ≤ 1-Cycle25.ly/d+v+boxWidth ∧
      (1-Cycle25.ly/d+v+boxWidth)+annulusSlack ≤ 2 := by
  obtain ⟨hylo,hyhi⟩ := physical_y_range d hd hdmax
  constructor <;> linarith

/-- A dilation-box upper edge bounds the combined primitive-plus-redundant
conductor relative to the actual original scale Y/N. -/
theorem combined_scale_of_dilation_box (U C Cu rowSize N y v boxWidth:ℝ)
    (hU:0 < U) (hC:0 < C) (hrow:0 < rowSize) (hrowU:rowSize ≤ U) (hN:0 < N)
    (hbox:max 1 (Cu*N/(C*rowSize)) ≤ U^(v+boxWidth)) :
    Cu ≤ C*U^(1-y+v+boxWidth)*(U^y/N) := by
  have hb : Cu*N ≤ U^(v+boxWidth)*(C*rowSize) :=
    (div_le_iff₀ (mul_pos hC hrow)).mp ((le_max_right _ _).trans hbox)
  have hprod : Cu*N ≤ C*(U^(v+boxWidth)*U) := by
    calc
      _ ≤ U^(v+boxWidth)*(C*rowSize) := hb
      _ ≤ U^(v+boxWidth)*(C*U) := by gcongr
      _ = _ := by ring
  have hpow : U^(1-y+v+boxWidth)*U^y = U^(v+boxWidth)*U := by
    rw [←Real.rpow_add hU]
    calc
      _ = U^(v+boxWidth+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hU,Real.rpow_one]
  have he : C*U^(1-y+v+boxWidth)*(U^y/N) =
      (C*(U^(v+boxWidth)*U))/N := by
    calc
      _ = (C*(U^(1-y+v+boxWidth)*U^y))/N := by ring
      _ = _ := by rw [hpow]
  rw [he]
  exact (le_div_iff₀ hN).mpr hprod

lemma capacity_shift_exact (kap y v boxWidth annulusSlack:ℝ) :
    selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) =
      selectedCapacity kap ((2*y-1)/(6*kap)) (v+boxWidth+annulusSlack) := by
  unfold selectedCapacity
  congr 1
  ring

/-- A positive selected family fits the reflected two-plain capacity. If the
capacity has saturated to zero, positivity forces the selected family empty. -/
theorem physical_reflected_capacity_or_empty {ι:Type*} (T:Finset ι)
    (width:ι→ℝ) (kap y v boxWidth annulusSlack:ℝ) (hkap:0< kap)
    (hw:∀i∈T,0 < width i)
    (hselected:(∑i∈T,width i) ≤
      selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth)) :
    2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*(∑i∈T,width i) ≤ 1 ∨ T=∅ := by
  let raw := (2*y-1)/(6*kap)-annulusSlack/(3*kap)-(v+boxWidth)/(3*kap)
  by_cases hraw:0 ≤ raw
  · left
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = raw :=
      max_eq_right hraw
    rw [he] at hselected
    have hid : 2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*raw = 1 := by dsimp [raw]; field_simp; ring
    have hm := mul_le_mul_of_nonneg_left hselected (show 0≤6*kap by positivity)
    linarith
  · right
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = 0 :=
      max_eq_left (le_of_not_ge hraw)
    rw [he] at hselected
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hs := Finset.single_le_sum (fun j hj=>(hw j hj).le) hi
    linarith [hw i hi]

/-- The annular tolerance changes the selected-slot exponent by exactly its
linear capacity cost; it can be included in the final small loss budget. -/
lemma annular_capacity_saving_loss (kap q y annulusSlack:ℝ) :
    -q*((2*y-1)/(6*kap)-annulusSlack/(3*kap))/2 =
      -q*((2*y-1)/(6*kap))/2+q*annulusSlack/(6*kap) := by ring


/-- A convenient uniform positive margin for the selected base capacity. -/
lemma physical_y_strong_lower (d:ℝ) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension) :
    (11/20:ℝ) < Cycle25.ly/d := by
  have hdp : 0 < d := by linarith
  apply (lt_div_iff₀ hdp).mpr
  have hh := Cycle25.h_interval
  have hy := Cycle25.ly_coarse
  norm_num [Cycle25.rowExtension] at *
  linarith

lemma shifted_base_capacity_pos (kap d annulusSlack:ℝ)
    (hkap:0< kap) (hd:(1/2:ℝ) ≤ d)
    (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension)
    (hann:annulusSlack ≤ 1/100) :
    0 < (2*(Cycle25.ly/d)-1)/(6*kap)-annulusSlack/(3*kap) := by
  have hh := physical_y_strong_lower d hd hdmax
  have hid : (2*(Cycle25.ly/d)-1)/(6*kap)-annulusSlack/(3*kap) =
      (2*(Cycle25.ly/d)-1-2*annulusSlack)/(6*kap) := by ring
  rw [hid]
  exact div_pos (by linarith) (by positivity)

def coefficientBoxCount (xi:ℝ) : ℕ := ⌈1/xi⌉₊

lemma coefficientBoxCount_extent (xi:ℝ) (hxi:0 < xi) :
    1 ≤ (coefficientBoxCount xi:ℝ)*xi ∧
      (coefficientBoxCount xi:ℝ)*xi < 1+xi := by
  have hlo := Nat.le_ceil (1/xi)
  have hhi := Nat.ceil_lt_add_one (by positivity:(0:ℝ) ≤ 1/xi)
  constructor
  · have hh := mul_le_mul_of_nonneg_right hlo hxi.le
    simpa only [coefficientBoxCount,div_mul_cancel₀ _ hxi.ne'] using hh
  · have hh := mul_lt_mul_of_pos_right hhi hxi
    dsimp [coefficientBoxCount]
    simpa only [add_mul,div_mul_cancel₀ _ hxi.ne',one_mul] using hh

lemma coefficient_box_index_range (xi:ℝ) (hxi:0 < xi) (j:ℕ)
    (hj:j∈Finset.range (coefficientBoxCount xi+1)) :
    0 ≤ (j:ℝ)*xi ∧ (j:ℝ)*xi ≤ 1+xi := by
  have hjn : j ≤ coefficientBoxCount xi := by have := Finset.mem_range.mp hj; omega
  have hjr : (j:ℝ) ≤ (coefficientBoxCount xi:ℝ) := by exact_mod_cast hjn
  exact ⟨mul_nonneg (Nat.cast_nonneg _) hxi.le,
    (mul_le_mul_of_nonneg_right hjr hxi.le).trans (coefficientBoxCount_extent xi hxi).2.le⟩

/-- A fixed source cutoff fits below U uniformly in every weighted high dyad. -/
theorem eventually_physical_cutoff_le_base (b:ℝ) (hb:0 ≤ b) :
    ∀ᶠU:ℝ in Filter.atTop, 1 < U ∧ ∀d:ℝ,(1/2:ℝ) ≤ d →
      b*U^(Cycle25.ly/d) ≤ U := by
  have he : ∀ᶠU:ℝ in Filter.atTop, b ≤ U^(1/20:ℝ) :=
    (tendsto_rpow_atTop (by norm_num:(0:ℝ)<1/20)).eventually (Filter.eventually_ge_atTop _)
  filter_upwards [he,Filter.eventually_gt_atTop (1:ℝ)] with U he hU
  refine ⟨hU,?_⟩
  intro d hd
  have hdp : 0 < d := by linarith
  have hy : Cycle25.ly/d ≤ 19/20 := by
    apply (div_le_iff₀ hdp).mpr
    linarith [Cycle25.ly_coarse.2]
  calc
    _ ≤ U^(1/20:ℝ)*U^(19/20:ℝ) := by
      exact mul_le_mul he (Real.rpow_le_rpow_of_exponent_le hU.le hy)
        (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
    _ = U := by
      rw [←Real.rpow_add (zero_lt_one.trans hU)]
      norm_num

/-- The finite box range and the reflected scale range use the same actual
parameters; no unbounded coefficient tail remains after the source cutoff. -/
theorem physical_coefficient_box_geometry (d xi annulusSlack:ℝ)
    (hd:(1/2:ℝ) ≤ d) (hdmax:d ≤ Cycle25.h+Cycle25.rowExtension)
    (hxi:0 < xi) (hann:0 ≤ annulusSlack) (hsmall:2*xi+annulusSlack ≤ 1/2)
    (j:ℕ) (hj:j∈Finset.range (coefficientBoxCount xi+1)) :
    0 ≤ 1-Cycle25.ly/d+(j:ℝ)*xi+xi ∧
      (1-Cycle25.ly/d+(j:ℝ)*xi+xi)+annulusSlack ≤ 2 := by
  obtain ⟨hv,hvmax⟩ := coefficient_box_index_range xi hxi j hj
  exact reflected_box_geometry d ((j:ℝ)*xi) xi annulusSlack hd hdmax hv hvmax hxi.le hann hsmall


lemma physical_reflected_capacity_or_empty_subtype {ι:Type*} (T:Finset ι)
    (width:T→ℝ) (kap y v boxWidth annulusSlack:ℝ) (hkap:0< kap)
    (hw:∀i,0 < width i)
    (hselected:(∑i,width i) ≤
      selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth)) :
    2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*(∑i,width i) ≤ 1 ∨ T=∅ := by
  let raw := (2*y-1)/(6*kap)-annulusSlack/(3*kap)-(v+boxWidth)/(3*kap)
  by_cases hraw:0 ≤ raw
  · left
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = raw := max_eq_right hraw
    rw [he] at hselected
    have hid : 2*(1-y+v+boxWidth+annulusSlack)+(6*kap)*raw = 1 := by dsimp [raw]; field_simp; ring
    have hm := mul_le_mul_of_nonneg_left hselected (show 0≤6*kap by positivity)
    linarith
  · right
    have he : selectedCapacity kap ((2*y-1)/(6*kap)-annulusSlack/(3*kap)) (v+boxWidth) = 0 := max_eq_left (le_of_not_ge hraw)
    rw [he] at hselected
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hs := Finset.single_le_sum (fun (j:T) (_:j∈Finset.univ)=>(hw j).le) (Finset.mem_univ (⟨i,hi⟩:T))
    linarith [hw ⟨i,hi⟩]

end Cycle25.Numerator

/- Adapted from weighted numerator PR6, commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.BoxGeometry -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorReconstruction ; sha256 63b458af3d864fa21577b08f227b417e37b7c7cfb8772557758099523a3ec78c -/
section



/-! Exact reconstruction of the actual prime tuples, with finite interchanges
justified before taking any absolute value or splitting rows into amplitudes. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped Classical BigOperators ContDiff
open MeasureTheory Set Complex
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths ProbeHighRowFamily ProbeEuler HeckeFamily ProbePhysical HeckeInverseAmplification
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem image_supported {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (J : Finset (Fin K)) (P : Fin K→HeckeInverseAmplification.PrimeIdeal)
    (hP : ∀i,(P i).val∉S) : ∀Q∈J.image P,Supported Q.val := by
  intro Q hQ
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
  exact outside_prime_supported S hS.bad (P i) (hP i)

theorem partial_image_supported {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (J : Finset (Fin K)) (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (P : ∀i:J,T i.val) :
    ∀Q∈Finset.univ.image (fun i:J=>(P i).val),Supported Q.val := by
  intro Q hQ
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
  exact outside_prime_supported S hS.bad (P i).val (hT i.val _ (P i).property)

theorem calibrated_tuple_kernel_integrable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (P : Fin K→HeckeInverseAmplification.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (hη : ∀i,IsCoprime (P i).val η.modulus)
    (hQ : ∀i,(4:ℝ)≤(P i).val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hmargin : 1+firsteps≤ x.re+1/2)
    (W1 : ℝ→ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W1⊆Icc a b)
    (hW : ContDiff ℝ ∞ W1) (Y : ℝ) (hY : 0< Y) :
    Integrable (fun t : ℝ=>(Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)*
      calibratedTupleValue S hS hmax η u P hPS W Yp x ((1/2:ℂ)+t*Complex.I) z) := by
  have hη' (J : Finset (Fin K)) : ∀Q∈J.image P,IsCoprime Q.val η.modulus := by
    intro Q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hη i
  have hQ' (J : Finset (Fin K)) : ∀Q∈J.image P,(4:ℝ)≤ Q.val.absNorm := by
    intro Q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact hQ i
  have hi (J : Finset (Fin K)) :=
    (weightedErrorTuple_kernel_integrable S hS firsteps hfirst η u hrow J P hP hPS
      (image_supported S hS J P hPS) (hη' J) (hQ' J) W Yp x z hx hz hmargin
      W1 a b ha hsupp hW Y hY).mul_const (physicalMainTuple u J P W Yp z)
  have hsum := (integrable_finsetSum Finset.univ.powerset (fun J _=> hi J)).const_mul
    (numeratorFreeRowScalar S hS hmax η u x z)
  apply hsum.congr
  filter_upwards with t
  rw [calibratedTupleValue_error_subsets firsteps S hS hfirst hmax P hP hPS η u W Yp x
    ((1/2:ℂ)+t*Complex.I) z hx hz (by simp;norm_num) (by simpa using hmargin)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  ring

/-- A literal finite error-label numerator; its coefficients are those reconstructed
from the original row integral. -/
def errorLabelNumerator {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (J : Finset (Fin K))
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ) : ℂ :=
  ∑P:(∀i:J,T i.val),(∏i:J,physicalSlotWeight (P i).val (W i.val) (Yp i.val) z)*
    errorNumeratorIntegral S hS η u (Finset.univ.image (fun i:J=>(P i).val))
      (partial_image_supported S hS J T hT P) x z W1 Y

/-- The normalized full-w integral of the actual calibrated prime tuples equals
its error-label numerators times the remaining, unaltered prime sums. -/
theorem normalized_prime_tuple_reconstruction {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (u : FreeRow)
    (hrow : (rowCharacter S hS.prime u).residue≠1)
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀J : Finset (Fin K),∀P:(∀i:J,T i.val),Function.Injective (fun i=>(P i).val))
    (hdisAll : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hQ : ∀i P,P∈T i→(4:ℝ)≤ P.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hmargin : 1+firsteps≤ x.re+1/2)
    (W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W1⊆Icc a b)
    (Y : ℝ) (hY : 0< Y) :
    (1/(2*Real.pi):ℂ)*(∑P:(∀i,T i),FullWContour.rowNumeratorIntegral S hS hmax η u
      (fun i=>(P i).val) (fun i=> hT i _ (P i).property) W Yp W1 Y x z)=
    numeratorFreeRowScalar S hS hmax η u x z*
      ∑J∈Finset.univ.powerset,errorLabelNumerator S hS η u J T hT W Yp x z W1 Y*
        (∏j:{i:Fin K//i∉J},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Yp j.val) z*
          (-star (idealRowHom u.val P.val.val))) := by
  let kern (t : ℝ) := (Y:ℂ)^(((1/2:ℂ)+t*Complex.I)-1)*mellin W1 ((1/2:ℂ)+t*Complex.I)
  let f (J : Finset (Fin K)) (P : ∀i:J,T i.val) (t : ℝ) :=
    kern t*HeckeOrigin.continued (rowCharacter S hS.prime u) ((1/2:ℂ)+t*Complex.I)*
      partialErrorTuple S hS η u J T hT P W Yp x ((1/2:ℂ)+t*Complex.I) z
  let main (J : Finset (Fin K)) :=
    ∏j:{i:Fin K//i∉J},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Yp j.val) z*
      (-star (idealRowHom u.val P.val.val))
  have hi (P : ∀i,T i) := calibrated_tuple_kernel_integrable S hS hmax firsteps hfirst η u hrow
    (fun i=>(P i).val) (hdisAll P) (fun i=> hT i _ (P i).property)
    (fun i=> hη i _ (P i).property) (fun i=> hQ i _ (P i).property)
    W Yp x z hx hz hmargin W1 a b ha hsupp (W1.smooth ⊤) Y hY
  have hfi (J : Finset (Fin K)) (P : ∀i:J,T i.val) : Integrable (f J P) := by
    apply partialErrorTuple_kernel_integrable S hS firsteps hfirst η u hrow J T hT P (hdis J P)
      (partial_image_supported S hS J T hT P) _ _ W Yp x z hx hz hmargin
      W1 a b ha hsupp (W1.smooth ⊤) Y hY
    · intro Q hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact hη i.val _ (P i).property
    · intro Q hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact hQ i.val _ (P i).property
  have hsum (J : Finset (Fin K)) : Integrable (fun t=>(∑P:(∀i:J,T i.val),f J P t)*main J) :=
    (integrable_finsetSum Finset.univ (fun P _=> hfi J P)).mul_const (main J)
  have he (t : ℝ) :
      (∑P:(∀i,T i),kern t*calibratedTupleValue S hS hmax η u
        (fun i=>(P i).val) (fun i=> hT i _ (P i).property) W Yp x ((1/2:ℂ)+t*Complex.I) z)=
      numeratorFreeRowScalar S hS hmax η u x z*
        ∑J∈Finset.univ.powerset,(∑P:(∀i:J,T i.val),f J P t)*main J := by
    rw [←Finset.mul_sum,calibrated_prime_error_slots_separate firsteps S hS hfirst hmax η u T hT
      hdisAll W Yp x ((1/2:ℂ)+t*Complex.I) z hx hz (by simp;norm_num) (by simpa using hmargin)]
    simp only [Finset.mul_sum,f,main]
    apply Finset.sum_congr rfl
    intro J hJ
    simp only [Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P hP
    ring
  unfold FullWContour.rowNumeratorIntegral
  rw [←integral_finsetSum Finset.univ (fun P _=> hi P)]
  change (1/(2*Real.pi):ℂ)*(∫t : ℝ,∑P:(∀i,T i),kern t*calibratedTupleValue S hS hmax η u
    (fun i=>(P i).val) (fun i=> hT i _ (P i).property) W Yp x ((1/2:ℂ)+t*Complex.I) z)=_
  simp_rw [he]
  rw [integral_const_mul,integral_finsetSum Finset.univ.powerset (fun J _=> hsum J)]
  rw [mul_left_comm,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  rw [integral_mul_const,integral_finsetSum Finset.univ (fun P _=> hfi J P)]
  change (1/(2*Real.pi):ℂ)*((∑P:(∀i:J,T i.val),∫t : ℝ,f J P t)*main J)=_
  rw [←mul_assoc,Finset.mul_sum]
  change (∑P:(∀i:J,T i.val),(1/(2*Real.pi):ℂ)*(∫t : ℝ,f J P t))*main J=_
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  exact partialErrorTuple_mellin S hS η u J T hT P (hdis J P)
    (partial_image_supported S hS J T hT P) W Yp x z W1 Y


def reconstructedDyadValue {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (x z : ℂ) (W1 : ℝ→ℂ) (Y : ℝ) : ℂ :=
  ∑u∈R,frequencyWeight z ⟨u.val,u.property.1⟩ * numeratorFreeRowScalar S hS hmax η u x z *
    ∑J∈Finset.univ.powerset,errorLabelNumerator S hS η u J T hT W Yp x z W1 Y*
      (∏j:{i:Fin K//i∉J},∑P:T j.val,physicalSlotWeight P.val (W j.val) (Yp j.val) z*
        (-star (idealRowHom u.val P.val.val)))

theorem integratedDyadValue_reconstruction {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (firsteps : ℝ) (hfirst : FirstTail firsteps S) (η : Character) (R : Finset FreeRow)
    (hrow : ∀u∈R,(rowCharacter S hS.prime u).residue≠1)
    (T : Fin K→Finset HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀J : Finset (Fin K),∀P:(∀i:J,T i.val),Function.Injective (fun i=>(P i).val))
    (hdisAll : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hQ : ∀i P,P∈T i→(4:ℝ)≤ P.val.absNorm)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (x z : ℂ)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (hmargin : 1+firsteps≤ x.re+1/2)
    (W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hsupp : Function.support W1⊆Icc a b)
    (Y : ℝ) (hY : 0< Y) :
    FullWContour.integratedDyadValue S hS hmax η R T hT W Yp W1 Y x z=
      (2*Real.pi:ℂ)*reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y := by
  have he : (1/(2*Real.pi):ℂ)*FullWContour.integratedDyadValue S hS hmax η R T hT W Yp W1 Y x z=
      reconstructedDyadValue S hS hmax η R T hT W Yp x z W1 Y := by
    unfold FullWContour.integratedDyadValue reconstructedDyadValue
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    simp only [FullWContour.integratedRowValue,←Finset.mul_sum]
    rw [mul_left_comm,normalized_prime_tuple_reconstruction S hS hmax firsteps hfirst η u
      (hrow u hu) T hT hdis hdisAll hη hQ W Yp x z hx hz hmargin W1 a b ha hsupp Y hY]
    ring
  have hc : (2*Real.pi:ℂ)*(1/(2*Real.pi):ℂ)=1 := by
    apply mul_one_div_cancel
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  calc
    _ = (2*Real.pi:ℂ)*((1/(2*Real.pi):ℂ)*FullWContour.integratedDyadValue
        S hS hmax η R T hT W Yp W1 Y x z) := by rw [←mul_assoc,hc,one_mul]
    _ = _ := by rw [he]

end Cycle25.Weighted.Numerator
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.Imported.NumeratorReconstruction -/

/- BEGIN ORIGINAL MODULE Cycle25.Numerator.PacketBoxes ; sha256 1534bb07bb9de5d470ac5fa18390dce092b0b18b4430401c9ed135c1ac35998b -/
section


/-! Coefficient removal inside a finite dilation box. The polynomial moment
is applied only to active coefficient choices; the resulting packet is
normalized by its actual absolute coefficient mass. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace Cycle25.Numerator
open Cycle25.Weighted Cycle25.Weighted.Numerator

variable {ι : Type*} [Fintype ι] {α : ι → Type*}

theorem packet_box_fourth
    (base : ∀ i, α i) (A S : ∀ i, α i → ℂ) (N : ∀ i, α i → ℝ)
    (hN : ∀ i e, 0 < N i e) (L : ι → ℝ) (rho U v : ℝ)
    (active : ∀ i, α i → Prop) [∀ i e, Decidable (active i e)]
    (Q : ι → ℂ) (M E : ℝ) (hM : 0 < M) (hU : 0 < U) (hrho : 0 ≤ rho)
    (hlower : ∀ i e, active i e → U^v ≤ max 1 (L i * N i e))
    (hs : ∀ i, Summable (fun e => ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho))
    (hm : ∀ i, (∑' e, ‖A i e‖ * (N i e)^(-(1 / 2 : ℝ)) *
      max 1 (L i * N i e)^rho) ≤ M)
    (hselection : ∀ e : ∀ i, α i,
      (∑ i, ‖if active i (e i) then S i (e i) else 0‖^4 * ‖Q i‖^2) ≤ E) :
    (∑ i, ‖((U^(rho*v) / M : ℝ) : ℂ) *
      (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) *
        (if active i e then S i e else 0))‖^4 * ‖Q i‖^2) ≤ E := by
  let B (i : ι) (e : α i) := if active i e then S i e else 0
  let T (i : ι) (e : α i) := ((U^(rho*v) : ℝ) : ℂ) * B i e
  have hfactor (i : ι) (e : α i) :
      ‖T i e / ((max 1 (L i * N i e)^rho : ℝ) : ℂ)‖ ≤ ‖B i e‖ := by
    by_cases ha : active i e
    · have hD : 0 < max 1 (L i * N i e)^rho :=
        Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
      have hpow : U^(rho*v) ≤ max 1 (L i * N i e)^rho := by
        calc
          _ = (U^v)^rho := by rw [←Real.rpow_mul hU.le]; congr 1; ring
          _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hU.le _) (hlower i e ha) hrho
      dsimp only [T]
      rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hU.le _),
        Complex.norm_real,Real.norm_of_nonneg hD.le]
      exact (div_le_iff₀ hD).mpr (by nlinarith [norm_nonneg (B i e)])
    · simp [T,B,ha]
  have hsel : ∀ e : ∀ i, α i,
      (∑ i, ‖T i (e i) / ((max 1 (L i * N i (e i))^rho : ℝ) : ℂ)‖^4 * ‖Q i‖^2) ≤ E := by
    intro e
    refine (Finset.sum_le_sum (fun i _ => ?_)).trans (hselection e)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hfactor i (e i)) 4) (sq_nonneg _)
  have hp := packet_fourth_selection base A T N hN L rho Q M E hM.le hs hm hsel
  have he (i : ι) :
      (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * T i e) =
      ((U^(rho*v) : ℝ) : ℂ) * (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * B i e) := by
    rw [←tsum_mul_left]
    apply tsum_congr
    intro e
    dsimp only [T]
    ring
  simp only [he] at hp
  have hnorm (i : ι) :
      ‖((U^(rho*v) / M : ℝ) : ℂ) * (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * B i e)‖^4 * ‖Q i‖^2 =
      (‖((U^(rho*v) : ℝ) : ℂ) * (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * B i e)‖^4 * ‖Q i‖^2) / M^4 := by
    rw [Complex.ofReal_div]
    have hmul (z : ℂ) : (((U^(rho*v) : ℝ) : ℂ) / (M : ℂ)) * z = (((U^(rho*v) : ℝ) : ℂ)*z)/(M : ℂ) := by ring
    rw [hmul,norm_div,Complex.norm_real,Real.norm_of_nonneg hM.le,div_pow]
    ring
  change (∑ i, ‖((U^(rho*v) / M : ℝ) : ℂ) * (∑' e, A i e * (N i e : ℂ)^(-(1 / 2 : ℂ)) * B i e)‖^4 * ‖Q i‖^2) ≤ E
  simp_rw [hnorm]
  rw [←Finset.sum_div]
  exact (div_le_iff₀ (pow_pos hM 4)).mpr (by simpa only [mul_comm E] using hp)

end Cycle25.Numerator

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 generalizes the moment parameter and retains explicit mesh losses. -/
end
/- END ORIGINAL MODULE Cycle25.Numerator.PacketBoxes -/
