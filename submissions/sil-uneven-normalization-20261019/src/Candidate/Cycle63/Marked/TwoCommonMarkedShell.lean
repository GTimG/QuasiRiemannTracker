import Candidate.Cycle63.Marked.ProfileMarkedShell
import Candidate.Cycle63.Physical.InitialMass.SecondHighShell
import Candidate.Cycle63.Physical.InitialMass.SecondSourceControls

/- Original module: Candidate.Cycle63.Marked.ProfileMarkedFamily. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle63Moment
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle63HighResidual Cycle63HighProfiles CenteredMomentFiniteProfileExceptional
open Cycle63FinalLow CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The actual residual shell contracts before the weighted row count. All
outer geometric coefficients and varying common-volume exponents remain
inside one literal sum of natural slot weights. -/
theorem actual_profile_marked_weighted_family {Index : Type} [Fintype Index]
    (Slots : Index→Type) [∀l,Fintype (Slots l)] [∀l,DecidableEq (Slots l)]
    (N : ℕ) (hN : ∀l,Fintype.card (Slots l)≤N)
    (P : HighSourceParameters) (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀a : ℝ,51/100≤a→a≤1→∀i : ℕ,
      ∀{Row : Type}(labels : Finset Row)(S : Row→Index)
        (s : ∀l,Data (Slots (S l)))
        (st : Row→NaturalState Z P.Bmask P.bΦ)
        (hQM : ∀l,(st l).fixedModulus≤M)(hQη : ∀l,(st l).fixedModulus≤η₀.modulus)
        (z : Row→O)(hz : ∀l,(st l).radial.keep (z l))
        (w σ v : ∀l,Slots (S l)→ℝ)(θ : ∀l,Slots (S l)→RayQuotient.Characters M H),
      ∀F G : Finset (ℕ×ℕ),(0,0)∈F→∀p : Row→Profiles ap bp,
      (∀l∈labels,(s l).W₁=((p l).profile 0:ℝ→ℂ) ∧ (s l).W₂=((p l).profile 1:ℝ→ℂ) ∧
        (s l).b₁=bp ∧ (s l).b₂=bp)→
      ∀Ds : Row→Finset (Ideal O),(∀l∈labels,∀L∈Ds l,Squarefree L)→
      ∀(T Cprofile Kcontrol allowance : ℝ)(e coeff : Row→ℝ),
      1≤T→0≤Cprofile→0≤Kcontrol→(∀l∈labels,0≤coeff l)→
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T)→
      (∀l∈labels,((p l).control G)^2*(wholeControl (s l))^2≤Kcontrol)→
      (∀l∈labels,(s l).toSource.allowance Z+
        Cycle63.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂]≤allowance)→
      (∀l∈labels,∀L∈Ds l,∀alloc∈(s l).toSource.active L,∀b : Bool,
        Cycle63.Physical.sourcePositiveRow (s l).toSource b L alloc (z l)≠0→
        HighSourceAdmissible hH P η₀ Z a i n
          (profileWholeDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
            (s l) b L alloc (w l) (σ l) (v l) (θ l) hap F (p l)))→
      (∀l∈labels,∀L∈Ds l,∀alloc∈(s l).toSource.active L,∀b : Bool,
        clippedControl hap F (p l) (profileScales (s l) b L alloc)
          (profile_scales_pos (s l) b L alloc) 0*
        clippedControl hap F (p l) (profileScales (s l) b L alloc)
          (profile_scales_pos (s l) b L alloc) 1≤Cprofile*(p l).control G)→
      (∀l∈labels,(2*a-1)*(Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume (s l))-
        ∑k,w l k)+2*P.εplain*P.d≤e l)→
      (∑l∈labels,coeff l*(∑L∈Ds l,∑alloc∈(s l).toSource.active L,
        retainedAllocationCost (s l) L alloc (z l)))≤
      C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^allowance*
        ∑l∈labels,coeff l*Z^(e l)*
          retainedSourceSlotWeight M H hH P η₀ Z (st l) (z l) (hz l)
            (w l) (σ l) (v l) (θ l) (s l).t := by
  obtain ⟨n,C,hC,hactual⟩:=actual_profile_marked_retained_family M H hH Slots N hN P ε hε hap
  refine ⟨n,C,hC,?_⟩
  intro η₀
  filter_upwards [hactual η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro a ha ha' i Row labels S s st hQM hQη z hz w σ v θ F G hF p hWsrc Ds hDs
    T Cprofile Kcontrol allowance e coeff hT hCprofile hKcontrol hcoeff hdyad hcontrol
    hallowance hvalid hprofile hexp
  have hzpos : 0<Z:=zero_lt_one.trans hZ.1
  let K:=C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^allowance
  have hK : 0≤K:=by dsimp [K];positivity
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l hl
  have hr:=hZ.2 a ha ha' i (S l) (s l) (st l) (hQM l) (hQη l) (z l) (hz l)
    (w l) (σ l) (v l) (θ l) F G hF (p l) (hWsrc l hl).1 (hWsrc l hl).2.1
    (hWsrc l hl).2.2.1 (hWsrc l hl).2.2.2 (Ds l) (hDs l hl) T (e l) Cprofile hT hCprofile
    (fun L hL=>(hdyad l hl L hL).1) (fun L hL=>(hdyad l hl L hL).2)
    (hvalid l hl) (hprofile l hl) (hexp l hl)
  let wt:=retainedSourceSlotWeight M H hH P η₀ Z (st l) (z l) (hz l)
    (w l) (σ l) (v l) (θ l) (s l).t
  have hwt : 0≤wt:=Finset.prod_nonneg (fun _ _=>sq_nonneg _)
  have hp : Z^(e l+(s l).toSource.allowance Z+
      Cycle63.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂])≤Z^(e l+allowance):=
    Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith [hallowance l hl])
  have hbound : (∑L∈Ds l,∑alloc∈(s l).toSource.active L,
      retainedAllocationCost (s l) L alloc (z l))≤K*Z^(e l)*wt := by
    apply hr.trans
    calc
      _=(C*Cprofile^2)*(((p l).control G)^2*(wholeControl (s l))^2)*
        (2*T)^(2*ε)*Z^(e l+(s l).toSource.allowance Z+
          Cycle63.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂])*wt:=by ring
      _≤(C*Cprofile^2)*Kcontrol*(2*T)^(2*ε)*Z^(e l+allowance)*wt := by
        gcongr
        exact hcontrol l hl
      _=K*Z^(e l)*wt := by
        rw [Real.rpow_add hzpos]
        dsimp [K]
        ring
  have hh:=mul_le_mul_of_nonneg_left hbound (hcoeff l hl)
  convert hh using 1 <;> ring

end
end OAI.SevenEighths.Cycle63Moment
#print axioms OAI.SevenEighths.Cycle63Moment.actual_profile_marked_weighted_family
end

/- Original module: Candidate.Cycle63.Marked.CommonMarkedShell. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle63Moment
local notation "O"=>HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Literal common children, their actual profile admission and all residual
allocations reduce to the common slot weighted row sum. No analytic moment
or row-admissibility predicate remains among the input gates. -/
theorem actual_common_marked_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character) (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧
      ∀P : HighSourceParameters,P.profileBound=bound→
      8*P.τ≤P.d*P.vslot→16*P.τ≤P.d*P.vplain→
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧ ∀{Row : Type}(labels : Finset Row)
        (st : Row→NaturalState Z P.Bmask P.bΦ)
        (hQM : ∀l,(st l).fixedModulus≤M)(hQη : ∀l,(st l).fixedModulus≤η₀.modulus)
        (z : Row→O)(hz : ∀l,(st l).radial.keep (z l)),
      ∀(a allowance Kcontrol T : ℝ)(i : ℕ),51/100≤a→a≤1→0≤Kcontrol→1≤T→
      (i:ℝ)≤Z^P.τ→
      ∀(S : Row→Finset α)(s : ∀l,Input (S l))(E R : Row→Ideal O)
        (pick : ∀l,actualAllocations (s l).pools (E l))(t : Row→ℝ)
        (w σ v : ∀l,S l→ℝ)(θ : ∀l,S l→RayQuotient.Characters M H)
        (p : Row→Profiles ap bp)(Ds : Row→Finset (Ideal O))(cap : ℝ),
      cap≤P.d*P.Rplain→
      (∀l∈labels,Matches M H hH (s l) η₀ (θ l) (w l) (σ l) (v l) P.Wslot P.B₀ Z)→
      (∀l∈labels,∀second j,Cycle63.Physical.sourcePlainScales (s l).toData.toSource second j≤Z^cap)→
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R l*E l))→
      (∀l∈labels,(st l).width≤P.Mcap)→
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0)→
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e)→
      (∀l∈labels,∀j,0≤w l j)→(∀l∈labels,∀j,w l j/P.d≤P.Rwidth)→
      (∀l∈labels,∀j,P.σmin≤σ l j)→(∀l∈labels,∀j,σ l j≤P.σmax)→
      (∀l∈labels,∀j,|t l+v l j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ)→
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ)→
      (∀l∈labels,(s l).W₁=((p l).profile 0:ℝ→ℂ) ∧
        (s l).W₂=((p l).profile 1:ℝ→ℂ) ∧ (s l).b₁=bp ∧ (s l).b₂=bp)→
      (∀l∈labels,∀L∈Ds l,Squarefree L)→
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T)→
      let src:=fun l=>commonData (withHeight (s l) (st l).character (t l)) (E l) (R l) (pick l)
      ∀coeff e : Row→ℝ,(∀l∈labels,0≤coeff l)→
      (∀l∈labels,((p l).control G)^2*(wholeControl (src l))^2≤Kcontrol)→
      (∀l∈labels,(src l).toSource.allowance Z+
        Cycle63.Physical.plainClipAllowance Z ![(src l).b₁,(src l).b₂]≤allowance)→
      (∀l∈labels,(2*a-1)*(Real.logb Z (preVolume (src l))-
        ∑k : CenteredMomentCommonProfile.liveIndices (pick l).val,w l k.val)+
          2*P.εplain*P.d≤e l)→
      (∑l∈labels,coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l)))≤
      C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^allowance*
        ∑l∈labels,coeff l*Z^(e l)*retainedSourceSlotWeight M H hH P η₀ Z
          (st l) (z l) (hz l) (fun k : CenteredMomentCommonProfile.liveIndices (pick l).val=>w l k.val)
          (fun k=>σ l k.val) (fun k=>v l k.val) (fun k=>θ l k.val) (t l) := by
  obtain ⟨bound,hbound,hadmit⟩:=eventual_common_profile_admission M H hH hap
  let Slots:=fun l : (S : Finset α)×Finset S=>↥l.2
  have hN (l : (S : Finset α)×Finset S) : Fintype.card (Slots l)≤Fintype.card α := by
    simpa only [Slots,Fintype.card_coe] using
      (Finset.card_le_univ l.2).trans (by simpa using Finset.card_le_univ l.1)
  refine ⟨bound,hbound,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨n,C,hC,henergy⟩:=actual_profile_marked_weighted_family M H hH Slots
    (Fintype.card α) hN P ε hε hap
  obtain ⟨F,G,Cprofile,hF,hCprofile,hprofile,hadmit⟩:=hadmit n
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [henergy η₀,hadmit P hboundeq hslot hplain η₀,eventually_ge_atTop (2:ℝ)] with Z he hn hZ2
  refine ⟨hZ2,?_⟩
  intro Row labels st hQM hQη z hz a allowance Kcontrol T i ha ha' hK hT hi
    S s E R pick t w σ v θ p Ds cap hcap hmatches hscales hstateMask hwidth hradial hupper
    hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src coeff e hcoeff hcontrol hallowance hraw
  apply he.2 a ha ha' i labels (fun l=>⟨S l,CenteredMomentCommonProfile.liveIndices (pick l).val⟩)
    src st hQM hQη z hz
    (fun l j=>w l j.val) (fun l j=>σ l j.val) (fun l j=>v l j.val) (fun l j=>θ l j.val)
    F G hF p hW Ds hDs T Cprofile Kcontrol allowance e coeff hT hCprofile.le hK hcoeff
    hdyad hcontrol hallowance
  · intro l hl L hL alloc haL second hne
    exact hn.2 a (t l) cap i (by linarith) hi hcap (s l) (θ l) (w l) (σ l) (v l)
      (hmatches l hl) (hscales l hl) (E l) (R l) (pick l) (st l) (hQM l) (hQη l)
      (z l) (hz l) (hstateMask l hl) (hwidth l hl) (hradial l hl) (hupper l hl)
      (hw l hl) (hwr l hl) (hσlo l hl) (hσhi l hl) (hfreq l hl) (hplainfreq l hl)
      second L alloc (p l) (hW l hl).1 (hW l hl).2.1 (hW l hl).2.2.1 (hW l hl).2.2.2 hne
  · intro l hl L hL alloc haL second
    exact hprofile (p l) _ _
  · exact hraw

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_common_marked_shell
end

/- Original module: Candidate.Cycle63.Marked.TwoCommonMarkedShell. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle63Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Both literal common allocations retain the complete surviving slot product
in the row sum. Raw volume, analytic controls and clipping allowances are
transported from the original input. -/
theorem actual_two_common_marked_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character) (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ : Type} (labels : Finset κ),
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l)),
      ∀ (a allowance Kcontrol T : ℝ) (i : ℕ),
      51/100 ≤ a → a ≤ 1 → 0 ≤ Kcontrol → 1 ≤ T →
      (i:ℝ)≤Z^P.τ →
      ∀(s : Input α),Fintype.card α≤N → (∀j,s.M j≤Cs) →
      s.b₁≤bs → s.b₂≤bs → s.upper≤b →
      (∀j,logWindow (s.lo j) (s.hi j)≤window) →
      ∀(C₁ R₁ : κ→Ideal O)(B₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→Character)(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) (R₁ l) s.ν s.W s.P≠0) →
      let first := fun l=>child s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      ∀(E R : κ→Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap Araw : ℝ),
      cap≤P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
      Real.logb Z (preVolume s.toData)≤Araw → pad≤allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R l)
        (first l).ν (first l).W (first l).P≠0) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R l*E l)) →
      (∀l∈labels,(st l).width≤P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)<a+2*P.e) →
      (∀j,0≤w j) → (∀j,w j/P.d≤P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (first l) (st l).character (t l)) (E l) (R l) (pick l)
      ∀coeff : κ→ℝ,(∀l∈labels,0≤coeff l)→
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤Kcontrol) →
      (∑l∈labels,coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l)))≤
      C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^allowance*
        ∑l∈labels,coeff l*
          Z^((2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
            Real.logb Z ((E l).absNorm:ℝ)-
            ∑k : CenteredMomentCommonProfile.liveIndices (pick l).val,w k.val.val)+
            pad+2*P.εplain*P.d)*
          retainedSourceSlotWeight M H hH P η₀ Z (st l) (z l) (hz l)
            (fun k : CenteredMomentCommonProfile.liveIndices (pick l).val=>w k.val.val)
            (fun k=>σ k.val.val) (fun k=>v k.val.val) (fun k=>θ k.val.val) (t l) := by
  obtain ⟨bound,hbound,hboundJoint⟩ := actual_common_marked_shell
    (α:=α) (bp:=bp) M H hH η₀ ε hε hap
  refine ⟨bound,hbound,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hboundJoint P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint,eventual_two_common_allowance N window bs pad hwindow hbs hpad,
    eventually_two_stage_padding N b pad hb hpad] with Z he hallow hpadding
  refine ⟨he.1,?_⟩
  intro κ labels st hQM hQη z hz a allowance Kcontrol T i ha ha' hK hT
    hi s hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ first
    E R pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src coeff hcoeff hcontrol
  apply he.2 labels st hQM hQη z hz a allowance Kcontrol T i ha ha' hK hT
    hi (fun l=>liveIndices (B₁ l).val) first E R pick t
    (fun _ j=>w j.val) (fun _ j=>σ j.val) (fun _ j=>v j.val) (fun _ j=>θ j.val)
    p Ds cap hcap
    (fun l _=>actual_child_matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z hmatches
      (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l))
    (fun l _ second j=>(actual_child_plain_scale_le s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      second j).trans (hscales second j))
    hstateMask hwidth hradial hupper (fun _ _ j=>hw j.val) (fun _ _ j=>hwr j.val)
    (fun _ _ j=>hσlo j.val) (fun _ _ j=>hσhi j.val)
    (fun l hl j=>hfreq l hl j.val) hplainfreq hW hDs hdyad coeff
      (fun l=>(2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
        Real.logb Z ((E l).absNorm:ℝ)-
        ∑k : CenteredMomentCommonProfile.liveIndices (pick l).val,w k.val.val)+
        pad+2*P.εplain*P.d) hcoeff
  · intro l hl
    have hc := actual_two_common_control_fixed N Cs bs hCs hbs s hcard hM hb₁ hb₂
      (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l) (E l) (R l) (pick l) (st l).character (t l)
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (wholeControl_nonneg (src l)) hc 2) (sq_nonneg _)).trans (hcontrol l hl)
  · intro l hl
    exact (hallow.2 s hcard hwin hb₁ hb₂ (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      (E l) (R l) (pick l) (st l).character (t l)).trans hpadallow
  · intro l hl
    have hr := actual_two_stage_raw_log N b hb s hcard hupperB (C₁ l) (R₁ l) (B₁ l)
      (hf₁ l hl) (χ₁ l) (t₁ l) (E l) (R l) (pick l) (hf₂ l hl) Z hpadding.1
    have hr' : Real.logb Z (preVolume (src l))≤
        Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-Real.logb Z ((E l).absNorm:ℝ)+pad := by
      change Real.logb Z (preVolume (commonData (first l) (E l) (R l) (pick l)))≤_
      linarith [hpadding.2]
    have hδ : 0≤2*a-1 := by linarith
    have hδ' : 2*a-1≤1 := by linarith
    have hh := mul_le_mul_of_nonneg_left hr' hδ
    have hloss := mul_le_mul_of_nonneg_right hδ' hpad.le
    nlinarith

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_two_common_marked_shell
end
