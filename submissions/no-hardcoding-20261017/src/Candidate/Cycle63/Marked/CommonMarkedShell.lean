import Candidate.Cycle63.Physical.InitialMass.SecondHighShell
import Candidate.Cycle63.Marked.ProfileMarkedFamily

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
