import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.ProfileJointShellEnergy
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.ProfileCommonAdmissible
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.HighRawExponent
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Moment.WholeSourceDatum
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.HighResidualAllocation
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators HeckeNotation
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle63HighProfiles Cycle63FinalLow CenteredMomentFiniteProfileExceptional
open Cycle63HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle63Moment
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The pointwise bound on the literal common-allocated sources. Normalization, conductor, truncated heights and
residual clipping are derived, with the budget chosen before all live slot subsets and common allocations; the energy
is at most the pointwise bound times the number of labels. -/
theorem actual_common_joint_high_shell {α : Type} [Fintype α] [DecidableEq α] (η₀ : Character)
    (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (a e allowance Kcontrol T : ℝ) (i : ℕ),
      4/5 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ st : NonzeroJointSourceLabel left u₀ unit → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : NonzeroJointSourceLabel left u₀ unit → O) (hz : ∀ l, (st l).radial.keep (z l)),
      (i:ℝ)≤Z^P.τ →
      ∀(S : NonzeroJointSourceLabel left u₀ unit→Finset α)
        (s : ∀l,Input (S l))
        (E R : NonzeroJointSourceLabel left u₀ unit→ Ideal O)
        (pick : ∀l,actualAllocations (s l).pools (E l))
        (t : NonzeroJointSourceLabel left u₀ unit→ℝ)
        (w σ v : ∀l,S l→ℝ)(θ : ∀l,S l→RayQuotient.Characters M H)
        (p : NonzeroJointSourceLabel left u₀ unit→Profiles ap bp)
        (Ds : NonzeroJointSourceLabel left u₀ unit→Finset (Ideal O)) (cap : ℝ),
      cap≤P.d*P.Rplain →
      (∀l∈labels,Matches M H hH (s l) η₀ (θ l) (w l) (σ l) (v l) P.Wslot P.B₀ Z) →
      (∀l∈labels,∀second j,Cycle63.Physical.sourcePlainScales (s l).toData.toSource second j≤Z^cap) →
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
      (∀l∈labels,∀j,0≤w l j) → (∀l∈labels,∀j,w l j/P.d≤P.Rwidth) →
      (∀l∈labels,∀j,P.σmin≤σ l j) → (∀l∈labels,∀j,σ l j≤P.σmax) →
      (∀l∈labels,∀j,|t l+v l j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,(s l).W₁=((p l).profile 0:ℝ→ℂ) ∧
        (s l).W₂=((p l).profile 1:ℝ→ℂ) ∧ (s l).b₁=bp ∧ (s l).b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (s l) (st l).character (t l)) (E l) (R l) (pick l)
      (∀l∈labels,((p l).control G)^2*(wholeControl (src l))^2≤Kcontrol) →
      (∀l∈labels,(src l).toSource.allowance Z+
        Cycle63.Physical.plainClipAllowance Z ![(src l).b₁,(src l).b₂]≤allowance) →
      (∀l∈labels,(2*a-1)*Real.logb Z (preVolume (src l))+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤e) →
      (∑l∈labels,∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l))≤
      C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^(e+allowance)*labels.card := by
  obtain ⟨bound,hbound,hadmit⟩ := eventual_common_profile_admission M H hH hap
  let Slots := fun l : (S : Finset α) × Finset S=>↥l.2
  have hN (l : (S : Finset α) × Finset S) : Fintype.card (Slots l)≤Fintype.card α := by
    simpa only [Slots,Fintype.card_coe] using
      (Finset.card_le_univ l.2).trans (by simpa using Finset.card_le_univ l.1)
  have hjoint := actual_profile_joint_family_energy (bp := bp) M H hH Slots (Fintype.card α) hN η₀ ε hε hap
  refine ⟨bound,hbound,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨n,C,hC,henergy⟩ := hjoint P
  obtain ⟨F,G,Cprofile,hF,hCprofile,hprofile,hadmit⟩ := hadmit n
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [henergy,hadmit P hboundeq hslot hplain η₀] with Z he hn
  refine ⟨he.1,?_⟩
  intro left u₀ unit a e allowance Kcontrol T i ha ha' hK hT
    labels st hQM hQη z hz
    hi S s E R pick t w σ v θ p Ds cap hcap hmatches hscales hstateMask hwidth hradial hupper
    hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hallowance hraw
  apply he.2 left u₀ unit a e allowance Kcontrol T i ha ha' hK hT
    labels st hQM hQη z hz
    F G hF Cprofile hCprofile.le p
    (fun l=>⟨S l,CenteredMomentCommonProfile.liveIndices (pick l).val⟩) src
    (fun l j=>w l j.val) (fun l j=>σ l j.val) (fun l j=>v l j.val)
    (fun l j=>θ l j.val) Ds hW hDs hdyad hcontrol hallowance
  · intro l hl L hL alloc haL second hne
    exact hn.2 a (t l) cap i (by linarith) hi hcap (s l) (θ l) (w l) (σ l) (v l)
      (hmatches l hl) (hscales l hl) (E l) (R l) (pick l) (st l) (hQM l) (hQη l)
      (z l) (hz l) (hstateMask l hl) (hwidth l hl) (hradial l hl) (hupper l hl)
      (hw l hl) (hwr l hl) (hσlo l hl) (hσhi l hl) (hfreq l hl) (hplainfreq l hl)
      second L alloc (p l) (hW l hl).1 (hW l hl).2.1 (hW l hl).2.2.1 (hW l hl).2.2.2 hne
  · intro l hl L hL alloc haL second
    exact hprofile (p l) _ _
  · intro l hl L hL alloc haL second
    let D := wholeHighDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
      (src l) second L alloc (fun j=>w l j.val) (fun j=>σ l j.val) (fun j=>v l j.val)
      (fun j=>θ l j.val) ap bp
    have hd := high_source_exponent_le_raw D hn.1
      (fun j=>(hmatches l hl).scale j.val) (fun j=>hw l hl j.val)
      (2*a-1) (by linarith) (by linarith)
    have hr := hraw l hl
    change (2*a-1)*D.total P-Cycle63.Physical.sourcePostClip (src l).toSource second Z L alloc≤
      (2*a-1)*Real.logb Z (preVolume (src l)) at hd
    change (2*a-1)*D.total P+2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)-
      Cycle63.Physical.sourcePostClip (src l).toSource second Z L alloc≤e
    linarith

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
