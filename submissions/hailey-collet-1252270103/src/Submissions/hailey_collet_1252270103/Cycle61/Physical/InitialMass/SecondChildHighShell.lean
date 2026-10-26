import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondSelectedHighShell
import Submissions.hailey_collet_1252270103.Cycle61.Physical.InitialMass.SecondSourceControls

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonHeightEnvelope CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentRetainedProfile
open Cycle61HighProfiles Cycle61FinalLow CenteredMomentFiniteProfileExceptional
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
open CenteredMomentAllocatedChildCapacity Cycle61Moment
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The high-shell bound applied to literal first common children. All
slot matching, plain-scale caps, analytic controls and clipping allowances
come from the original input. Both supported allocations pay their raw
common-ideal shifts; no affine condition is imposed on a descendant. -/
theorem actual_child_selected_high_shell {α Base : Type} [Fintype α] [DecidableEq α]
    [Fintype Base] (base : Base→Character) (η₀ : Character)
    (B Q loss ε : ℝ) (hB : 0≤B) (hQ : 0≤Q) (hQB : Q≤B)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ : Type}[Nonempty κ],
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a e allowance Kcontrol T : ℝ) (i : ℕ),
      q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ (key : κ→NonzeroJointSourceLabel left u₀ unit), Function.Injective key →
      ∀ labels : Finset κ,
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (index : κ → Base)
        (holes : κ → Ideal O),
      (∀ l ∈ labels, holes l ≠ 0) →
      (∀ l ∈ labels, ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow (st l).character (z l)
          ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) I =
        idealCoeff (excluded (naturalRow (base (index l)) (nonzeroJointSourceRow (key l)).val
          (nonzeroJointSourceRow (key l)).property).character (holes l)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow (key l)) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, Supported (key l).val.1.1.1 ∧ (key l).val.1.1.2 ≠ 0 ∧
        Supported (key l).val.2.1.1 ∧ (key l).val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport (key l).val.1.1.1 = primeSupport (key l).val.1.1.2 ∧
        primeSupport (key l).val.2.1.1 = primeSupport (key l).val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((key l).val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        ((key l).val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        ((key l).val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ ((key l).val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^m) →
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
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤Z^cap) →
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
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤Kcontrol) →
      (∀l∈labels,(2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
        Real.logb Z ((E l).absNorm:ℝ))+pad+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤e) →
      (∑l∈labels,∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l))≤
      C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
        Z^(m+q*unmarkedDensity (2*a-1)+loss+e+allowance) := by
  obtain ⟨bound,hbound,J,hboundJoint⟩ := actual_common_selected_high_shell
    (α:=α) (bp:=bp) M H hH base η₀ B Q loss ε hB hQ hQB hloss hε hap
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hboundJoint P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint,eventual_two_common_allowance N window bs pad hwindow hbs hpad,
    eventually_two_stage_padding N b pad hb hpad] with Z he hallow hpadding
  refine ⟨he.1,?_⟩
  intro κ _ left u₀ unit q m a e allowance Kcontrol T i hq ha ha' hK hT
    key hinj labels st hQM hQη z hz index holes hholes hmask hzero hsupported heq hsupport hnorm hmissing
    hi s hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ first
    E R pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hledger
  apply he.2 left u₀ unit q m a e allowance Kcontrol T i hq ha ha' hK hT
    key hinj labels st hQM hQη z hz index holes hholes hmask hzero hsupported heq hsupport hnorm hmissing
    hi (fun l=>liveIndices (B₁ l).val) first E R pick t
    (fun _ j=>w j.val) (fun _ j=>σ j.val) (fun _ j=>v j.val) (fun _ j=>θ j.val)
    p Ds cap hcap
    (fun l _=>actual_child_matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z hmatches
      (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l))
    (fun l _ second j=>(actual_child_plain_scale_le s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      second j).trans (hscales second j))
    hstateMask hwidth hradial hupper (fun _ _ j=>hw j.val) (fun _ _ j=>hwr j.val)
    (fun _ _ j=>hσlo j.val) (fun _ _ j=>hσhi j.val)
    (fun l hl j=>hfreq l hl j.val) hplainfreq hW hDs hdyad
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
    have hg := hledger l hl
    nlinarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_child_selected_high_shell
