import Candidate.Cycle63.Marked.TwoCommonMarkedShell
import Candidate.Cycle63.Marked.RetainedFamilyDiscard
import Candidate.Cycle63.Marked.RetainedSlotCaps
import Candidate.Cycle63.Physical.InitialMass.SecondSourceControls

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
open CenteredMomentAmplificationChildInput CenteredMomentCommonProfile
open CenteredMomentSlotRatios CenteredMomentSourceLiveColumn
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Both literal common allocations retain the complete surviving slot product
in the row sum. Raw volume, analytic controls and clipping allowances are
transported from the original input. -/
theorem actual_two_common_large_slot_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character) (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap)
    (N : ℕ)(Cs bs b window pad : ℝ)
    (hCs : 1≤Cs)(hbs : 1≤bs)(hb : 1≤b)(hwindow : 0≤window)(hpad : 0<pad) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧
      ∀P : HighSourceParameters,P.profileBound=bound → P.B₀=2 →
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
      ∀(C₁ R₁ : κ→ Ideal O)(B₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→ Character)(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) (R₁ l) s.ν s.W s.P≠0) →
      let first := fun l=>child s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      ∀(E R : κ→ Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)(Ds : κ→Finset (Ideal O))(cap Araw wmin : ℝ),
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
      ∀coeff : κ→ℝ,(∀l∈labels,0≤ coeff l)→
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤Kcontrol) →
      (∑l∈labels,coeff l*(∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l)))≤
      C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*
        Z^(allowance+pad+2*P.εplain*P.d+(2*P.εslot*P.d)*N)*
        ∑l∈labels,coeff l*
          Z^((2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
            Real.logb Z ((E l).absNorm:ℝ)-
            ∑j∈Cycle63MarkedPlain.largeSlots
              (Cycle63CommonSupply.originalSlots
                (fun k : CenteredMomentCommonProfile.liveIndices (pick l).val=>k.val.val)) w wmin,w j))*
          (∏j∈Cycle63MarkedPlain.largeSlots
              (Cycle63CommonSupply.originalSlots
                (fun k : CenteredMomentCommonProfile.liveIndices (pick l).val=>k.val.val)) w wmin,
            max 1 ‖Cycle63MarkedPlain.labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
              (fun l=>excluded (naturalRow (st l).character (z l)
                ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) l j‖)^2 := by
  obtain ⟨bound,hbound,hboundJoint⟩ := actual_two_common_marked_shell
    (α:=α) (bp:=bp) M H hH η₀ ε hε hap N Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,?_⟩
  intro P hboundeq hB hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hboundJoint P hboundeq hslot hplain
  obtain ⟨Ccap,hCcap,hcaps⟩ := actual_retained_slot_caps M H hH P hslot hplain
  refine ⟨F,G,Cprofile,C*Ccap^N,hF,hCprofile,mul_pos hC (pow_pos (zero_lt_one.trans_le hCcap) _),?_⟩
  filter_upwards [hjoint,hcaps η₀] with Z he hc
  refine ⟨he.1,?_⟩
  intro κ labels st hQM hQη z hz a allowance Kcontrol T i ha ha' hK hT hi
    s hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ first E R pick t w σ v θ
    p Ds cap Araw wmin hcap hmatches hscales hAraw hpadallow hf₂ hstateMask hwidth hradial
    hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src coeff hcoeff hcontrol
  have hZ : 1<Z := by linarith [he.1]
  have hsource := he.2 labels st hQM hQη z hz a allowance Kcontrol T i ha ha' hK hT hi
    s hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ E R pick t w σ v θ
    p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂ hstateMask hwidth hradial
    hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad coeff hcoeff hcontrol
  have hcap' (l : κ)(hl : l∈labels)(j : α) :
      (max 1 ‖Cycle63MarkedPlain.labeledRawSlot M H hH η₀ P.Wslot Z w σ v t θ
        (fun l=>excluded (naturalRow (st l).character (z l)
          ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) l j‖)^2≤
      Ccap*Z^((2*a-1)*w j+2*P.εslot*P.d) := by
    have hh := hc.2 (st l) (hwidth l hl) (hQM l) (hQη l) (z l) (hz l) a i ha ha' hi
      (hradial l hl) (hupper l hl) (w j) (σ j) (t l) (v j) (θ j)
      (hw j) (hwr j) (hσlo j) (hσhi j) (hfreq l hl j)
    simpa only [Cycle63MarkedPlain.labeledRawSlot,hB] using hh
  have hd := Cycle63MarkedPlain.retained_family_discard M H hH
    (fun l=>CenteredMomentCommonProfile.liveIndices (pick l).val)
    (fun l k=>k.val.val) (fun l a b h=>Subtype.ext (Subtype.ext h)) P hB η₀ Z st z hz
    w σ v θ t labels
    (fun l=>Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-Real.logb Z ((E l).absNorm:ℝ))
    coeff Ccap (2*a-1) (2*P.εslot*P.d) (pad+2*P.εplain*P.d) wmin hZ hCcap
    (mul_nonneg (mul_nonneg (by norm_num) P.hεs.le) P.hd.le) N hcard hcoeff hcap'
  have hfac : 0≤C*Cprofile^2*Kcontrol*(2*T)^(2*ε)*Z^allowance := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) hK)
      (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _)
  simp only [add_assoc] at hsource hd ⊢
  apply hsource.trans
  apply (mul_le_mul_of_nonneg_left hd hfac).trans_eq
  simp only [Real.rpow_add (zero_lt_one.trans hZ)]
  ring

end
end OAI.SevenEighths.Cycle63InitialMass
