import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondHighShell
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

/-- The high shell of an injective selection of actual rows. All dependent source data stay on the selected row type;
the energy is at most the pointwise bound times the number of selected rows. -/
theorem actual_common_selected_high_shell {α : Type} [Fintype α] [DecidableEq α] (η₀ : Character)
    (ε : ℝ) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap) :
    ∃bound : ℕ→ℝ,(∀k,0<bound k) ∧
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤P.d*P.vslot → 16*P.τ≤P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0<Cprofile ∧ 0<C ∧
      ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{κ : Type}[Nonempty κ],
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (a e allowance Kcontrol T : ℝ) (i : ℕ),
      4/5 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ (key : κ→NonzeroJointSourceLabel left u₀ unit), Function.Injective key →
      ∀ labels : Finset κ,
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l)),
      (i:ℝ)≤Z^P.τ →
      ∀(S : κ→Finset α)
        (s : ∀l,Input (S l))
        (E R : κ→ Ideal O)
        (pick : ∀l,actualAllocations (s l).pools (E l))
        (t : κ→ℝ)
        (w σ v : ∀l,S l→ℝ)(θ : ∀l,S l→RayQuotient.Characters M H)
        (p : κ→Profiles ap bp)
        (Ds : κ→Finset (Ideal O)) (cap : ℝ),
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
  obtain ⟨bound,hbound,hboundJoint⟩ := actual_common_joint_high_shell
    (α:=α) (bp:=bp) M H hH η₀ ε hε hap
  refine ⟨bound,hbound,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hboundJoint P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ _ left u₀ unit a e allowance Kcontrol T i ha ha' hK hT
    key hinj labels st hQM hQη z hz
    hi S s E R pick t w σ v θ p Ds cap hcap hmatches hscales hstateMask hwidth hradial hupper
    hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hallowance hraw
  let back := Function.invFun key
  have hb (k : κ) : back (key k)=k := Function.leftInverse_invFun hinj k
  have hh := he.2 left u₀ unit a e allowance Kcontrol T i ha ha' hK hT
    (labels.image key) (fun j=>st (back j)) (fun j=>hQM (back j))
    (fun j=>hQη (back j)) (fun j=>z (back j)) (fun j=>hz (back j))
    hi (fun j=>S (back j)) (fun j=>s (back j)) (fun j=>E (back j))
    (fun j=>R (back j)) (fun j=>pick (back j)) (fun j=>t (back j))
    (fun j=>w (back j)) (fun j=>σ (back j)) (fun j=>v (back j))
    (fun j=>θ (back j)) (fun j=>p (back j)) (fun j=>Ds (back j)) cap hcap
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hmatches k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hscales k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hstateMask k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hwidth k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hradial k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hupper k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hw k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hwr k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hσlo k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hσhi k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hfreq k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hplainfreq k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hW k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hDs k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; (try erw [hb k]); exact hdyad k hk)
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; exact (congrArg (fun k=>(p k).control G^2*wholeControl (src k)^2≤Kcontrol) (hb k)).mpr (hcontrol k hk))
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; exact (congrArg (fun k=>(src k).toSource.allowance Z+Cycle63.Physical.plainClipAllowance Z ![(src k).b₁,(src k).b₂]≤allowance) (hb k)).mpr (hallowance k hk))
    (by intro j hj; obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj; exact (congrArg (fun k=>(2*a-1)*Real.logb Z (preVolume (src k))+2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤e) (hb k)).mpr (hraw k hk))
  rw [Finset.sum_image (fun x _ y _ h=>hinj h), Finset.card_image_of_injective labels hinj] at hh
  apply le_trans (le_of_eq ?_) hh
  refine Finset.sum_congr rfl fun k hk => ?_
  exact (congrArg (fun k=>∑L∈Ds k,∑alloc∈(src k).toSource.active L,
    retainedAllocationCost (src k) L alloc (z k)) (hb k)).symm

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
