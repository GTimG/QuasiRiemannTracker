import Candidate.Cycle63.Physical.InitialMass.SecondHighShell

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
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Joint high-shell estimate for an injective selection of actual rows.
All dependent source data stay on the selected row type; the extension outside
its encoded image contributes no terms or analytic assumptions. -/
theorem actual_common_selected_high_shell {α Base : Type} [Fintype α] [DecidableEq α]
    [Fintype Base] (base : Base→Character) (η₀ : Character)
    (B Q loss ε : ℝ) (hB : 0≤B) (hQ : 0≤Q) (hQB : Q≤B)
    (hloss : 0<loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0<ap) :
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
      ∀(S : κ→Finset α)
        (s : ∀l,Input (S l))
        (E R : κ→Ideal O)
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
      C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
        Z^(m+q*unmarkedDensity (2*a-1)+loss+e+allowance) := by
  obtain ⟨bound,hbound,J,hboundJoint⟩ := actual_common_joint_high_shell
    (α:=α) (bp:=bp) M H hH base η₀ B Q loss ε hB hQ hQB hloss hε hap
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hboundJoint P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ _ left u₀ unit q m a e allowance Kcontrol T i hq ha ha' hK hT
    key hinj labels st hQM hQη z hz index holes hholes hmask hzero hsupported heq hsupport hnorm hmissing
    hi S s E R pick t w σ v θ p Ds cap hcap hmatches hscales hstateMask hwidth hradial hupper
    hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hallowance hraw
  let back := Function.invFun key
  have hb (k : κ) : back (key k)=k := Function.leftInverse_invFun hinj k
  have hh := he.2 left u₀ unit q m a e allowance Kcontrol T i hq ha ha' hK hT
    (labels.image key) (fun j=>st (back j)) (fun j=>hQM (back j))
    (fun j=>hQη (back j)) (fun j=>z (back j)) (fun j=>hz (back j))
    (fun j=>index (back j)) (fun j=>holes (back j))
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hholes k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hmask k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hzero k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hsupported k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact heq k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hsupport k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hnorm k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hmissing k hk)
    hi (fun j=>S (back j)) (fun j=>s (back j)) (fun j=>E (back j))
    (fun j=>R (back j)) (fun j=>pick (back j)) (fun j=>t (back j))
    (fun j=>w (back j)) (fun j=>σ (back j)) (fun j=>v (back j))
    (fun j=>θ (back j)) (fun j=>p (back j)) (fun j=>Ds (back j)) cap hcap
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hmatches k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hscales k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hstateMask k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hwidth k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hradial k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hupper k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hw k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hwr k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hσlo k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hσhi k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hfreq k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hplainfreq k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hW k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hDs k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      try erw [hb k]
      exact hdyad k hk)
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      exact (congrArg (fun k=>(p k).control G^2*wholeControl (src k)^2≤Kcontrol) (hb k)).mpr (hcontrol k hk))
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      exact (congrArg (fun k=>(src k).toSource.allowance Z+Cycle63.Physical.plainClipAllowance Z ![(src k).b₁,(src k).b₂]≤allowance) (hb k)).mpr (hallowance k hk))
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      exact (congrArg (fun k=>(2*a-1)*Real.logb Z (preVolume (src k))+2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤e) (hb k)).mpr (hraw k hk))
  rw [Finset.sum_image (fun x _ y _ h=>hinj h)] at hh
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro k hk
  exact (congrArg (fun k=>∑L∈Ds k,∑alloc∈(src k).toSource.active L,
    retainedAllocationCost (src k) L alloc (z k)) (hb k)).symm

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_common_selected_high_shell
