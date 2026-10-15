/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B109
import Submissions.cycle61_c0125139.Bundles.B119
import Submissions.cycle61_c0125139.Bundles.B123
import Submissions.cycle61_c0125139.Bundles.B130

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondSelectedHighShell; sha256 dc3872172f7d26ff48adebab8c2197740c86965454814c62c8edfe0cf6ed9cae -/
section
                                                   

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
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Joint high-shell estimate for an injective selection of actual rows.
All dependent source data stay on the selected row type; the extension outside
its encoded image contributes no terms or analytic assumptions. -/
theorem actual_common_selected_high_shell {α Base : Type} [Fintype α] [DecidableEq α]
    [Fintype Base] (base : Base→ Character) (η₀ : Character)
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ : Type}[Nonempty κ],
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a e allowance Kcontrol T : ℝ) (i : ℕ),
      q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ (key : κ→ NonzeroJointSourceLabel left u₀ unit), Function.Injective key →
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
      (i:ℝ)≤ Z^P.τ →
      ∀(S : κ→ Finset α)
        (s : ∀l,Input (S l))
        (E R : κ→ Ideal O)
        (pick : ∀l,actualAllocations (s l).pools (E l))
        (t : κ→ℝ)
        (w σ v : ∀l,S l→ℝ)(θ : ∀l,S l→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)
        (Ds : κ→ Finset (Ideal O)) (cap : ℝ),
      cap≤ P.d*P.Rplain →
      (∀l∈labels,Matches M H hH (s l) η₀ (θ l) (w l) (σ l) (v l) P.Wslot P.B₀ Z) →
      (∀l∈labels,∀second j,Cycle61.Physical.sourcePlainScales (s l).toData.toSource second j≤ Z^cap) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R l*E l)) →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)< a+2*P.e) →
      (∀l∈labels,∀j,0≤ w l j) → (∀l∈labels,∀j,w l j/P.d≤ P.Rwidth) →
      (∀l∈labels,∀j,P.σmin≤σ l j) → (∀l∈labels,∀j,σ l j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v l j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,(s l).W₁=((p l).profile 0:ℝ→ℂ) ∧
        (s l).W₂=((p l).profile 1:ℝ→ℂ) ∧ (s l).b₁=bp ∧ (s l).b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (s l) (st l).character (t l)) (E l) (R l) (pick l)
      (∀l∈labels,((p l).control G)^2*(wholeControl (src l))^2≤ Kcontrol) →
      (∀l∈labels,(src l).toSource.allowance Z+
        Cycle61.Physical.plainClipAllowance Z ![(src l).b₁,(src l).b₂]≤ allowance) →
      (∀l∈labels,(2*a-1)*Real.logb Z (preVolume (src l))+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤ e) →
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
      exact (congrArg (fun k=>(p k).control G^2*wholeControl (src k)^2≤ Kcontrol) (hb k)).mpr (hcontrol k hk))
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      exact (congrArg (fun k=>(src k).toSource.allowance Z+Cycle61.Physical.plainClipAllowance Z ![(src k).b₁,(src k).b₂]≤ allowance) (hb k)).mpr (hallowance k hk))
    (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
      exact (congrArg (fun k=>(2*a-1)*Real.logb Z (preVolume (src k))+2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤ e) (hb k)).mpr (hraw k hk))
  rw [Finset.sum_image (fun x _ y _ h=>hinj h)] at hh
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro k hk
  exact (congrArg (fun k=>∑L∈Ds k,∑alloc∈(src k).toSource.active L,
    retainedAllocationCost (src k) L alloc (z k)) (hb k)).symm

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_common_selected_high_shell

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondSelectedHighShell -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondChildHighShell; sha256 145168a9a1deb69e88f16c5613b5be5d0517581f8a07ca767d52df7d02c1e2a4 -/
section
                                                           
                                                        

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
    [Fintype Base] (base : Base→ Character) (η₀ : Character)
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(Cs bs b window pad : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hb : 1≤ b)(hwindow : 0≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ : Type}[Nonempty κ],
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a e allowance Kcontrol T : ℝ) (i : ℕ),
      q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ (key : κ→ NonzeroJointSourceLabel left u₀ unit), Function.Injective key →
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
      (i:ℝ)≤ Z^P.τ →
      ∀(s : Input α),Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      s.b₁≤ bs → s.b₂≤ bs → s.upper≤ b →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
      ∀(C₁ R₁ : κ→ Ideal O)(B₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→ Character)(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) (R₁ l) s.ν s.W s.P≠0) →
      let first := fun l=>child s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      ∀(E R : κ→ Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)(Ds : κ→ Finset (Ideal O))(cap Araw : ℝ),
      cap≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      Real.logb Z (preVolume s.toData)≤ Araw → pad≤ allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R l)
        (first l).ν (first l).W (first l).P≠0) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R l*E l)) →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)< a+2*P.e) →
      (∀j,0≤ w j) → (∀j,w j/P.d≤ P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (first l) (st l).character (t l)) (E l) (R l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤ Kcontrol) →
      (∀l∈labels,(2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
        Real.logb Z ((E l).absNorm:ℝ))+pad+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤ e) →
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
      change Real.logb Z (preVolume (commonData (first l) (E l) (R l) (pick l)))≤ _
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

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondChildHighShell -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryHighShell; sha256 bd96a9351f02d3cb2d579b53b760ed2cc3bd48a809b6feb5b6a9c430b1b9d53c -/
section
                                                        
                                                        
                                                        

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
open CenteredMomentChildRows RayFourExpansion
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- High shell energy for actual geometric second rows in the fixed two-ray
dictionary. Canonical masks, nonzero holes and both stages of ideal support
are derived from the source, for either first orientation and second sign. -/
theorem actual_geometry_selected_high_shell {α : Type} [Fintype α] [DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (B Q loss ε : ℝ) (hB : 0≤ B) (hQ : 0≤ Q) (hQB : Q≤ B)
    (hloss : 0< loss) (hε : 0<ε) {ap bp : ℝ} (hap : 0< ap)
    (N : ℕ)(Cs bs b window pad : ℝ)
    (hCs : 1≤ Cs)(hbs : 1≤ bs)(hb : 1≤ b)(hwindow : 0≤ window)(hpad : 0< pad) :
    ∃bound : ℕ→ℝ,(∀k,0< bound k) ∧ ∃J : ℕ,
      ∀P : HighSourceParameters,P.profileBound=bound →
      8*P.τ≤ P.d*P.vslot → 16*P.τ≤ P.d*P.vplain →
      ∃F G : Finset (ℕ×ℕ),∃Cprofile C : ℝ,(0,0)∈F ∧ 0< Cprofile ∧ 0< C ∧
      ∀ᶠZ : ℝ in atTop,2≤ Z ∧
      ∀{κ DataLabel : Type}[Nonempty κ][Fintype DataLabel],
      ∀(reflected second : Bool)(s : Input α)(hη : s.η=excluded F₀.character R₀)
        (R seed : Ideal O)(K ξ : ℝ)(hK : 0< K)(bin : ℤ×(Fin 5→ℤ))
        (column : κ→ FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
        (datum : DataLabel→ SecondInputDatum α)(first : DataLabel→ FirstSourceLabel)
        (row : κ→ secondLiveRows (fun l=>(datum l).block))
        (hparent : ∀l,(datum (row l).val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin (column l))
        (hfirst : ∀l,first (row l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l))
        (hR : ∀l,(datum (row l).val.1).R≠0)(ψ : κ→ RayCharacter),
      let left := !reflected
      let unit := fun l=>(firstDictionaryUnit left η₀ u₀ F₀ R₀ l:O)
      let hf := fun l=>geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin (column l) datum first (row l) (hfirst l)
      let rawKey := fun l=>secondEncodedNonzeroRow (fun k=>(datum k).block) first (row l) left u₀ unit (hf l)
      let key := fun l=>if second then reflectedNonzeroJointLabel (rawKey l) else rawKey l
      ∀
        (q m a e allowance Kcontrol T : ℝ) (i : ℕ),
      q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      Function.Injective key →
      ∀ labels : Finset κ,
      ∀ st : κ → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : κ → O) (hz : ∀ l, (st l).radial.keep (z l))
        (hchar : ∀l,(st l).character=(datum (row l).val.1).τ (ψ l))
        (hpuncture : ∀l,(st l).puncture=(datum (row l).val.1).R*
          (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
        (hrow : ∀l,z l=if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val),
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow (key l)) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit (key l).val}*
        firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((key l).val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        ((key l).val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        ((key l).val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ ((key l).val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left (key l).val.1).absNorm : ℝ) ≤ Z^m) →
      (i:ℝ)≤ Z^P.τ →
      Fintype.card α≤ N → (∀j,s.M j≤ Cs) →
      s.b₁≤ bs → s.b₂≤ bs → s.upper≤ b →
      (∀j,logWindow (s.lo j) (s.hi j)≤ window) →
      ∀(C₁ R₁ : κ→ Ideal O)(B₁ : ∀l,actualAllocations s.pools (C₁ l))
        (χ₁ : κ→ Character)(t₁ : κ→ℝ),
      (∀l∈labels,frozenCoefficient (B₁ l).val (C₁ l) (R₁ l) s.ν s.W s.P≠0) →
      let first := fun l=>child s (C₁ l) (R₁ l) (B₁ l) (χ₁ l) (t₁ l)
      ∀(E R : κ→ Ideal O)(pick : ∀l,actualAllocations (first l).pools (E l))
        (t : κ→ℝ)(w σ v : α→ℝ)(θ : α→ RayQuotient.Characters M H)
        (p : κ→ Profiles ap bp)(Ds : κ→ Finset (Ideal O))(cap Araw : ℝ),
      cap≤ P.d*P.Rplain →
      Matches M H hH s η₀ θ w σ v P.Wslot P.B₀ Z →
      (∀second j,Cycle61.Physical.sourcePlainScales s.toData.toSource second j≤ Z^cap) →
      Real.logb Z (preVolume s.toData)≤ Araw → pad≤ allowance →
      (∀l∈labels,frozenCoefficient (pick l).val (E l) (R l)
        (first l).ν (first l).W (first l).P≠0) →
      (∀l∈labels,(st l).mask=CenteredMomentSecondHeightFamily.fixedBadMask*
        ConcretePrimeRowBridge.idealGenerator (R l*E l)) →
      (∀l∈labels,(st l).width≤ P.Mcap) →
      (∀l∈labels,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀l∈labels,HeckeDetectorZeros.zeroMaximum
        (wholeSourceFamily M H hH η₀
          (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
            (st l).puncture))
        (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l) _)
          (3*(i+1:ℕ)*Z^P.τ)< a+2*P.e) →
      (∀j,0≤ w j) → (∀j,w j/P.d≤ P.Rwidth) →
      (∀j,P.σmin≤σ j) → (∀j,σ j≤ P.σmax) →
      (∀l∈labels,∀j,|t l+v j|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,|t l|+Z^P.τ/2≤(3*i+2:ℕ)*Z^P.τ) →
      (∀l∈labels,s.W₁=((p l).profile 0:ℝ→ℂ) ∧
        s.W₂=((p l).profile 1:ℝ→ℂ) ∧ s.b₁=bp ∧ s.b₂=bp) →
      (∀l∈labels,∀L∈Ds l,Squarefree L) →
      (∀l∈labels,∀L∈Ds l,T≤(L.absNorm:ℝ) ∧ (L.absNorm:ℝ)<2*T) →
      let src := fun l=>commonData (withHeight (first l) (st l).character (t l)) (E l) (R l) (pick l)
      (∀l∈labels,((p l).control G)^2*(2*bs*Cs^N)^2≤ Kcontrol) →
      (∀l∈labels,(2*a-1)*(Araw-Real.logb Z ((C₁ l).absNorm:ℝ)-
        Real.logb Z ((E l).absNorm:ℝ))+pad+
        2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)≤ e) →
      (∑l∈labels,∑L∈Ds l,∑alloc∈(src l).toSource.active L,
        retainedAllocationCost (src l) L alloc (z l))≤
      C*Cprofile^2*Kcontrol*(1+3*(i+1:ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
        Z^(m+q*unmarkedDensity (2*a-1)+loss+e+allowance) := by
  obtain ⟨bound,hbound,J,hboundJoint⟩ := actual_child_selected_high_shell
    (α:=α) (bp:=bp) M H hH (secondFixedDictionary η₀) η₀ B Q loss ε hB hQ hQB hloss hε hap
    N Cs bs b window pad hCs hbs hb hwindow hpad
  refine ⟨bound,hbound,J,?_⟩
  intro P hboundeq hslot hplain
  obtain ⟨F,G,Cprofile,C,hF,hCprofile,hC,hjoint⟩ := hboundJoint P hboundeq hslot hplain
  refine ⟨F,G,Cprofile,C,hF,hCprofile,hC,?_⟩
  filter_upwards [hjoint] with Z he
  refine ⟨he.1,?_⟩
  intro κ DataLabel _ _ reflected second s hη R seed K ξ hK bin column datum first row hparent hfirst hR ψ
    left unit hf rawKey key q m a e allowance Kcontrol T i hq ha ha' hKcontrol hT
    hinj labels st hQM hQη z hz hchar hpuncture hrow hzero hsupport hnorm hmissing hi
    hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁ firstChild
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad src hcontrol hledger
  let index := fun l=>(geometryDictionaryRay reflected s R seed K Z ξ hK bin (column l),ψ l)
  let holes := fun l=>(datum (row l).val.1).input.η.modulus*
    ((datum (row l).val.1).R*(if second then (datum (row l).val.1).D else (datum (row l).val.1).C))
  have hd l := actual_geometry_natural_dictionary reflected second η₀ u₀ F₀ R₀ hu₀ s hη R seed K Z ξ hK
    bin (column l) datum first (row l) (hparent l) (hfirst l) (hR l) (ψ l)
  have hmask l (I : Ideal O) :
      idealCoeff (excluded (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) I =
      idealCoeff (excluded (naturalRow (secondFixedDictionary η₀ (index l)) (nonzeroJointSourceRow (key l)).val
        (nonzeroJointSourceRow (key l)).property).character (holes l)) I := by
    have transfer (χ χ' : Character) (u v : O) (hu : u≠0) (hv : v≠0)
        (hc : χ=χ') (hr : u=v) :
        (naturalRow χ u hu).character=(naturalRow χ' v hv).character := by
      subst χ'; subst v; rfl
    have hv : (if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val)≠0 :=
      (hrow l) ▸ (st l).row_ne_zero (z l) (hz l)
    rw [transfer _ _ _ _ _ hv (hchar l) (hrow l),hpuncture l]
    exact (hd l).2 I
  have hfirstSupport l : Supported (key l).val.1.1.1 ∧ Supported (key l).val.1.1.2 ∧
      primeSupport (key l).val.1.1.1=primeSupport (key l).val.1.1.2 := by
    have heq : (key l).val.1=geometryFirstLabel s R seed K Z ξ hK bin (column l) := by
      cases second <;> exact hfirst l
    rw [heq]
    exact ⟨(geometryFirstSource s R seed K Z ξ hK bin (column l).1).hC,
      (geometryFirstSource s R seed K Z ξ hK bin (column l).1).hD,
      (geometryFirstSource s R seed K Z ξ hK bin (column l).1).sameSupport⟩
  have hsupported l : Supported (key l).val.1.1.1 ∧ (key l).val.1.1.2≠0 ∧
      Supported (key l).val.2.1.1 ∧ (key l).val.2.1.2≠0 := by
    refine ⟨(hfirstSupport l).1,(hfirstSupport l).2.1.1,?_⟩
    cases second <;> exact ⟨(datum (row l).val.1).hC,(datum (row l).val.1).hD.1⟩
  have heq l : primeSupport (key l).val.1.1.1=primeSupport (key l).val.1.1.2 ∧
      primeSupport (key l).val.2.1.1=primeSupport (key l).val.2.1.2 := by
    refine ⟨(hfirstSupport l).2.2,?_⟩
    cases second <;> exact (datum (row l).val.1).sameSupport
  exact he.2 left u₀ unit q m a e allowance Kcontrol T i hq ha ha' hKcontrol hT
    key hinj labels st hQM hQη z hz index holes (fun l _=>(hd l).1) (fun l _=>hmask l)
    hzero (fun l _=>hsupported l) (fun l _=>heq l) hsupport hnorm hmissing hi
    s hcard hM hb₁ hb₂ hupperB hwin C₁ R₁ B₁ χ₁ t₁ hf₁
    E R₂ pick t w σ v θ p Ds cap Araw hcap hmatches hscales hAraw hpadallow hf₂
    hstateMask hwidth hradial hupper hw hwr hσlo hσhi hfreq hplainfreq hW hDs hdyad hcontrol hledger

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_selected_high_shell

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryHighShell -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondChildHighPayment; sha256 232045f1581e09b2cdd30c248ca438aaf37cb12190fd658959252de93a891c58 -/
section
                                                     

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle61Moment Cycle61HighGeometry
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- High scalar payment for the genuine first common child. The eventual
threshold pays the fixed lower-volume constant before any moving source. -/
theorem eventual_actual_child_high_payment (N : ℕ) (lo εv : ℝ)
    (hlo : 0< lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤ N → lo≤ s.lower →
    ∀(reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2),
    primeSupport l.1.1=primeSupport l.1.2 →
    ∀(Rfirst : Ideal O)(B : actualAllocations s.pools (if reflected then l.1.2 else l.1.1))
    (χ : Character)(t : ℝ),
    frozenCoefficient B.val (if reflected then l.1.2 else l.1.1) Rfirst s.ν s.W s.P≠0 →
    ∀(C₂ D₂ : Ideal O)(hC₂ : Supported C₂)(hD₂ : Supported D₂),
    primeSupport C₂=primeSupport D₂ →
    ∀(U : Finset (CommonIndex C₂ D₂))(b δ M a ξ reserve ε : ℝ),
    3401/100000≤ b ∧ b≤1/25 →
    Cycle61.Arithmetic.q0≤δ ∧ δ≤3/4 → 0≤ M →
    Real.logb Z (volume s)≤ M*Cycle61.Arithmetic.totalA b →
    a≤ M*Cycle61.Arithmetic.amp b →
    let A := Real.logb Z (volume s)
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let q := M-R-max (c-d) 0+Lc-6*a-ω+ε
    let m := Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/volume (child s
      (if reflected then l.1.2 else l.1.1) Rfirst B χ t))*
      (normalizer C₂ D₂ U/Z^b₂)*Z^(m+ρ*q+δ*(A-c-b₂)) ≤
      Z^(S-M*(720486667/30493190000000)+(1-ρ)*ω+ρ*ε+εv) := by
  filter_upwards [eventual_common_inverse_volume N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hcard hlow reflected left second l hC hD heq Rfirst B χ t hB
    C₂ D₂ hC₂ hD₂ heq₂ U b δ M a ξ reserve ε hb hδ hM hA ha
  let A := Real.logb Z (volume s)
  let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
  have hZ := zero_lt_one.trans hz.1
  have hv := volume_pos s
  have hc : (0:ℝ)<(if reflected then l.1.2 else l.1.1).absNorm := by
    cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact norm_pos _ hC.1
    · exact norm_pos _ hD.1
  have hV : Z^A=volume s := Real.rpow_logb hZ hz.1.ne' hv
  have hratio : ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)/volume s=
      (Z^(A-c))⁻¹ := by
    rw [Real.rpow_sub hZ,hV,Real.rpow_logb hZ hz.1.ne' hc,inv_div]
  have hi := hz.2 s hcard hlow _ Rfirst B χ t hB
  rw [hratio] at hi
  have hmain : firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l /
      volume (child s (if reflected then l.1.2 else l.1.1) Rfirst B χ t) ≤
      Z^εv*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/Z^(A-c)) := by
    have hh := mul_le_mul_of_nonneg_left hi
      (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve hZ l).le
    simpa only [div_eq_mul_inv,mul_left_comm] using hh
  have hp := actual_high_scalar_payment reflected left second l hC hD heq
    C₂ D₂ hC₂ hD₂ heq₂ U Z b δ M A a ξ reserve ε hz.1 hb hδ hM hA ha
  dsimp only at hp ⊢
  rw [hV] at hp
  have hp' := mul_le_mul_of_nonneg_left hp (Real.rpow_pos_of_pos hZ εv).le
  rw [←Real.rpow_add hZ] at hp'
  rw [add_comm εv] at hp'
  apply le_trans _ hp'
  have hn := (normalizer_pos C₂ D₂ hC₂ U).le
  have hh := mul_le_mul_of_nonneg_left hmain (Real.rpow_pos_of_pos hZ (-a)).le
  have hh' := mul_le_mul_of_nonneg_right hh
    (div_nonneg hn (Real.rpow_pos_of_pos hZ (Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ))).le)
  have hh'' := mul_le_mul_of_nonneg_right hh' (Real.rpow_pos_of_pos hZ
    (Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)+LocalMoment.unmarkedDensity δ*
      (M-Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)-
        max (c-Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)) 0+
        Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)-6*a-
        (frequencyLoss Z 32 ξ+reserve)+ε)+
      δ*(A-c-Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)))).le
  convert hh'' using 1 <;> ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_actual_child_high_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondChildHighPayment -/
