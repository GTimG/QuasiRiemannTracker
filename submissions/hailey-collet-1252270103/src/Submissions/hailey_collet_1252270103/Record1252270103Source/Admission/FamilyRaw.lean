/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual positive row families from one fixed-anchor earlier global source. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.Dictionary
import Submissions.hailey_collet_1252270103.Record1252270103Source.Low.GlobalRaw
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve Cycle61Moment
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentEnergySlotHeight
open CenteredMomentEnergyProfiles CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentNaturalFixedRaySource
open CenteredMomentPrimeSlot CenteredMomentEnergyBands
open QRH.Record12518109Source Record12518109Raw QRH.Record1252270103Low
local notation "O" => HeckeFamily.O
local notation "ps" => CompletedGauss.primeSupport

open CenteredMomentRetainedEnergy CenteredMomentTwist CenteredMomentLattice
open OAI.SevenEighths.Record1252270103Low
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (Hray : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ Hray)

/-- The only analytic premise is the earlier fixed-anchor InitialAffineAt.
The physical dictionary is coefficient equality and may come from
`actual_joint_extra_mask`; the original fixed-inducing filter is retained. -/
theorem global_fixed_missing_positive_family
    (Mslot : α→ℝ) (hMslot : ∀i,0≤Mslot i)
    (slotUpper B loss εmask : ℝ) (hB : 0≤B) (hloss : 0<loss) (hεmask : 0<εmask)
    (SP : Finset (ℕ×ℕ)) :
    ∃TP : Finset (ℕ×ℕ), ∃DP C : ℝ, 0<DP ∧ 0<C ∧
    ∀F : Finset α,
    ∀(Bprev lam hprev : ℝ), 0≤lam → ∀(W : ℝ→ℂ)
      (a b bΦ mesh σlo σhi Mmin Mmax εsource Z : ℝ),2≤Z →
    ∀(η η₀ : Character)(Q : Ideal O)(degreeP : ℕ)(CP : ℝ), 0≤CP →
      InitialAffineAt (α:=α) rayModulus Hray hH (SourceFace.mk Bprev lam 0 Bprev 0 hprev) W
        slotUpper a b bΦ mesh σlo σhi Mmin Mmax εsource Z η η₀ Q degreeP SP CP →
    ∀(left : Bool)(u₀ : O)(unit : FirstSourceLabel→O)(H : Ideal O), H≠0 →
    ∀labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      (∀l∈labels,((Ideal.span {(nonzeroJointSourceRow l).val}).absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((Ideal.span {(nonzeroJointSourceRow l).val}*H).absNorm:ℝ)≤Z^B) →
      (∀l∈labels,Supported l.val.1.1.1 ∧ l.val.1.1.2≠0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2≠0) →
      (∀l∈labels,ps l.val.1.1.1=ps l.val.1.1.2 ∧ ps l.val.2.1.1=ps l.val.2.1.2) →
      (∀l∈labels,(l.val.1.1.1.absNorm:ℝ)≤Z^B ∧ (l.val.1.1.2.absNorm:ℝ)≤Z^B ∧
        (l.val.2.1.1.absNorm:ℝ)≤Z^B ∧ (l.val.2.1.2.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,firstSourceMissing left l.val.1=H) →
    ∀R : Ideal O,R≠0 →
      (∀l : labels,initialKeep η (internalQ Q η₀) (nonzeroJointSourceRow l.val).val) →
    ∀(τ : labels→Character)(z : labels→O)(mask : labels→Ideal O),
    ∀(physical : ∀l : labels,NaturalRow (τ l) (z l)),
      (∀l,mask l≠0) →
      (∀(l : labels)(I : Ideal O),idealCoeff (excluded (physical l).character (mask l)) I=
        idealCoeff (excluded (naturalRow η (nonzeroJointSourceRow l.val).val
          (nonzeroJointSourceRow l.val).property).character (R*H)) I) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ))(ha : 0<a)(hb : 0≤b)
      (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
      (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b),
    ∀(θ : α→RayQuotient.Characters rayModulus Hray)(w σ freq : α→ℝ)(t height : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤mesh) →
      (∀i∈F,σlo≤σ i) → (∀i∈F,σ i≤σhi) → 0≤height → (∀i∈F,|freq i|≤height) →
      (∀i∈F,∀I∈primePool rayModulus Hray slotUpper (Z^(w i)),Prime I) →
      (∀i∈F,∀I∈primePool rayModulus Hray slotUpper (Z^(w i)),
        ‖idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I‖≤Mslot i) →
      (∀i∈F,∀I∈primePool rayModulus Hray slotUpper (Z^(w i)),
        idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I≠0 →
        (I.absNorm:ℝ)≤slotUpper*Z^(w i)) →
    ∀(M m₁ m₂ cap : ℝ),Mmin≤M → M≤Mmax → cap≤hprev*M → m₁+m₂+lam*cap≤Bprev*M →
      (∑i∈F,w i)≤cap →
    ∀(Φ : 𝓢(ℝ,ℂ)),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
    ∀(lo hi low high A : ℝ)(lx ly weight : labels→ℝ),
      (∀l : labels,1≤(Φ (‖eisEmbedding (nonzeroJointSourceRow l.val).val‖^2/(Z^M))).re) →
      lo≤hi → low≤high → length Z (Real.exp hi)≤m₁ → length Z (Real.exp high)≤m₂ →
      (∀l,lx l∈Set.Icc lo hi) → (∀l,ly l∈Set.Icc low high) →
      0≤A → (∀l,0≤weight l) → (∀l,weight l≤A) →
      (∑l : labels,weight l*‖positiveSlotRow (τ l) (fixedBadMask*idealGenerator (mask l)) 1 (z l)
        W₁ W₂ (fun i:F=>primePool rayModulus Hray slotUpper (Z^(w i)))
        (fun (i:F) I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
        (fun i:F=>Z^(w i)) t (Real.exp (lx l)) (Real.exp (ly l))‖^2)≤
      C*Z^loss*A*((∏I∈ps (R*H),I).absNorm:ℝ)^εmask*
        ((1+2*(hi-lo))*((1+2*(high-low))*
          globalRawBudget CP DP TP degreeP Φ
            (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t)
            (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) t height Z M εsource)) := by
  obtain ⟨TP,DP,C,hDP,hC,hraw⟩:=global_fixed_missing_source_moment_all_slots (α:=α)
    rayModulus Hray hH Mslot hMslot slotUpper B loss εmask hB hloss hεmask SP
  refine ⟨TP,DP,C,hDP,hC,?_⟩
  intro F Bprev lam hprev hlam W a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ₂
    η η₀ Q degreeP CP hCP hp left u₀ unit H hH0 labels
    hrow hsupport hsupported heq hnorm hmissing R hR hkeep
    τ z mask physical hmask hdict W₁ W₂ ha hb hs₁ hs₂
    θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    M m₁ m₂ cap hMlo hMhi hslotcap hcapacity hcap Φ hΦs hΦ
    lo hi low high A lx ly weight hcover hlo hlow hm₁ hm₂ hlx hly hA hweight hweightA
  have hZ0 : 0<Z:=by linarith
  have hr:=hraw F Bprev lam hprev hlam W a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ₂
    η η₀ Q degreeP CP hCP hp left u₀ unit H hH0 labels
    hrow hsupport hsupported heq hnorm hmissing R hR hkeep
    (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t)
    (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) hb
    ((normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t).trans hs₁)
    ((normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t).trans hs₂)
    θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    M m₁ m₂ cap hMlo hMhi hslotcap hcapacity hcap Φ hΦs hΦ
    lo hi low high A lx ly weight hcover hlo hlow hm₁ hm₂ hlx hly hA hweight hweightA
  apply le_trans (le_of_eq ?_) hr
  apply Finset.sum_congr rfl
  intro l hl
  have hn:=positive_row_norm_dictionary (physical l)
    (naturalRow η (nonzeroJointSourceRow l.val).val (nonzeroJointSourceRow l.val).property)
    (mask l) (R*H) (hmask l) (hdict l) W₁ W₂ a b ha hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
    (fun i:F=>primePool rayModulus Hray slotUpper (Z^(w i)))
    (fun (i:F) I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
    (fun i:F=>Z^(w i)) (fun i=>Real.rpow_pos_of_pos hZ0 _) t
    (Real.exp (lx l)) (Real.exp (ly l)) (Real.exp_pos _) (Real.exp_pos _)
  rw [hn]
  have hprod:=Finset.prod_coe_sort F (fun i=>naturalSlot
    (excluded (naturalRow η (nonzeroJointSourceRow l.val).val
      (nonzeroJointSourceRow l.val).property).character (R*H))
    (primePool rayModulus Hray slotUpper (Z^(w i)))
    (heightCoefficient (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
  rw [hprod]

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.global_fixed_missing_positive_family
