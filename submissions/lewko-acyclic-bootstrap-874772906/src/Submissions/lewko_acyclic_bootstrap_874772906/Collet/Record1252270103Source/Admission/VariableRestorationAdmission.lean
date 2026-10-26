/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual positive row families from one fixed-anchor earlier global source. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FamilyRaw
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.VariableRestoration
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.Canonical
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.GlobalRaw
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
local instance variableRestorationAdmissionFinite : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (Hray : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ Hray)

def profileFloor (b : ℝ) : ℝ := (max 1 b)⁻¹

lemma profileFloor_bounds (b : ℝ) : 0<profileFloor b ∧ profileFloor b≤1 := by
  have hB : 0<max (1:ℝ) b := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨inv_pos.mpr hB,?_⟩
  simpa only [profileFloor,one_div] using
    (div_le_iff₀ hB).mpr (show (1:ℝ)≤1*(max 1 b) by simpa using le_max_left (1:ℝ) b)

lemma positive_row_profile_floor_norm_le {κ : Type*} [Fintype κ]
    (τ : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (b : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (S : κ→Finset (Ideal O)) (β : κ→Ideal O→ℂ) (P : κ→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    ‖positiveSlotRow τ m A z W₁ W₂ S β P t X₁ X₂‖≤
      ‖positiveSlotRow τ m A z W₁ W₂ S β P t
        (max (profileFloor b) X₁) (max (profileFloor b) X₂)‖ := by
  classical
  have small (X : ℝ) (hX : 0<X) (h : X<profileFloor b) : X*b<1 := by
    have hB : 0<max (1:ℝ) b := zero_lt_one.trans_le (le_max_left _ _)
    have hh : X*(max 1 b)<1 := (lt_div_iff₀ hB).mp (by simpa [profileFloor,one_div] using h)
    exact (mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) b) hX.le).trans_lt hh
  by_cases h₁ : profileFloor b≤X₁
  · by_cases h₂ : profileFloor b≤X₂
    · rw [max_eq_right h₁,max_eq_right h₂]
    · have hz:=CenteredMomentRetainedProfile.strict_subunit_rowTwistedSum_zero
        τ m A z W₂ b t X₂ hX₂ hs₂ (small X₂ hX₂ (lt_of_not_ge h₂))
      simp only [positiveSlotRow,hz,mul_zero,zero_mul,norm_zero]
      positivity
  · have hz:=CenteredMomentRetainedProfile.strict_subunit_rowTwistedSum_zero
      τ m A z W₁ b t X₁ hX₁ hs₁ (small X₁ hX₁ (lt_of_not_ge h₁))
    simp only [positiveSlotRow,hz,mul_zero,zero_mul,norm_zero]
    positivity

theorem global_fixed_missing_positive_variable_shortened
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
    ∀(C₁ C₂ : ℝ),0<C₁ → 0<C₂ → length Z C₁≤m₁ → length Z C₂≤m₂ →
    ∀(A : ℝ)(weight : labels→ℝ),
      (∀l : labels,1≤(Φ (‖eisEmbedding (nonzeroJointSourceRow l.val).val‖^2/(Z^M))).re) →
      0≤A → (∀l,0≤weight l) → (∀l,weight l≤A) →
    ∀(X₁ X₂ Y₁ Y₂ : labels→ℝ),
      (∀l,0<X₁ l ∧ 0<X₂ l ∧ X₁ l≤C₁ ∧ X₂ l≤C₂) →
      (∀l,0<Y₁ l ∧ 0<Y₂ l ∧ Y₁ l≤X₁ l ∧ Y₂ l≤X₂ l) →
      (∑l : labels,weight l*‖positiveSlotRow (τ l) (fixedBadMask*idealGenerator (mask l)) 1 (z l)
        W₁ W₂ (fun i:F=>primePool rayModulus Hray slotUpper (Z^(w i)))
        (fun (i:F) I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
        (fun i:F=>Z^(w i)) t (Y₁ l) (Y₂ l)‖^2)≤
      C*Z^loss*A*((∏I∈ps (R*H),I).absNorm:ℝ)^εmask*
        ((1+2*(Real.log (max 1 C₁)-Real.log (profileFloor b)))*
          ((1+2*(Real.log (max 1 C₂)-Real.log (profileFloor b)))*
          globalRawBudget CP DP TP degreeP Φ
            (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t)
            (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) t height Z M εsource)) := by
  obtain ⟨TP,DP,C,hDP,hC,hraw⟩:=global_fixed_missing_positive_family (α:=α)
    rayModulus Hray hH Mslot hMslot slotUpper B loss εmask hB hloss hεmask SP
  refine ⟨TP,DP,C,hDP,hC,?_⟩
  intro F Bprev lam hprev hlam W a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ₂
    η η₀ Q degreeP CP hCP hp left u₀ unit H hH0 labels
    hrow hsupport hsupported heq hnorm hmissing R hR hkeep
    τ z mask physical hmask hdict W₁ W₂ ha hb hs₁ hs₂
    θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    M m₁ m₂ cap hMlo hMhi hslotcap hcapacity hcap Φ hΦs hΦ
    C₁ C₂ hC₁ hC₂ hx₁ hx₂ A weight hcover hA hweight hweightA
    X₁ X₂ Y₁ Y₂ hX hY
  have hf := profileFloor_bounds b
  have hfloorCap (C : ℝ) : profileFloor b≤max 1 C := hf.2.trans (le_max_left _ _)
  have hcl₁ (l : labels) : max (profileFloor b) (Y₁ l)≤max 1 C₁ :=
    max_le (hfloorCap C₁) ((hY l).2.2.1.trans ((hX l).2.2.1.trans (le_max_right _ _)))
  have hcl₂ (l : labels) : max (profileFloor b) (Y₂ l)≤max 1 C₂ :=
    max_le (hfloorCap C₂) ((hY l).2.2.2.trans ((hX l).2.2.2.trans (le_max_right _ _)))
  have hwin (C Y : ℝ) (hc : max (profileFloor b) Y≤max 1 C) :
      Real.log (max (profileFloor b) Y)∈Set.Icc (Real.log (profileFloor b)) (Real.log (max 1 C)) :=
    ⟨Real.log_le_log hf.1 (le_max_left _ _),Real.log_le_log
      (hf.1.trans_le (le_max_left _ _)) hc⟩
  have hlen (C : ℝ) : length Z (Real.exp (Real.log (max 1 C)))=length Z C := by
    rw [Real.exp_log (zero_lt_one.trans_le (le_max_left _ _))]
    change Real.logb Z (max 1 (max 1 C))=Real.logb Z (max 1 C)
    rw [max_eq_right (le_max_left (1:ℝ) C)]
  have hr:=hraw F Bprev lam hprev hlam W a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ₂
    η η₀ Q degreeP CP hCP hp left u₀ unit H hH0 labels
    hrow hsupport hsupported heq hnorm hmissing R hR hkeep
    τ z mask physical hmask hdict W₁ W₂ ha hb hs₁ hs₂
    θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    M m₁ m₂ cap hMlo hMhi hslotcap hcapacity hcap Φ hΦs hΦ
    (Real.log (profileFloor b)) (Real.log (max 1 C₁))
    (Real.log (profileFloor b)) (Real.log (max 1 C₂)) A
    (fun l=>Real.log (max (profileFloor b) (Y₁ l)))
    (fun l=>Real.log (max (profileFloor b) (Y₂ l))) weight hcover
    (Real.log_le_log hf.1 (hfloorCap C₁)) (Real.log_le_log hf.1 (hfloorCap C₂))
    (by rw [hlen];exact hx₁) (by rw [hlen];exact hx₂)
    (fun l=>hwin C₁ (Y₁ l) (hcl₁ l)) (fun l=>hwin C₂ (Y₂ l) (hcl₂ l))
    hA hweight hweightA
  simp only [Real.exp_log (hf.1.trans_le (le_max_left _ _))] at hr
  apply le_trans _ hr
  apply Finset.sum_le_sum
  intro l hl
  apply mul_le_mul_of_nonneg_left _ (hweight l)
  exact pow_le_pow_left₀ (norm_nonneg _) (positive_row_profile_floor_norm_le _ _ _ _ W₁ W₂ b
    (hs₁.trans (by intro x hx;exact hx.2)) (hs₂.trans (by intro x hx;exact hx.2)) _ _ _ _ _ _
    (hY l).1 (hY l).2.1) 2

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.profileFloor_bounds
#print axioms QRH.Record1252270103Source.Admission.positive_row_profile_floor_norm_le
#print axioms QRH.Record1252270103Source.Admission.global_fixed_missing_positive_variable_shortened
