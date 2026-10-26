/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual positive row families from one fixed-anchor earlier global source. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.FamilyRaw
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.VariableRestorationAdmission
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.VariableCofactorCorners
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
open Record1252270103Second Record1252270103Source
open QRH.Record1252270103Restoration QRH.Record1252270103KernelMass
open QRH.Record1252270103Source.High.CorrectedCentered
local notation "O" => HeckeFamily.O
local notation "ps" => CompletedGauss.primeSupport

open CenteredMomentRetainedEnergy CenteredMomentTwist CenteredMomentLattice
open CenteredMomentHeckeSlots CenteredMomentHeckeExpansion CenteredMomentWholeSlotDeletion
open OAI.SevenEighths.Record1252270103Low
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance variableCofactorCornersAdmissionFinite : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (Hray : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ Hray)

theorem global_fixed_missing_frozen_variable_corners
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
    ∀(M mx₁ mx₂ my₁ my₂ cap : ℝ),Mmin≤M → M≤Mmax → cap≤hprev*M →
      mx₁+mx₂+lam*cap≤Bprev*M → my₁+my₂+lam*cap≤Bprev*M →
      (∑i∈F,w i)≤cap →
    ∀(Φ : 𝓢(ℝ,ℂ)),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
    ∀(CX₁ CX₂ CY₁ CY₂ : ℝ),0<CX₁ → 0<CX₂ → 0<CY₁ → 0<CY₂ →
      length Z CX₁≤mx₁ → length Z CX₂≤mx₂ → length Z CY₁≤my₁ → length Z CY₂≤my₂ →
    ∀(A : ℝ)(weight : labels→ℝ),
      (∀l : labels,1≤(Φ (‖eisEmbedding (nonzeroJointSourceRow l.val).val‖^2/(Z^M))).re) →
      0≤A → (∀l,0≤weight l) → (∀l,weight l≤A) →
    ∀(X₁ X₂ Y₁ Y₂ : labels→ℝ),
      (∀l,0<X₁ l ∧ 0<X₂ l ∧ X₁ l≤CX₁ ∧ X₂ l≤CX₂) →
      (∀l,0<Y₁ l ∧ 0<Y₂ l ∧ Y₁ l≤CY₁ ∧ Y₂ l≤CY₂) →
      (∀l,Y₁ l*Y₂ l=X₁ l*X₂ l) →
    ∀(parentR A₁ A₂ : labels→Ideal O)(d : IdealPair),GoodPair d →
      (∀l,A₁ l≠0) → (∀l,A₂ l≠0) → (∀l,A₁ l*A₂ l∣parentR l) →
      (∀l,mask l=parentR l*(d.1*d.2)) →
      (∀i∈F,∀I∈primePool rayModulus Hray slotUpper (Z^(w i)),IsCoprime I (d.1*d.2)) →
    ∀(δ Brestore : ℝ),0<δ → 0≤Brestore →
      (∀l,b^2*X₁ l*X₂ l≤Z^Brestore) →
      (∑l : labels,‖frozenCenteredRow
        (rowWeight (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l) t) W₁ W₂
        (A₁ l*d.1) (A₂ l*d.2) b (X₁ l) (X₂ l) (Y₁ l) (Y₂ l) (X₁ l*X₂ l)*
        (∏i:F,normalizedSlot (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l)
          (primePool rayModulus Hray slotUpper (Z^(w i)))
          (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
          t (Z^(w i)))‖^2*weight l)≤
      2*(holeDeletionMass*((eulerBound 5 (1/2+δ/(Brestore+1))+
        eulerBound 432 (1/2+δ/(Brestore+1)))*Z^δ))^2*(
      C*Z^loss*A*((∏I∈ps (R*H),I).absNorm:ℝ)^εmask*
        ((1+2*(Real.log (max 1 CX₁)-Real.log (profileFloor b)))*
          ((1+2*(Real.log (max 1 CX₂)-Real.log (profileFloor b)))*
          globalRawBudget CP DP TP degreeP Φ
            (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t)
            (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) t height Z M εsource)) +
      C*Z^loss*A*((∏I∈ps (R*H),I).absNorm:ℝ)^εmask*
        ((1+2*(Real.log (max 1 CY₁)-Real.log (profileFloor b)))*
          ((1+2*(Real.log (max 1 CY₂)-Real.log (profileFloor b)))*
          globalRawBudget CP DP TP degreeP Φ
            (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t)
            (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) t height Z M εsource))) := by
  obtain ⟨TP,DP,C,hDP,hC,hraw⟩:=global_fixed_missing_positive_variable_shortened (α:=α)
    rayModulus Hray hH Mslot hMslot slotUpper B loss εmask hB hloss hεmask SP
  refine ⟨TP,DP,C,hDP,hC,?_⟩
  intro F Bprev lam hprev hlam W a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ₂
    η η₀ Q degreeP CP hCP hp left u₀ unit H hH0 labels
    hrow hsupport hsupported heq hnorm hmissing R hR hkeep
    τ z mask physical hmask hdict W₁ W₂ ha hb hs₁ hs₂
    θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    M mx₁ mx₂ my₁ my₂ cap hMlo hMhi hslotcap hcapacityX hcapacityY hcap Φ hΦs hΦ
    CX₁ CX₂ CY₁ CY₂ hCX₁ hCX₂ hCY₁ hCY₂ hx₁ hx₂ hy₁ hy₂ A weight hcover hA hweight hweightA
    X₁ X₂ Y₁ Y₂ hX hY hXY parentR A₁ A₂ d hd hA₁ hA₂ hAR hmaskEq havoid
    δ Brestore hδ hBrestore hcut
  let budget := fun C₁ C₂ : ℝ=>C*Z^loss*A*((∏I∈ps (R*H),I).absNorm:ℝ)^εmask*
        ((1+2*(Real.log (max 1 C₁)-Real.log (profileFloor b)))*
          ((1+2*(Real.log (max 1 C₂)-Real.log (profileFloor b)))*
          globalRawBudget CP DP TP degreeP Φ
            (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t)
            (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) t height Z M εsource))
  have raw (C₁ C₂ m₁ m₂ : ℝ) (hc₁ : 0<C₁) (hc₂ : 0<C₂)
      (hlen₁ : length Z C₁≤m₁) (hlen₂ : length Z C₂≤m₂)
      (hcapacity : m₁+m₂+lam*cap≤Bprev*M)
      (V₁ V₂ Z₁ Z₂ : labels→ℝ)
      (hV : ∀l,0<V₁ l ∧ 0<V₂ l ∧ V₁ l≤C₁ ∧ V₂ l≤C₂)
      (hZ : ∀l,0<Z₁ l ∧ 0<Z₂ l ∧ Z₁ l≤V₁ l ∧ Z₂ l≤V₂ l) :
      (∑l : labels,‖positiveSlotRow (τ l) (fixedBadMask*idealGenerator (parentR l*(d.1*d.2)))
        1 (z l) W₁ W₂ (fun i:F=>primePool rayModulus Hray slotUpper (Z^(w i)))
        (fun (i:F) I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
        (fun i:F=>Z^(w i)) t (Z₁ l) (Z₂ l)‖^2*weight l)≤budget C₁ C₂ := by
    have hr:=hraw F Bprev lam hprev hlam W a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ₂
      η η₀ Q degreeP CP hCP hp left u₀ unit H hH0 labels
      hrow hsupport hsupported heq hnorm hmissing R hR hkeep
      τ z mask physical hmask hdict W₁ W₂ ha hb hs₁ hs₂
      θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
      M m₁ m₂ cap hMlo hMhi hslotcap hcapacity hcap Φ hΦs hΦ
      C₁ C₂ hc₁ hc₂ hlen₁ hlen₂ A weight hcover hA hweight hweightA
      V₁ V₂ Z₁ Z₂ hV hZ
    simpa only [budget,hmaskEq,mul_comm] using hr
  have hxraw:=raw CX₁ CX₂ mx₁ mx₂ hCX₁ hCX₂ hx₁ hx₂ hcapacityX X₁ X₂
  have hyraw:=raw CY₁ CY₂ my₁ my₂ hCY₁ hCY₂ hy₁ hy₂ hcapacityY Y₁ Y₂
  have hEx : 0≤budget CX₁ CX₂ := le_trans
    (Finset.sum_nonneg (by intro l hl;exact mul_nonneg (sq_nonneg _) (hweight l)))
    (hxraw X₁ X₂ hX (fun l=>⟨(hX l).1,(hX l).2.1,le_rfl,le_rfl⟩))
  have hEy : 0≤budget CY₁ CY₂ := le_trans
    (Finset.sum_nonneg (by intro l hl;exact mul_nonneg (sq_nonneg _) (hweight l)))
    (hyraw Y₁ Y₂ hY (fun l=>⟨(hY l).1,(hY l).2.1,le_rfl,le_rfl⟩))
  have hn:=newton_positive_variable_two_corner_family Finset.univ τ (fun _=>t) weight z
    (fun l _=>hweight l) parentR A₁ A₂ (fun l _=>hA₁ l) (fun l _=>hA₂ l)
    (fun l _=>hAR l) d hd W₁ W₂ b hb
    (hs₁.trans (by intro x hx;exact hx.2)) (hs₂.trans (by intro x hx;exact hx.2))
    (fun i:F=>primePool rayModulus Hray slotUpper (Z^(w i)))
    (fun (i:F) I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
    (fun i:F=>Z^(w i)) (fun i=>Real.rpow_pos_of_pos (show 0<Z by linarith) _)
    (fun i I hI=>havoid i.val i.property I hI) X₁ X₂ Y₁ Y₂
    (fun l _=>⟨(hX l).1,(hX l).2.1⟩) (fun l _=>⟨(hY l).1,(hY l).2.1⟩)
    (fun l _=>hXY l) (budget CX₁ CX₂) (budget CY₁ CY₂) δ Brestore Z hEx hEy hδ hBrestore (by linarith)
    (fun l _=>hcut l)
    (fun Z₁ Z₂ hz=>hxraw Z₁ Z₂ hX (fun l=>hz l (Finset.mem_univ l)))
    (fun Z₁ Z₂ hz=>hyraw Z₁ Z₂ hY (fun l=>hz l (Finset.mem_univ l)))
  apply le_trans (le_of_eq ?_) hn
  apply Finset.sum_congr rfl
  intro l hl
  rw [normalized_slots_product (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l)
    (fun i:F=>primePool rayModulus Hray slotUpper (Z^(w i)))
    (fun (i:F) I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
    (fun i:F=>Z^(w i)) (fun i=>Real.rpow_pos_of_pos (show 0<Z by linarith) _) t]
  rfl


end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.global_fixed_missing_frozen_variable_corners
