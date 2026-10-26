/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual positive row families from one fixed-anchor earlier global source. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.RetainedLowCollected
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.GlobalPhysicalActualLowErasure
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
noncomputable section
open OAI OAI.SevenEighths
open scoped Classical BigOperators SchwartzMap ContDiff
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
open CenteredMomentCommonRadialData CenteredMomentChildRows RayFourExpansion Cycle61InitialMass
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredExceptionalProfile
open QRH.Record1252270103Source.Admission FirstFamily LowErasure
open CenteredMomentEnergyState Filter Set Cycle61Moment.LowBranch
local notation "source"=>QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource
local notation "O" => HeckeFamily.O
local notation "ps" => CompletedGauss.primeSupport

open CenteredMomentRetainedEnergy CenteredMomentTwist CenteredMomentLattice
open CenteredMomentHeckeSlots CenteredMomentHeckeExpansion CenteredMomentWholeSlotDeletion
open OAI.SevenEighths.Record1252270103Low
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance retainedLowCollectedFinite : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (Hray : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ Hray)

theorem actual_low_erased_positive_family
    (Mslot : α→ℝ) (hMslot : ∀i,0≤Mslot i)
    (slotUpper B loss εmask : ℝ) (hB : 0≤B) (hloss : 0<loss) (hεmask : 0<εmask)
    (q : ℝ) (hq0 : 0≤q) (hq1 : q≤1) (W : ℝ→ℂ) (slotLower : ℝ) (hslo : 0<slotLower)
    (hWs : Function.support W⊆Icc slotLower slotUpper) (hW : ContDiff ℝ ∞ W)
    (Rwidth dmax τlow εlow e κ η σlo σhi bΦ Mcap Bmask margin densityWidth : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τlow) (hεlow : 0<εlow)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤εlow) (hbΦ : 0≤bΦ) (hmargin : 0<margin)
    (hd : 0<densityWidth) (hdsupply : Mcap+Bmask+margin≤densityWidth) (hdm : densityWidth≤dmax)
    (SP : Finset (ℕ×ℕ)) :
    ∃TP : Finset (ℕ×ℕ), ∃DP C Cslot : ℝ, 0<DP ∧ 0<C ∧ 1≤Cslot ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,2≤Z ∧
    ∀(T F : Finset α),F⊆T →
    ∀(Bprev lam hprev : ℝ), 0≤lam →
    ∀(a b mesh Mmin Mmax εsource : ℝ)(Q : Ideal O)(degreeP : ℕ)(CP : ℝ), 0≤CP →
    ∀(reflected second : Bool)(s : Input α)(modifier : CenteredMomentAddedZeroUniform.Tuple α→ℂ)
      (R₀ seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ)),R₀≠0 →
      (∀ray ψ : RayCharacter,
        InitialAffineAt (α:=α) rayModulus Hray hH (SourceFace.mk Bprev lam 0 Bprev 0 hprev) W
          slotUpper a b bΦ mesh σlo σhi Mmin Mmax εsource Z
          (secondFixedDictionary s.η (ray,ψ)) η₀ Q degreeP SP CP) →
    let left:=!reflected
    let unit:=fun l=>(Record12518109Raw.fixedParentUnit left s.η l:O)
    ∀labels : Finset (NonzeroJointSourceLabel left 1 unit),
    ∀ray₁ ray₂ : NonzeroJointSourceLabel left 1 unit→RayCharacter,
    ∀{DataLabel : Type}[Fintype DataLabel],
    ∀(column : labels→FirstColumnIndex (source s modifier R₀ seed K Z ξ hK bin))
      (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
      (row : labels→secondLiveRows (fun l=>(datum l).block)),
    ∀hfirst : ∀l,first (row l).val.1=firstLabel s modifier R₀ seed K Z ξ hK bin (column l),
      (∀l,(datum (row l).val.1).input.η=columnCharacter reflected s modifier R₀ seed K Z ξ hK bin (column l)) →
      (∀l,(datum (row l).val.1).R=R₀*columnIdeal reflected s modifier R₀ seed K Z ξ hK bin (column l)) →
      (∀l,rawKey reflected s modifier R₀ seed K Z ξ hK bin (column l) datum first (row l) (hfirst l) second=l.val) →
      (∀l,dictionaryRay reflected s modifier R₀ seed K Z ξ hK bin (column l)=ray₁ l.val) →
    ∀(L : Ideal O),L≠0 → ∀Cf : labels→Ideal O,
      (∀l,L∣Cf l) → (∀l,Cf l∣L^2) →
    ∀(d : IdealPair),GoodPair d →
    let τ:=fun l=>(datum (row l).val.1).τ (ray₂ l.val)
    let z:=fun l=>if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val
    let parentR:=fun l=>((datum (row l).val.1).R*
      (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))*Cf l;
      (∀l∈labels,((Ideal.span {(nonzeroJointSourceRow l).val}).absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((Ideal.span {(nonzeroJointSourceRow l).val}*firstSourceMissing left l.val.1).absNorm:ℝ)≤Z^B) →
      (∀l∈labels,(l.val.1.1.1.absNorm:ℝ)≤Z^B ∧ (l.val.1.1.2.absNorm:ℝ)≤Z^B ∧
        (l.val.2.1.1.absNorm:ℝ)≤Z^B ∧ (l.val.2.1.2.absNorm:ℝ)≤Z^B) →
      (∀l,¬FixedInducingRow (τ l) (internalQ Q η₀) fixedBadMask 1 (z l)) →
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
    ∀(M m₁ m₂ cap : ℝ),Mmin≤M → M≤Mmax → cap≤hprev*M →
      m₁+m₂+lam*cap≤Bprev*M →
      (∑i∈F,w i)≤cap →
    ∀(Φ : 𝓢(ℝ,ℂ)),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
    ∀(C₁ C₂ : ℝ),0<C₁ → 0<C₂ → length Z C₁≤m₁ → length Z C₂≤m₂ →
    ∀(A : ℝ)(weight : labels→ℝ),
      (∀l : labels,1≤(Φ (‖eisEmbedding (nonzeroJointSourceRow l.val).val‖^2/(Z^M))).re) →
      0≤A → (∀l,0≤weight l) → (∀l,weight l≤A) →
    ∀(X₁ X₂ : labels→ℝ),
      (∀l,0<X₁ l ∧ 0<X₂ l ∧ X₁ l≤C₁ ∧ X₂ l≤C₂) →
    ∀(A₁ A₂ : labels→Ideal O),
      (∀l,A₁ l≠0) → (∀l,A₂ l≠0) → (∀l,A₁ l*A₂ l∣parentR l) →
      (∀i∈T,∀I∈primePool rayModulus Hray slotUpper (Z^(w i)),IsCoprime I (d.1*d.2)) →
    ∀(δ Brestore : ℝ),0<δ → 0≤Brestore →
      (∀l,b^2*X₁ l*X₂ l≤Z^Brestore) →
    ∀(lo hi γ : ℝ),0≤γ →
      (∀l∈labels,Z^lo≤((firstSourceMissing left l.val.1).absNorm:ℝ)) →
      (∀l∈labels,((firstSourceMissing left l.val.1).absNorm:ℝ)≤Z^hi) →
    ∀st : labels→NaturalState Z Bmask bΦ,
    ∀(hQM : ∀l,(st l).fixedModulus≤rayModulus)(hQη : ∀l,(st l).fixedModulus≤η₀.modulus),
      (∀l,(st l).character=τ l) → (∀l,(st l).puncture=parentR l*(d.1*d.2)) →
      (∀l,(st l).width≤Mcap) → (∀l,(st l).radial.keep (z l)) →
    ∀(aLow : labels→ℝ)(iBin : labels→ℕ),
      (∀l,51/100≤aLow l) → (∀l,aLow l≤(1+q)/2) →
      (∀i∈T,0≤w i) → (∀i∈T,w i/densityWidth≤Rwidth) →
      (∀i∈T,σlo≤σ i) → (∀i∈T,σ i≤σhi) →
      (∀l,∀j∈T,|t+freq j|+Z^τlow/2≤(3*iBin l+2:ℕ)*Z^τlow) →
      (∀l,(3+(3*iBin l+2:ℕ)*Z^τlow)^2≤(Z^densityWidth)^η) →
      (∀l,ActualLow rayModulus Hray hH (st l) η₀ (hQM l) (hQη l) (aLow l) e
        (3*(iBin l+1:ℕ)*Z^τlow) (z l)) →
      (∑l : labels,‖RetainedLow.positiveFrozenRow
        (rowWeight (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l) t) W₁ W₂
        (A₁ l*d.1) (A₂ l*d.2) b (X₁ l) (X₂ l) (X₁ l*X₂ l)*
        (∏i:T,normalizedSlot (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l)
          (primePool rayModulus Hray slotUpper (Z^(w i)))
          (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
          t (Z^(w i)))‖^2*(weight l*((firstSourceMissing left l.val.val.1).absNorm:ℝ)^(-γ)))≤
      erasurePayment Z q (Cslot*Z^(2*εlow*densityWidth)) w T F*(128*(Fintype.card RayCharacter:ℝ)^2*
      ((holeDeletionMass*((eulerBound 5 (1/2+δ/(Brestore+1))+
        eulerBound 432 (1/2+δ/(Brestore+1)))*Z^δ))^2*(
      C*Z^loss*A*
        ((1+2*(Real.log (max 1 C₁)-Real.log (profileFloor b)))*
          ((1+2*(Real.log (max 1 C₂)-Real.log (profileFloor b)))*
          globalRawBudget CP DP TP degreeP Φ
            (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t)
            (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) t height Z M εsource))))*
      ((∏I∈ps ((geometryRawFixedMask s R₀*L)*(d.1*d.2)),I).absNorm:ℝ)^εmask*
        Z^(hi*(1+εmask)-γ*lo)) := by
  obtain ⟨TP,DP,C,hDP,hC,hraw⟩:=actual_fixed_seed_low_collected_family (α:=α)
    rayModulus Hray hH Mslot hMslot slotUpper B loss εmask hB hloss hεmask SP
  obtain ⟨Cslot,hCslot,hslots⟩:=actual_restricted_erasure_supplier q hq0 hq1 rayModulus Hray hH
    W slotLower slotUpper hslo hWs hW Rwidth dmax τlow εlow e κ η σlo σhi bΦ Mcap Bmask margin densityWidth
    hRw hdmax hτ hεlow he he' hκ hη hbudget hbΦ hmargin hd hdsupply hdm
  refine ⟨TP,DP,C,Cslot,hDP,hC,hCslot,?_⟩
  intro η₀
  filter_upwards [hslots η₀,eventually_ge_atTop (2:ℝ)] with Z hsZ hZ₂
  refine ⟨hZ₂,?_⟩
  intro T F hFT Bprev lam hprev hlam a b mesh Mmin Mmax εsource
    Q degreeP CP hCP reflected second s modifier R₀ seed K ξ hK bin hR₀ hp
    left unit labels ray₁ ray₂ DataLabel _ column datum first row hfirst hparent hchild hkey hray
    L hL Cf hLC hCL d hdGood τ z parentR hrow hsupport hnorm hnonfixed
    W₁ W₂ ha hb hs₁ hs₂ θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    M m₁ m₂ cap hMlo hMhi hslotcap hcapacity hcap Φ hΦs hΦ
    C₁ C₂ hC₁ hC₂ hx₁ hx₂ A weight hcover hA hweight hweightA
    X₁ X₂ hX A₁ A₂ hA₁ hA₂ hAR havoid δ Brestore hδ hBrestore hcut
    lo hi γ hγ hlo hhi st hQM hQη hchar hpuncture hwidth hkeep aLow iBin haLow haLow'
    hwT hwrT hσloT hσhiT hfreq hheight hlow
  have hr:=hraw F Bprev lam hprev hlam W a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ₂
    η₀ Q degreeP CP hCP reflected second s modifier R₀ seed K ξ hK bin hR₀ hp
    labels ray₁ ray₂ column datum first row hfirst hparent hchild hkey hray
    L hL Cf hLC hCL d hdGood hrow hsupport hnorm hnonfixed
    W₁ W₂ ha hb hs₁ hs₂ θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    M m₁ m₂ cap hMlo hMhi hslotcap hcapacity hcap Φ hΦs hΦ
    C₁ C₂ hC₁ hC₂ hx₁ hx₂ A weight hcover hA hweight hweightA
    X₁ X₂ hX A₁ A₂ hA₁ hA₂ hAR (fun i hi=>havoid i (hFT hi)) δ Brestore hδ hBrestore hcut
    lo hi γ hγ hlo hhi
  let Dplain:=fun l:labels=>RetainedLow.positiveFrozenRow
    (rowWeight (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l) t) W₁ W₂
      (A₁ l*d.1) (A₂ l*d.2) b (X₁ l) (X₂ l) (X₁ l*X₂ l)
  let rowWeight:=fun l:labels=>weight l*((firstSourceMissing left l.val.val.1).absNorm:ℝ)^(-γ)
  have he:= (hsZ.2 Finset.univ T rowWeight Dplain st hQM hQη z (fun _=>t) aLow iBin
    parentR (fun _=>d.1*d.2) θ w σ freq
    (fun l _=>mul_nonneg (hweight l) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun l _=>hwidth l) (fun l _=>hpuncture l) (fun l _=>haLow l) (fun l _=>haLow' l)
    hwT hwrT hσloT hσhiT (fun l _=>hfreq l) (fun l _=>hheight l)
    (fun l _=>havoid) (fun l _ _=>hkeep l) (fun l _ _=>hlow l)).1 F hFT
  have hpay:0≤erasurePayment Z q (Cslot*Z^(2*εlow*densityWidth)) w T F :=
    erasurePayment_nonneg _ _ _ _ _ _ (zero_lt_one.trans hsZ.1).le
      (mul_nonneg (zero_le_one.trans hCslot) (Real.rpow_nonneg (zero_lt_one.trans hsZ.1).le _))
  have he':
      (∑l:labels,‖Dplain l*(∏j:T,normalizedSlot (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l)
        (primePool rayModulus Hray slotUpper (Z^(w j)))
        (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ j)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w j)) (σ j) (freq j) I) t (Z^(w j)))‖^2*rowWeight l)≤
      erasurePayment Z q (Cslot*Z^(2*εlow*densityWidth)) w T F*
      (∑l:labels,‖Dplain l*(∏j:F,normalizedSlot (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l)
        (primePool rayModulus Hray slotUpper (Z^(w j)))
        (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ j)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w j)) (σ j) (freq j) I) t (Z^(w j)))‖^2*rowWeight l) := by
    have hprod (U:Finset α)(l:labels):
        (∏j:U,normalizedSlot (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l)
          (primePool rayModulus Hray slotUpper (Z^(w j)))
          (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ j)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w j)) (σ j) (freq j) I) t (Z^(w j)))=
        (∏j∈U,normalizedSlot (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l)
          (primePool rayModulus Hray slotUpper (Z^(w j)))
          (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ j)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w j)) (σ j) (freq j) I) t (Z^(w j))) :=
      Finset.prod_coe_sort U (fun j:α=>normalizedSlot (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l)
        (primePool rayModulus Hray slotUpper (Z^(w j)))
        (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ j)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w j)) (σ j) (freq j) I) t (Z^(w j)))
    simp_rw [hprod]
    simpa only [retainedNorm,hchar] using he
  exact he'.trans (mul_le_mul_of_nonneg_left hr hpay)

end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.actual_low_erased_positive_family
