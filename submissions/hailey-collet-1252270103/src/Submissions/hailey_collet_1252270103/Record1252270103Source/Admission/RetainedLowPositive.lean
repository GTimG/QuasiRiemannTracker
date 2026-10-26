/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual positive row families from one fixed-anchor earlier global source. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.RetainedLowPositiveCore
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.RetainedLowCofactorDictionary
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.VariableRestorationAdmission
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
open CenteredMomentCommonRadialData CenteredMomentChildRows RayFourExpansion Cycle61InitialMass
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily CenteredExceptionalProfile
open FirstFamily
local notation "source"=>QRH.Record1252270103Source.High.CoupledFirst.geometryFirstSource
local notation "O" => HeckeFamily.O
local notation "ps" => CompletedGauss.primeSupport

open CenteredMomentRetainedEnergy CenteredMomentTwist CenteredMomentLattice
open CenteredMomentHeckeSlots CenteredMomentHeckeExpansion CenteredMomentWholeSlotDeletion
open OAI.SevenEighths.Record1252270103Low
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance retainedLowCofactorFinite : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (Hray : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ Hray)

theorem actual_fixed_seed_low_positive_family
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
    ∀(reflected second : Bool)(s : Input α)(modifier : CenteredMomentAddedZeroUniform.Tuple α→ℂ)
      (R₀ seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))(ray ψ : RayCharacter),
      R₀≠0 → η=secondFixedDictionary s.η (ray,ψ) →
    let left:=!reflected
    let unit:=fun l=>(Record12518109Raw.fixedParentUnit left s.η l:O)
    ∀(H : Ideal O),H≠0 →
    ∀labels : Finset (NonzeroJointSourceLabel left 1 unit),
    ∀{DataLabel : Type}[Fintype DataLabel],
    ∀(column : labels→FirstColumnIndex (source s modifier R₀ seed K Z ξ hK bin))
      (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
      (row : labels→secondLiveRows (fun l=>(datum l).block)),
    ∀hfirst : ∀l,first (row l).val.1=firstLabel s modifier R₀ seed K Z ξ hK bin (column l),
      (∀l,(datum (row l).val.1).input.η=columnCharacter reflected s modifier R₀ seed K Z ξ hK bin (column l)) →
      (∀l,(datum (row l).val.1).R=R₀*columnIdeal reflected s modifier R₀ seed K Z ξ hK bin (column l)) →
      (∀l,rawKey reflected s modifier R₀ seed K Z ξ hK bin (column l) datum first (row l) (hfirst l) second=l.val) →
      (∀l,dictionaryRay reflected s modifier R₀ seed K Z ξ hK bin (column l)=ray) →
    ∀(L : Ideal O),L≠0 → ∀Cf : labels→Ideal O,
      (∀l,L∣Cf l) → (∀l,Cf l∣L^2) →
    ∀(d : IdealPair),GoodPair d →
    let τ:=fun l=>(datum (row l).val.1).τ ψ
    let z:=fun l=>if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val
    let parentR:=fun l=>((datum (row l).val.1).R*
      (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))*Cf l;
      (∀l∈labels,((Ideal.span {(nonzeroJointSourceRow l).val}).absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((Ideal.span {(nonzeroJointSourceRow l).val}*H).absNorm:ℝ)≤Z^B) →
      (∀l∈labels,(l.val.1.1.1.absNorm:ℝ)≤Z^B ∧ (l.val.1.1.2.absNorm:ℝ)≤Z^B ∧
        (l.val.2.1.1.absNorm:ℝ)≤Z^B ∧ (l.val.2.1.2.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,firstSourceMissing left l.val.1=H) →
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
      (∀i∈F,∀I∈primePool rayModulus Hray slotUpper (Z^(w i)),IsCoprime I (d.1*d.2)) →
    ∀(δ Brestore : ℝ),0<δ → 0≤Brestore →
      (∀l,b^2*X₁ l*X₂ l≤Z^Brestore) →
      (∑l : labels,‖RetainedLow.positiveFrozenRow
        (rowWeight (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l) t) W₁ W₂
        (A₁ l*d.1) (A₂ l*d.2) b (X₁ l) (X₂ l) (X₁ l*X₂ l)*
        (∏i:F,normalizedSlot (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l)
          (primePool rayModulus Hray slotUpper (Z^(w i)))
          (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
          t (Z^(w i)))‖^2*weight l)≤
      (holeDeletionMass*((eulerBound 5 (1/2+δ/(Brestore+1))+
        eulerBound 432 (1/2+δ/(Brestore+1)))*Z^δ))^2*(
      C*Z^loss*A*((∏I∈ps (((geometryRawFixedMask s R₀*L)*(d.1*d.2))*H),I).absNorm:ℝ)^εmask*
        ((1+2*(Real.log (max 1 C₁)-Real.log (profileFloor b)))*
          ((1+2*(Real.log (max 1 C₂)-Real.log (profileFloor b)))*
          globalRawBudget CP DP TP degreeP Φ
            (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t)
            (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) t height Z M εsource))) := by
  obtain ⟨TP,DP,C,hDP,hC,hsource⟩:=global_fixed_missing_positive_variable_shortened (α:=α)
    rayModulus Hray hH Mslot hMslot slotUpper B loss εmask hB hloss hεmask SP
  refine ⟨TP,DP,C,hDP,hC,?_⟩
  intro F Bprev lam hprev hlam W a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ₂
    η η₀ Q degreeP CP hCP hp reflected second s modifier R₀ seed K ξ hK bin ray ψ hR₀ hanchor
    left unit H hH0 labels DataLabel _ column datum first row hfirst hparent hchild hkey hray
    L hL Cf hLC hCL d hd τ z parentR hrow hsupport hnorm hmissing hnonfixed
    W₁ W₂ ha hb hs₁ hs₂ θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    M m₁ m₂ cap hMlo hMhi hslotcap hcapacity hcap Φ hΦs hΦ
    C₁ C₂ hC₁ hC₂ hx₁ hx₂ A weight hcover hA hweight hweightA
    X₁ X₂ hX A₁ A₂ hA₁ hA₂ hAR havoid δ Brestore hδ hBrestore hcut
  let commonR:=(geometryRawFixedMask s R₀*L)*(d.1*d.2)
  have hfixed : geometryRawFixedMask s R₀≠0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero s.η.modulus_ne_bot
      (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))) hR₀
  have hcommonR : commonR≠0:=mul_ne_zero (mul_ne_zero hfixed hL) (mul_ne_zero hd.1 hd.2.1)
  have hCf (l : labels) : Cf l≠0 := by
    intro he
    have h:=hCL l
    rw [he] at h
    exact pow_ne_zero 2 hL (zero_dvd_iff.mp h)
  let physical:=fun l=>naturalRow (τ l) (z l) (RetainedLow.actual_row_ne second datum (row l))
  let mask:=fun l=>parentR l*(d.1*d.2)
  have hpbase (l : labels) : (datum (row l).val.1).R*
      (if second then (datum (row l).val.1).D else (datum (row l).val.1).C)≠0 := by
    apply mul_ne_zero
    · rw [hchild l];exact mul_ne_zero hR₀ (column_supported reflected s modifier R₀ seed K Z ξ hK bin (column l)).1
    · cases second
      · exact (datum (row l).val.1).hC.1
      · exact (datum (row l).val.1).hD.1
  have hmask (l : labels) : mask l≠0 :=
    mul_ne_zero (mul_ne_zero (hpbase l) (hCf l)) (mul_ne_zero hd.1 hd.2.1)
  have hpkt (l : labels):=actual_common_mask_extra reflected s modifier R₀ seed K Z ξ hK
    bin (column l) datum first (row l) (hfirst l) (hparent l) hR₀ (hchild l) second ψ
      (Cf l*(d.1*d.2)) (mul_ne_zero (hCf l) (mul_ne_zero hd.1 hd.2.1))
  have hdict (l : labels) (I : Ideal O) :
      idealCoeff (excluded (physical l).character (mask l)) I=
      idealCoeff (excluded (naturalRow η (nonzeroJointSourceRow l.val).val
        (nonzeroJointSourceRow l.val).property).character (commonR*H)) I := by
    have he:=(hpkt l).2 I
    dsimp only at he
    have hfkey : l.val.val.1=firstLabel s modifier R₀ seed K Z ξ hK bin (column l) := by
      rw [←hkey l]
      cases second <;> exact hfirst l
    rw [hkey l,hray l,←hanchor,←hfkey,hmissing l.val l.property] at he
    have he' : idealCoeff (excluded (physical l).character (mask l)) I=
        idealCoeff (excluded (naturalRow η (nonzeroJointSourceRow l.val).val
          (nonzeroJointSourceRow l.val).property).character
            ((geometryRawFixedMask s R₀*(Cf l*(d.1*d.2)))*H)) I := by
      simpa only [physical,mask,parentR,τ,z,mul_assoc] using he
    apply he'.trans
    have hx : (geometryRawFixedMask s R₀*(Cf l*(d.1*d.2)))*H=
        (geometryRawFixedMask s R₀*H)*(Cf l*(d.1*d.2)) := by ring
    have hy : commonR*H=(geometryRawFixedMask s R₀*H)*(L*(d.1*d.2)) := by
      dsimp only [commonR];ring
    rw [hx,hy]
    exact RetainedLow.excluded_forced_seed _ _ L (Cf l) (d.1*d.2)
      (mul_ne_zero hfixed hH0) hL (hCf l) (mul_ne_zero hd.1 hd.2.1) (hLC l) (hCL l) I
  have hkeep (l : labels) : initialKeep η (internalQ Q η₀) (nonzeroJointSourceRow l.val).val := by
    have he:=(actual_initialKeep reflected s modifier R₀ seed K Z ξ hK bin (column l) datum first
      (row l) (hfirst l) (hparent l) hR₀ (hchild l) second ψ (internalQ Q η₀)).mpr
        ⟨RetainedLow.actual_row_ne second datum (row l),hnonfixed l⟩
    simpa only [hkey l,hray l,←hanchor] using he
  have hsupported (l : labels):=RetainedLow.actual_key_support reflected second s modifier R₀ seed K Z ξ hK
    bin (column l) datum first (row l) (hfirst l)
  let E:=C*Z^loss*A*((∏I∈ps (commonR*H),I).absNorm:ℝ)^εmask*
    ((1+2*(Real.log (max 1 C₁)-Real.log (profileFloor b)))*
      ((1+2*(Real.log (max 1 C₂)-Real.log (profileFloor b)))*
      globalRawBudget CP DP TP degreeP Φ
        (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t)
        (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) t height Z M εsource))
  have raw (Y₁ Y₂ : labels→ℝ)
      (hY : ∀l,0<Y₁ l ∧ 0<Y₂ l ∧ Y₁ l≤X₁ l ∧ Y₂ l≤X₂ l) :
      (∑l : labels,‖positiveSlotRow (τ l) (fixedBadMask*idealGenerator (parentR l*(d.1*d.2)))
        1 (z l) W₁ W₂ (fun i:F=>primePool rayModulus Hray slotUpper (Z^(w i)))
        (fun (i:F) I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
        (fun i:F=>Z^(w i)) t (Y₁ l) (Y₂ l)‖^2*weight l)≤E := by
    have hr:=hsource F Bprev lam hprev hlam W a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ₂
      η η₀ Q degreeP CP hCP hp left 1 unit H hH0 labels hrow hsupport
      (by intro l hl;simpa only [hkey ⟨l,hl⟩] using (hsupported ⟨l,hl⟩).1)
      (by intro l hl;simpa only [hkey ⟨l,hl⟩] using (hsupported ⟨l,hl⟩).2)
      hnorm hmissing commonR hcommonR hkeep τ z mask physical hmask hdict
      W₁ W₂ ha hb hs₁ hs₂ θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
      M m₁ m₂ cap hMlo hMhi hslotcap hcapacity hcap Φ hΦs hΦ
      C₁ C₂ hC₁ hC₂ hx₁ hx₂ A weight hcover hA hweight hweightA
      X₁ X₂ Y₁ Y₂ hX hY
    simpa only [E,mask,mul_comm] using hr
  have hE : 0≤E:=le_trans
    (Finset.sum_nonneg (fun l _=>mul_nonneg (sq_nonneg _) (hweight l)))
    (raw X₁ X₂ (fun l=>⟨(hX l).1,(hX l).2.1,le_rfl,le_rfl⟩))
  exact RetainedLow.positive_frozen_finite_family Finset.univ τ (fun _=>t) weight z
    (fun l _=>hweight l) parentR A₁ A₂ (fun l _=>hA₁ l) (fun l _=>hA₂ l)
    (fun l _=>hAR l) d hd W₁ W₂ b
    (hs₁.trans (by intro x hx;exact hx.2)) (hs₂.trans (by intro x hx;exact hx.2))
    (fun i:F=>primePool rayModulus Hray slotUpper (Z^(w i)))
    (fun (i:F) I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
    (fun i:F=>Z^(w i)) (fun i=>Real.rpow_pos_of_pos (show 0<Z by linarith) _)
    (fun i I hI=>havoid i.val i.property I hI) X₁ X₂
    (fun l _=>⟨(hX l).1,(hX l).2.1⟩) E δ Brestore Z hE hδ hBrestore (by linarith)
    (fun l _=>hcut l)
    (fun Y₁ Y₂ hY=>raw Y₁ Y₂ (fun l=>hY l (Finset.mem_univ l)))

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.actual_fixed_seed_low_positive_family
