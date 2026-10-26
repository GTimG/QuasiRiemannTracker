/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual positive row families from one fixed-anchor earlier global source. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.RetainedLowPositive
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.RetainedLowCollectedFibers
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
local instance retainedLowCollectedFinite : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (Hray : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ Hray)

theorem actual_fixed_seed_low_collected_family
    (Mslot : α→ℝ) (hMslot : ∀i,0≤Mslot i)
    (slotUpper B loss εmask : ℝ) (hB : 0≤B) (hloss : 0<loss) (hεmask : 0<εmask)
    (SP : Finset (ℕ×ℕ)) :
    ∃TP : Finset (ℕ×ℕ), ∃DP C : ℝ, 0<DP ∧ 0<C ∧
    ∀F : Finset α,
    ∀(Bprev lam hprev : ℝ), 0≤lam → ∀(W : ℝ→ℂ)
      (a b bΦ mesh σlo σhi Mmin Mmax εsource Z : ℝ),2≤Z →
    ∀(η₀ : Character)(Q : Ideal O)(degreeP : ℕ)(CP : ℝ), 0≤CP →
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
      (∀i∈F,∀I∈primePool rayModulus Hray slotUpper (Z^(w i)),IsCoprime I (d.1*d.2)) →
    ∀(δ Brestore : ℝ),0<δ → 0≤Brestore →
      (∀l,b^2*X₁ l*X₂ l≤Z^Brestore) →
    ∀(lo hi γ : ℝ),0≤γ →
      (∀l∈labels,Z^lo≤((firstSourceMissing left l.val.1).absNorm:ℝ)) →
      (∀l∈labels,((firstSourceMissing left l.val.1).absNorm:ℝ)≤Z^hi) →
      (∑l : labels,‖RetainedLow.positiveFrozenRow
        (rowWeight (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l) t) W₁ W₂
        (A₁ l*d.1) (A₂ l*d.2) b (X₁ l) (X₂ l) (X₁ l*X₂ l)*
        (∏i:F,normalizedSlot (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l)
          (primePool rayModulus Hray slotUpper (Z^(w i)))
          (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
          t (Z^(w i)))‖^2*(weight l*((firstSourceMissing left l.val.val.1).absNorm:ℝ)^(-γ)))≤
      128*(Fintype.card RayCharacter:ℝ)^2*
      ((holeDeletionMass*((eulerBound 5 (1/2+δ/(Brestore+1))+
        eulerBound 432 (1/2+δ/(Brestore+1)))*Z^δ))^2*(
      C*Z^loss*A*
        ((1+2*(Real.log (max 1 C₁)-Real.log (profileFloor b)))*
          ((1+2*(Real.log (max 1 C₂)-Real.log (profileFloor b)))*
          globalRawBudget CP DP TP degreeP Φ
            (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t)
            (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) t height Z M εsource))))*
      ((∏I∈ps ((geometryRawFixedMask s R₀*L)*(d.1*d.2)),I).absNorm:ℝ)^εmask*
        Z^(hi*(1+εmask)-γ*lo) := by
  obtain ⟨TP,DP,C,hDP,hC,hsource⟩:=actual_fixed_seed_low_positive_family (α:=α)
    rayModulus Hray hH Mslot hMslot slotUpper B loss εmask hB hloss hεmask SP
  refine ⟨TP,DP,C,hDP,hC,?_⟩
  intro F Bprev lam hprev hlam W a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ₂
    η₀ Q degreeP CP hCP reflected second s modifier R₀ seed K ξ hK bin hR₀ hp
    left unit labels ray₁ ray₂ DataLabel _ column datum first row hfirst hparent hchild hkey hray
    L hL Cf hLC hCL d hd τ z parentR hrow hsupport hnorm hnonfixed
    W₁ W₂ ha hb hs₁ hs₂ θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    M m₁ m₂ cap hMlo hMhi hslotcap hcapacity hcap Φ hΦs hΦ
    C₁ C₂ hC₁ hC₂ hx₁ hx₂ A weight hcover hA hweight hweightA
    X₁ X₂ hX A₁ A₂ hA₁ hA₂ hAR havoid δ Brestore hδ hBrestore hcut
    lo hi γ hγ hlo hhi
  have hZ : 0<Z:=by linarith
  let commonR:=(geometryRawFixedMask s R₀*L)*(d.1*d.2)
  have hfixed : geometryRawFixedMask s R₀≠0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero s.η.modulus_ne_bot
      (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
      (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))) hR₀
  have hcommonR : commonR≠0:=mul_ne_zero (mul_ne_zero hfixed hL) (mul_ne_zero hd.1 hd.2.1)
  let value:=fun l : labels=>RetainedLow.positiveFrozenRow
    (rowWeight (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l) t) W₁ W₂
    (A₁ l*d.1) (A₂ l*d.2) b (X₁ l) (X₂ l) (X₁ l*X₂ l)*
      (∏i:F,normalizedSlot (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l)
        (primePool rayModulus Hray slotUpper (Z^(w i)))
        (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
        t (Z^(w i)))
  let budget:=C*Z^loss*A*
    ((1+2*(Real.log (max 1 C₁)-Real.log (profileFloor b)))*
      ((1+2*(Real.log (max 1 C₂)-Real.log (profileFloor b)))*
      globalRawBudget CP DP TP degreeP Φ
        (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t)
        (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t) t height Z M εsource))
  let E:=(holeDeletionMass*((eulerBound 5 (1/2+δ/(Brestore+1))+
    eulerBound 432 (1/2+δ/(Brestore+1)))*Z^δ))^2*budget
  have hbudget : 0≤budget := by
    have hf:=profileFloor_bounds b
    have hlog (c : ℝ) : Real.log (profileFloor b)≤Real.log (max 1 c) :=
      Real.log_le_log hf.1 (hf.2.trans (le_max_left _ _))
    have h₁ : 0≤1+2*(Real.log (max 1 C₁)-Real.log (profileFloor b)) := by linarith [hlog C₁]
    have h₂ : 0≤1+2*(Real.log (max 1 C₂)-Real.log (profileFloor b)) := by linarith [hlog C₂]
    have hdia:=QuadraticInitialBound.diagonalControl_nonneg Φ
    dsimp only [budget,globalRawBudget]
    positivity
  have hE : 0≤E:=mul_nonneg (sq_nonneg _) hbudget
  have hsupported (l : labels):=RetainedLow.actual_key_support reflected second s modifier R₀ seed K Z ξ hK
    bin (column l) datum first (row l) (hfirst l)
  have hsupp : ∀l∈labels,Supported l.val.1.1.1 := by
    intro l hl
    simpa only [hkey ⟨l,hl⟩] using (hsupported ⟨l,hl⟩).1.1
  apply RetainedLow.missing_ray_subtype_energy labels ray₁ ray₂ value weight commonR hcommonR
    Z lo hi εmask γ E hZ hεmask.le hγ hE hsupp hlo hhi
  intro H hHmem ray ψ
  obtain ⟨l₀,hl₀,he₀⟩:=Finset.mem_image.mp hHmem
  have hH0 : H≠0:=he₀ ▸ RetainedLow.missing_nonzero labels hsupp l₀ hl₀
  let fiber:=RetainedLow.missingRayFiber labels ray₁ ray₂ H ray ψ
  let inc : fiber→labels:=RetainedLow.fiberInclusion labels ray₁ ray₂ H ray ψ
  have hmiss (l : fiber) : firstSourceMissing left l.val.val.1=H :=
    ((RetainedLow.mem_missingRayFiber labels ray₁ ray₂ H ray ψ l.val).mp l.property).2.1
  have hray₁ (l : fiber) : ray₁ l.val=ray :=
    ((RetainedLow.mem_missingRayFiber labels ray₁ ray₂ H ray ψ l.val).mp l.property).2.2.1
  have hray₂ (l : fiber) : ray₂ l.val=ψ :=
    ((RetainedLow.mem_missingRayFiber labels ray₁ ray₂ H ray ψ l.val).mp l.property).2.2.2
  have hτ (l : fiber) : τ (inc l)=(datum (row (inc l)).val.1).τ ψ := by
    dsimp only [τ]
    exact congrArg (datum (row (inc l)).val.1).τ (hray₂ l)
  have hf:=hsource F Bprev lam hprev hlam W a b bΦ mesh σlo σhi Mmin Mmax εsource Z hZ₂
    (secondFixedDictionary s.η (ray,ψ)) η₀ Q degreeP CP hCP (hp ray ψ)
    reflected second s modifier R₀ seed K ξ hK bin ray ψ hR₀ rfl
    H hH0 fiber (fun l=>column (inc l)) datum first (fun l=>row (inc l))
    (fun l=>hfirst (inc l)) (fun l=>hparent (inc l)) (fun l=>hchild (inc l))
    (fun l=>hkey (inc l)) (fun l=>(hray (inc l)).trans (hray₁ l))
    L hL (fun l=>Cf (inc l)) (fun l=>hLC (inc l)) (fun l=>hCL (inc l)) d hd
    (by intro l hl;exact hrow l ((Finset.mem_filter.mp hl).1))
    (by intro l hl;have he:=hsupport l ((Finset.mem_filter.mp hl).1)
        rw [((RetainedLow.mem_missingRayFiber labels ray₁ ray₂ H ray ψ l).mp hl).2.1] at he
        exact he)
    (by intro l hl;exact hnorm l ((Finset.mem_filter.mp hl).1))
    (fun l hl=>((RetainedLow.mem_missingRayFiber labels ray₁ ray₂ H ray ψ l).mp hl).2.1)
    (by intro l;have hn:=hnonfixed (inc l);rw [hτ l] at hn;exact hn)
    W₁ W₂ ha hb hs₁ hs₂ θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    M m₁ m₂ cap hMlo hMhi hslotcap hcapacity hcap Φ hΦs hΦ
    C₁ C₂ hC₁ hC₂ hx₁ hx₂ A (fun l=>weight (inc l))
    (fun l=>hcover (inc l)) hA (fun l=>hweight (inc l)) (fun l=>hweightA (inc l))
    (fun l=>X₁ (inc l)) (fun l=>X₂ (inc l)) (fun l=>hX (inc l))
    (fun l=>A₁ (inc l)) (fun l=>A₂ (inc l))
    (fun l=>hA₁ (inc l)) (fun l=>hA₂ (inc l)) (fun l=>hAR (inc l)) havoid
    δ Brestore hδ hBrestore (fun l=>hcut (inc l))
  have heq : (∑l : fiber,‖value (inc l)‖^2*weight (inc l))=
      (∑l : fiber,‖RetainedLow.positiveFrozenRow
        (rowWeight ((datum (row (inc l)).val.1).τ ψ)
          (fixedBadMask*idealGenerator (parentR (inc l))) 1 (z (inc l)) t) W₁ W₂
        (A₁ (inc l)*d.1) (A₂ (inc l)*d.2) b (X₁ (inc l)) (X₂ (inc l)) (X₁ (inc l)*X₂ (inc l))*
        (∏i:F,normalizedSlot ((datum (row (inc l)).val.1).τ ψ)
          (fixedBadMask*idealGenerator (parentR (inc l))) 1 (z (inc l))
          (primePool rayModulus Hray slotUpper (Z^(w i)))
          (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
          t (Z^(w i)))‖^2*weight (inc l)) := by
    apply Finset.sum_congr rfl
    intro l _
    dsimp only [value]
    rw [hτ l]
  rw [heq]
  apply hf.trans_eq
  dsimp only [E,budget,commonR]
  ring

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.actual_fixed_seed_low_collected_family
