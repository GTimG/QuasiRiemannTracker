/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual positive row families from one fixed-anchor earlier global source. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalLowGlobalSource
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.RetainedLowErasedCollectedCells
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Low.CoupledAdmission
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission
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
local instance lowGlobalQuotientFinite (rayModulus:Ideal O)[NeZero rayModulus]:Finite (O⧸rayModulus):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)

theorem global_low_erased_collected_cells (Bprev lam hprev Mmin Mmax εsource:ℝ)
    (hG:GlobalSource Bprev lam hprev)(hBprev:0≤Bprev)(hhprev:0≤hprev)(hMmin:0<Mmin)(hεsource:0<εsource)(hlam:0≤lam):
    ∃meshMax:ℝ,0<meshMax ∧ ∀mesh:ℝ,mesh≤meshMax→
    ∀(α:Type)[Fintype α][DecidableEq α],
    ∀(rayModulus:Ideal O)[NeZero rayModulus](Hray:Subgroup (O⧸rayModulus)ˣ)
      (hH:RayOrthogonality.globalUnits rayModulus≤Hray),
    ∀(Mslot:α→ℝ),(∀i,0≤Mslot i)→
    ∀(B loss εmask:ℝ),0≤B→0<loss→0<εmask→
    ∀q:ℝ,0≤q→q≤1→∀W:ℝ→ℂ,Function.support W⊆Icc (1:ℝ) 2→ContDiff ℝ ∞ W→
    ∀(Rwidth dmax τlow εlow e κ η bΦ Mcap Bmask margin densityWidth:ℝ),
      0≤Rwidth→0≤dmax→0<τlow→0<εlow→0<e→e<1/1000→0<κ→0≤η→
      8*e*Rwidth+κ≤εlow→2≤bΦ→0<margin→0<densityWidth→Mcap+Bmask+margin≤densityWidth→densityWidth≤dmax→
    ∀(ηanchor η₀:Character)(Q:Ideal O),Q≤rayModulus→internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃degreeP:ℕ,∃SP TP:Finset (ℕ×ℕ),∃CP DP C Cslot:ℝ,0<CP ∧ 0<DP ∧ 0<C ∧ 1≤Cslot ∧
    ∀ᶠZ:ℝ in atTop,2≤Z ∧
    ∀T : Finset α,
    ∀(reflected second : Bool)(s : Input α)(modifier : CenteredMomentAddedZeroUniform.Tuple α→ℂ)
      (R₀ seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ)),R₀≠0 →
      s.η=ηanchor →
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
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ))(ha : 0<(1/4:ℝ))(hb : 0≤(9/4:ℝ))
      (hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc (1/4:ℝ) (9/4:ℝ))
      (hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc (1/4:ℝ) (9/4:ℝ)),
    ∀(θ : α→RayQuotient.Characters rayModulus Hray)(w σ freq : α→ℝ)(t height : ℝ),
      (∀i∈T,0≤w i) → (∀i∈T,w i≤mesh) →
      (∀i∈T,(33/50:ℝ)≤σ i) → (∀i∈T,σ i≤(33/50:ℝ)) → 0≤height → (∀i∈T,|freq i|≤height) →
      (∀i∈T,∀I∈primePool rayModulus Hray (2:ℝ) (Z^(w i)),Prime I) →
      (∀i∈T,∀I∈primePool rayModulus Hray (2:ℝ) (Z^(w i)),
        ‖idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I‖≤Mslot i) →
      (∀i∈T,∀I∈primePool rayModulus Hray (2:ℝ) (Z^(w i)),
        idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I≠0 →
        (I.absNorm:ℝ)≤(2:ℝ)*Z^(w i)) →
    ∀(Φ : 𝓢(ℝ,ℂ)),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
    ∀weight : labels→ℝ,(∀l,0≤weight l) →
    ∀(X₁ X₂ : labels→ℝ),
      (∀l,0<X₁ l ∧ 0<X₂ l) →
    ∀(A₁ A₂ : labels→Ideal O),
      (∀l,A₁ l≠0) → (∀l,A₂ l≠0) → (∀l,A₁ l*A₂ l∣parentR l) →
      (∀i∈T,∀I∈primePool rayModulus Hray (2:ℝ) (Z^(w i)),IsCoprime I (d.1*d.2)) →
    ∀(δ Brestore : ℝ),0<δ → 0≤Brestore →
      (∀l,(9/4:ℝ)^2*X₁ l*X₂ l≤Z^Brestore) →
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
      (∀i∈T,(33/50:ℝ)≤σ i) → (∀i∈T,σ i≤(33/50:ℝ)) →
      (∀l,∀j∈T,|t+freq j|+Z^τlow/2≤(3*iBin l+2:ℕ)*Z^τlow) →
      (∀l,(3+(3*iBin l+2:ℕ)*Z^τlow)^2≤(Z^densityWidth)^η) →
      (∀l,ActualLow rayModulus Hray hH (st l) η₀ (hQM l) (hQη l) (aLow l) e
        (3*(iBin l+1:ℕ)*Z^τlow) (z l)) →
    let D:=fun l : labels=>RetainedLow.positiveFrozenRow
      (rowWeight (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l) t) W₁ W₂
      (A₁ l*d.1) (A₂ l*d.2) (9/4:ℝ) (X₁ l) (X₂ l) (X₁ l*X₂ l)
    let slot:=fun (l : labels) i=>normalizedSlot (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l)
      (primePool rayModulus Hray (2:ℝ) (Z^(w i)))
      (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) t (Z^(w i))
    let value:=fun l : labels=>D l*∏i:T,slot l i
    ∀(select : labels→Finset α)(radius : labels→ℝ)(cellWidth : ℝ),0<cellWidth →
      (∀l,select l⊆T) →
      (∀l,value l≠0 → Mmin≤radius l ∧ radius l≤Mmax) →
      (∀l,value l≠0 → ‖eisEmbedding (nonzeroJointSourceRow l.val).val‖^2≤Z^(radius l)) →
      (∀x∈Set.Icc (0:ℝ) 1,1≤(Φ x).re) →
      (∀l,value l≠0 → RoundedPairAdmission (globalFace Bprev lam hprev) Z
        (X₁ l) (X₂ l) cellWidth (∑i∈select l,w i) (radius l)) →
    ∀Acell : Finset α→(Fin 3→ℤ)→ℝ,(∀F k,0≤Acell F k) →
      (∀l,value l≠0 → weight l≤Acell (select l)
        (RegularLowScaleGrouping.key cellWidth Z (X₁ l) (X₂ l) (radius l))) →
    let live:=(Finset.univ : Finset labels).filter (fun l=>value l≠0)
    let tag:=fun l : labels=>RegularLowScaleGrouping.key cellWidth Z (X₁ l) (X₂ l) (radius l)
    let budget:=fun (F : Finset α) (k : Fin 3→ℤ)=>
      erasurePayment Z q (Cslot*Z^(2*εlow*densityWidth)) w T F*(128*(Fintype.card RayCharacter:ℝ)^2*
      ((holeDeletionMass*((eulerBound 5 (1/2+δ/(Brestore+1))+
        eulerBound 432 (1/2+δ/(Brestore+1)))*Z^δ))^2*(
      C*Z^loss*(Acell F k)*
        ((1+2*(Real.log (max 1 (Z^(exponentBinUpper cellWidth k 0)))-Real.log (profileFloor (9/4:ℝ))))*
          ((1+2*(Real.log (max 1 (Z^(exponentBinUpper cellWidth k 1)))-Real.log (profileFloor (9/4:ℝ))))*
          globalRawBudget CP DP TP degreeP Φ
            (normPowerProfile W₁ (1/4:ℝ) (9/4:ℝ) ha hs₁ (W₁.smooth ⊤) t)
            (normPowerProfile W₂ (1/4:ℝ) (9/4:ℝ) ha hs₂ (W₂.smooth ⊤) t) t height Z
            (RegularLowScaleGrouping.radial cellWidth Mmax k) εsource))))*
      ((∏I∈ps ((geometryRawFixedMask s R₀*L)*(d.1*d.2)),I).absNorm:ℝ)^εmask*
        Z^(hi*(1+εmask)-γ*lo))
    (∑l : labels,‖value l‖^2*(weight l*((firstSourceMissing left l.val.val.1).absNorm:ℝ)^(-γ)))≤
        ∑F∈T.powerset,∑k∈(live.filter (fun l=>select l=F)).image tag,budget F k := by
  obtain ⟨meshMax,hm,hglobal⟩:=High.GlobalPhysical.global_low_erased_positive_family
    Bprev lam hprev Mmin Mmax εsource hG hMmin hεsource hlam
  refine ⟨meshMax,hm,?_⟩
  intro mesh hmesh α _ _ rayModulus _ Hray hH Mslot hMslot B loss εmask hB hloss hεmask
    q hq0 hq1 W hWs hW Rwidth dmax τlow εlow e κ η bΦ Mcap Bmask margin densityWidth
    hRw hdmax hτ hεlow he he' hκ hη hbudget hbΦ hmargin hdensity hdsupply hdm
    ηanchor η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degreeP,SP,TP,CP,DP,C,Cslot,hCP,hDP,hC,hCslot,hfamilies⟩:=hglobal mesh hmesh α
    rayModulus Hray hH Mslot hMslot B loss εmask hB hloss hεmask q hq0 hq1 W hWs hW
    Rwidth dmax τlow εlow e κ η bΦ Mcap Bmask margin densityWidth
    hRw hdmax hτ hεlow he he' hκ hη hbudget hbΦ hmargin hdensity hdsupply hdm
    ηanchor η₀ Q hQray hQ0 hQt hQ72
  refine ⟨degreeP,SP,TP,CP,DP,C,Cslot,hCP,hDP,hC,hCslot,?_⟩
  filter_upwards [hfamilies] with Z hZdata
  refine ⟨hZdata.1,?_⟩
  have hZ : 1<Z:=by linarith [hZdata.1]
  intro T reflected second s modifier R₀ seed K ξ hK bin hR₀ hanchor
    left unit labels ray₁ ray₂ DataLabel _ column datum first row hfirst hparent hchild hkey hray
    L hL Cf hLC hCL d hd τ z parentR hrow hsupport hnorm hnonfixed
    W₁ W₂ ha hb hs₁ hs₂ θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    Φ hΦs hΦ weight hweight X₁ X₂ hX A₁ A₂ hA₁ hA₂ hAR havoid δ Brestore hδ hBrestore hcut
    lo hi γ hγ hlo hhi st hQM hQη hcharacter hpuncture hwidth hkeep
    aLow iBin haLow haLow' hwT hwr hσT hσT' hfreq hheight hlow
    D slot value select radius cellWidth hcw hselect hradius hradial hΦone hadmit
    Acell hAcell hweightA live tag budget
  refine RetainedLow.selected_scale_sum_le (Finset.univ : Finset labels) T select
    (fun l _=>hselect l) tag value
    (fun l=>weight l*((firstSourceMissing left l.val.val.1).absNorm:ℝ)^(-γ)) budget ?_
  intro F hF k hk
  have hFT : F⊆T:=Finset.mem_powerset.mp hF
  let rows:=(live.filter (fun l=>select l=F)).filter (fun l=>tag l=k)
  let keys:=RetainedLow.originalKeyCarrier labels rows
  let inc : keys→labels:=RetainedLow.originalKeyInclusion labels rows
  have hmem (l : keys) : inc l∈rows:=RetainedLow.originalKeyInclusion_mem labels rows l
  have hactive (l : keys) : value (inc l)≠0:=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (hmem l)).1).1).2
  have hselectF (l : keys) : select (inc l)=F:=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (hmem l)).1).2
  have htag (l : keys) : tag (inc l)=k:=(Finset.mem_filter.mp (hmem l)).2
  obtain ⟨r₀,hr₀,hkr₀⟩:=Finset.mem_image.mp hk
  have hractive : value r₀≠0:=(Finset.mem_filter.mp (Finset.mem_filter.mp hr₀).1).2
  have hrselect : select r₀=F:=(Finset.mem_filter.mp hr₀).2
  have hrange:=RegularLowScaleGrouping.same_key_radial cellWidth Z (X₁ r₀) (X₂ r₀)
    (radius r₀) Mmin Mmax hcw k hkr₀ (hradius r₀ hractive).1 (hradius r₀ hractive).2
  have hplain:=RegularLowScaleGrouping.same_key_plain_envelopes cellWidth Z (X₁ r₀) (X₂ r₀)
    (radius r₀) hcw hZ k hkr₀
  have had:=RegularLowScaleGrouping.same_key_face_admission cellWidth Z (X₁ r₀) (X₂ r₀)
    (radius r₀) Mmin Mmax Bprev lam hprev (∑i∈F,w i) hcw hZ hBprev hhprev k hkr₀
    (hradius r₀ hractive).1 (hradius r₀ hractive).2
    (by
      intro n₁ n₂ hn₁ hn₂ he₁ he₂
      have ha:=hadmit r₀ hractive n₁ n₂ hn₁ hn₂ he₁ he₂
      rw [hrselect] at ha
      exact ha)
  have hcap : (∑i∈F,w i)≤hprev*RegularLowScaleGrouping.radial cellWidth Mmax k ∧
      exponentBinUpper cellWidth k 0+exponentBinUpper cellWidth k 1+lam*(∑i∈F,w i)≤
        Bprev*RegularLowScaleGrouping.radial cellWidth Mmax k := by
    exact (globalFace_admissible_iff hplain.1 hplain.2.1
      (Finset.sum_nonneg (fun i hi=>hw i (hFT hi))) hlam).mp had
  have hkc (l : keys):=RegularLowScaleGrouping.same_key_plain_envelopes cellWidth Z
    (X₁ (inc l)) (X₂ (inc l)) (radius (inc l)) hcw hZ k (htag l)
  have hcover (l : keys) : 1≤(Φ (‖eisEmbedding (nonzeroJointSourceRow l.val).val‖^2/
      Z^(RegularLowScaleGrouping.radial cellWidth Mmax k))).re := by
    have hm:=RegularLowScaleGrouping.same_key_radial cellWidth Z (X₁ (inc l)) (X₂ (inc l))
      (radius (inc l)) Mmin Mmax hcw k (htag l)
      (hradius (inc l) (hactive l)).1 (hradius (inc l) (hactive l)).2
    apply hΦone _
    refine ⟨div_nonneg (sq_nonneg _) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _),?_⟩
    apply (div_le_one (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)).mpr
    exact (hradial (inc l) (hactive l)).trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le hm.2.2.1)
  have hs:=hZdata.2 T F hFT reflected second s modifier R₀ seed K ξ hK bin hR₀ hanchor
    keys ray₁ ray₂ (fun l=>column (inc l)) datum first (fun l=>row (inc l))
    (fun l=>hfirst (inc l)) (fun l=>hparent (inc l)) (fun l=>hchild (inc l))
    (fun l=>hkey (inc l)) (fun l=>hray (inc l))
    L hL (fun l=>Cf (inc l)) (fun l=>hLC (inc l)) (fun l=>hCL (inc l)) d hd
    (by intro l hl;obtain ⟨r,hr,he⟩:=Finset.mem_image.mp hl;subst l;exact hrow r.val r.property)
    (by intro l hl;obtain ⟨r,hr,he⟩:=Finset.mem_image.mp hl;subst l;exact hsupport r.val r.property)
    (by intro l hl;obtain ⟨r,hr,he⟩:=Finset.mem_image.mp hl;subst l;exact hnorm r.val r.property)
    (fun l=>hnonfixed (inc l))
    W₁ W₂ ha hb hs₁ hs₂ θ w σ freq t height
    (fun i hi=>hw i (hFT hi)) (fun i hi=>hwm i (hFT hi))
    (fun i hi=>hσlo i (hFT hi)) (fun i hi=>hσhi i (hFT hi)) hh
    (fun i hi=>hv i (hFT hi)) (fun i hi=>hprime i (hFT hi))
    (fun i hi=>hβ i (hFT hi)) (fun i hi=>hslot i (hFT hi))
    (RegularLowScaleGrouping.radial cellWidth Mmax k) (exponentBinUpper cellWidth k 0)
    (exponentBinUpper cellWidth k 1) (∑i∈F,w i) hrange.1 hrange.2.1 hcap.1 hcap.2 (le_refl _)
    Φ hΦs hΦ (Z^(exponentBinUpper cellWidth k 0)) (Z^(exponentBinUpper cellWidth k 1))
    hplain.2.2.2.2.1 hplain.2.2.2.2.2.1 (le_of_eq hplain.2.2.2.2.2.2.1)
    (le_of_eq hplain.2.2.2.2.2.2.2.1) (Acell F k) (fun l=>weight (inc l)) hcover
    (hAcell F k) (fun l=>hweight (inc l))
    (by
      intro l
      have he:=hweightA (inc l) (hactive l)
      change weight (inc l)≤Acell (select (inc l)) (tag (inc l)) at he
      rwa [hselectF l,htag l] at he)
    (fun l=>X₁ (inc l)) (fun l=>X₂ (inc l))
    (fun l=>⟨(hX (inc l)).1,(hX (inc l)).2,(hkc l).2.2.1,(hkc l).2.2.2.1⟩)
    (fun l=>A₁ (inc l)) (fun l=>A₂ (inc l))
    (fun l=>hA₁ (inc l)) (fun l=>hA₂ (inc l)) (fun l=>hAR (inc l)) havoid
    δ Brestore hδ hBrestore (fun l=>hcut (inc l)) lo hi γ hγ
    (by intro l hl;obtain ⟨r,hr,he⟩:=Finset.mem_image.mp hl;subst l;exact hlo r.val r.property)
    (by intro l hl;obtain ⟨r,hr,he⟩:=Finset.mem_image.mp hl;subst l;exact hhi r.val r.property)
    (fun l=>st (inc l)) (fun l=>hQM (inc l)) (fun l=>hQη (inc l))
    (fun l=>hcharacter (inc l)) (fun l=>hpuncture (inc l))
    (fun l=>hwidth (inc l)) (fun l=>hkeep (inc l))
    (fun l=>aLow (inc l)) (fun l=>iBin (inc l))
    (fun l=>haLow (inc l)) (fun l=>haLow' (inc l)) hwT hwr hσT hσT'
    (fun l=>hfreq (inc l)) (fun l=>hheight (inc l)) (fun l=>hlow (inc l))
  change (∑r∈rows,‖value r‖^2*(weight r*((firstSourceMissing left r.val.val.1).absNorm:ℝ)^(-γ)))≤budget F k
  rw [←RetainedLow.originalKeyCarrier_sum labels rows]
  exact hs

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.global_low_erased_collected_cells
