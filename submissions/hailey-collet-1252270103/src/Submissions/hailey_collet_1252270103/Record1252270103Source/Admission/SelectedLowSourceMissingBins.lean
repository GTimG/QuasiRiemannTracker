/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual positive row families from one fixed-anchor earlier global source. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedLowSourceMissingBinsData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedLowSourceMissingBins
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
local instance lowPaidQuotientFinite (rayModulus:Ideal O)[NeZero rayModulus]:Finite (O⧸rayModulus):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)

open SelectedHighCofactorFamily High.GlobalPhysical SelectedLowPaid SelectedLowDictionary
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open Record12518109Natural Record1252270103Finite Record1252270103StepScalar
open QRH.Record1252270103Graph PhysicalLowReserve High
open OAI.SevenEighths.Record1252270103Source.Collision
theorem global_selected_low_positive_family_missing_bins (Kgraph:ℚ)(n low:Source)(bcell εsource:ℝ)
    (hg:RealGeometry Kgraph n low bcell)(hn:ParentGood n)(hlow:ParentGood low)
    (ha:0<(n.allowance:ℝ))(hq0:0≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
    (hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))(hεsource:0<εsource):
    ∃meshMax:ℝ,0<meshMax ∧ ∀mesh:ℝ,mesh≤meshMax→
    ∀(α:Type)[Fintype α][DecidableEq α],
    ∀(rayModulus:Ideal O)[NeZero rayModulus](Hray:Subgroup (O⧸rayModulus)ˣ)
      (hH:RayOrthogonality.globalUnits rayModulus≤Hray),
    ∀(Mslot:α→ℝ),(∀i,0≤Mslot i)→
    ∀(B loss εmask:ℝ),0≤B→0<loss→0<εmask→
    let q:ℝ:=(n.q:ℝ);
    ∀W:ℝ→ℂ,Function.support W⊆Icc (1:ℝ) 2→ContDiff ℝ ∞ W→
    ∀(Rwidth dmax τlow εlow e κ η bΦ Mcap Bmask margin densityWidth:ℝ),
      0≤Rwidth→0≤dmax→0<τlow→0<εlow→0<e→e<1/1000→0<κ→0≤η→
      8*e*Rwidth+κ≤εlow→2≤bΦ→0<margin→0<densityWidth→Mcap+Bmask+margin≤densityWidth→densityWidth≤dmax→
    ∀(ηanchor η₀:Character)(Q:Ideal O),Q≤rayModulus→internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
    ∃Cslot:ℝ,1≤Cslot ∧
    ∀(N:ℕ)(cellWidth Bscale₀ Bmaskcap δ Brestore εwindow:ℝ),Fintype.card α≤N →
      0<cellWidth → 0≤Bscale₀ → 0<δ → 0≤Brestore → 0<εwindow →
    ∀(B₁ B₂ εpref ell lower radiusMax errv Bmass εmass poolLoss:ℝ),
      0≤B₁→0≤B₂→0<εpref→0<ell→0<lower→0≤radiusMax→0<errv→0≤εmass→
    ∀Φ : 𝓢(ℝ,ℂ),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
      (∀x∈Set.Icc (0:ℝ) 1,1≤(Φ x).re) →
    ∀(missingWidth Bmissing:ℝ),0<missingWidth→0≤Bmissing→
    ∃Cpref:ℝ,0<Cpref ∧ ∃J:ℕ,∃Spaid:Finset (ℕ×ℕ),∃Cpaid:ℝ,0<Cpaid ∧
    ∀ᶠZ:ℝ in atTop,2≤Z ∧
    ∀T : Finset α,
    ∀(reflected second : Bool)(s : Input α)(Am₁ Am₂ Dm Km R₀ seed:Ideal O)(Fm:Ideal O→ℂ)
      (Dparent ξ : ℝ)(hK : 0<Z^Dparent)(bin : ℤ×(Fin 5→ℤ)),R₀≠0 →
      s.η=ηanchor →
    let K:=Z^Dparent;
    let modifier:=markedSourceModifier Am₁ Am₂ Dm Km Fm;
    let left:=!reflected;
    let unit:=fun l=>(Record12518109Raw.fixedParentUnit left s.η l:O);
    ∀{Row : Type}[DecidableEq Row],
    ∀(labels : Finset Row)(key : Row→NonzeroJointSourceLabel left 1 unit),
      Function.Injective (fun l:labels=>key l.val) →
    ∀ray₁ ray₂ : NonzeroJointSourceLabel left 1 unit→RayCharacter,
    ∀{DataLabel : Type}[Fintype DataLabel],
    ∀(column : labels→FirstColumnIndex (source s modifier R₀ seed K Z ξ hK bin))
      (datum : DataLabel→SecondInputDatum α)(first : DataLabel→FirstSourceLabel)
      (row : labels→secondLiveRows (fun l=>(datum l).block)),
    ∀hfirst : ∀l,first (row l).val.1=firstLabel s modifier R₀ seed K Z ξ hK bin (column l),
      (∀l,(datum (row l).val.1).input.η=columnCharacter reflected s modifier R₀ seed K Z ξ hK bin (column l)) →
      (∀l,(datum (row l).val.1).R=R₀*columnIdeal reflected s modifier R₀ seed K Z ξ hK bin (column l)) →
      (∀l,rawKey reflected s modifier R₀ seed K Z ξ hK bin (column l) datum first (row l) (hfirst l) second=key l.val) →
      (∀l,dictionaryRay reflected s modifier R₀ seed K Z ξ hK bin (column l)=ray₁ (key l.val)) →
    ∀sel:∀l:labels,Selection s reflected second
      (firstLabel s modifier R₀ seed K Z ξ hK bin (column l))
      (datum (row l).val.1).C (datum (row l).val.1).D R₀,
    ∀(L : Ideal O),L≠0 →
    let Cf:=fun l:labels=>(sel l).Cf;
      
      (∀l,L∣Cf l) → (∀l,Cf l∣L^2) →
    ∀(Snew Anew:Finset (Ideal O)),
    let d:=newtonDivisorPair Snew Anew;
      GoodPair d →
      ((geometryRawFixedMask s R₀*L)*(d.1*d.2))≠0 →
      (((geometryRawFixedMask s R₀*L)*(d.1*d.2)).absNorm:ℝ)≤Z^Bmaskcap →
    let τ:=fun l=>(datum (row l).val.1).τ (ray₂ (key l.val));
    let z:=fun l=>if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val;
    let parentR:=fun l=>((datum (row l).val.1).R*
      (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))*Cf l;
      (∀l∈labels,((Ideal.span {(nonzeroJointSourceRow (key l)).val}).absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((Ideal.span {(nonzeroJointSourceRow (key l)).val}*firstSourceMissing left (key l).val.1).absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((key l).val.1.1.1.absNorm:ℝ)≤Z^B ∧ ((key l).val.1.1.2.absNorm:ℝ)≤Z^B ∧
        ((key l).val.2.1.1.absNorm:ℝ)≤Z^B ∧ ((key l).val.2.1.2.absNorm:ℝ)≤Z^B) →
      (∀l,¬FixedInducingRow (τ l) (internalQ Q η₀) fixedBadMask 1 (z l)) →
    ∀p : Profiles (1/4:ℝ) (9/4:ℝ),
    let W₁:=p.profile 0
    let W₂:=p.profile 1
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
    ∀corner:Bool,
    let X₁:=fun l:labels=>(if corner then (sel l).finalInput.Y₁ else (sel l).finalInput.X₁)/d.1.absNorm;
    let X₂:=fun l:labels=>(if corner then (sel l).finalInput.Y₂ else (sel l).finalInput.X₂)/d.2.absNorm;
    let A₁:=fun l:labels=>Selection.frozenLeft (sel l);
    let A₂:=fun l:labels=>Selection.frozenRight (sel l);
    ∀(omega:labels→ℝ),(∀l,0≤omega l)→
    let weight:=fun l:labels=>selectedPaidWeight (sel l) (omega l);

      (∀i∈T,∀I∈primePool rayModulus Hray (2:ℝ) (Z^(w i)),IsCoprime I (d.1*d.2)) →
      (∀l,(9/4:ℝ)^2*X₁ l*X₂ l≤Z^Brestore) →
      (∀l:labels,firstSourceMissing left (key l.val).val.1≠0) →
      (∀l:labels,((firstSourceMissing left (key l.val).val.1).absNorm:ℝ)≤Z^Bmissing) →
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
    ∀(U:∀l:labels,Finset (CommonIndex (datum (row l).val.1).C (datum (row l).val.1).D))
      (reserve err rho:labels→ℝ)(width:ℝ)(Wa:𝓢(ℝ,ℂ)),
    let x:=fun l:labels=>childHighCoordinates
      (actualHighCoordinates reflected (!reflected) second
        (firstLabel s modifier R₀ seed K Z ξ hK bin (column l))
        (datum (row l).val.1).C (datum (row l).val.1).D (U l) Z Dparent (Real.logb Z (volume s))
        (sourceAReal n low bcell) ξ (reserve l) (err l)) errv
    let radius:=fun l:labels=>sourceFReal n low bcell-max
      (labelD reflected (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)) Z-
        labelC reflected (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)) Z) 0-rho l
    let annularLoss:=3*(N:ℝ)*Real.logb Z 2+2*Real.logb Z (max 1 (9/4:ℝ))+2*cellWidth
    (∀l,T⊆(sel l).full) →
    s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) →
    (∀i∈T,s.slots i=primePool rayModulus Hray (2:ℝ) (Z^(w i))) →
    (∀i∈T,restoredSlotCoeff s i=(fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)) →
    (∀i,s.P i=Z^(w i)) → (∀i,0≤w i) → (∑i,w i)≤bcell →
    1≤s.lower → s.upper≤2 → Squarefree seed →
    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass →
    (∀l,Supported (datum (row l).val.1).C) →
    length Z s.X₁+length Z s.X₂≤plainBudget n bcell width →
    0≤mesh → mesh≤(n.allowance:ℝ)/4 →
    0≤width → width≤PhysicalLowGuard.step n → cellWidth≤(n.allowance:ℝ)/4 →
    errv≤(n.allowance:ℝ)/4 →
    (∀l,err l≤(n.allowance:ℝ)/4) →
    (∀l,0≤rho l ∧ rho l≤(n.allowance:ℝ)/4) →
    (∀l,max (labelD reflected (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)) Z-
      labelC reflected (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)) Z) 0≤
        labelC reflected (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)) Z) →
    0≤annularLoss → annularLoss≤(n.allowance:ℝ)/4 →
    (∀l,annularLoss+(low.B:ℝ)*rho l+2*(n.allowance:ℝ)≤
      (low.B:ℝ)*sourceFReal n low bcell-plainBudget n bcell width-bcell) →
    (∀l,radius l≤x l 2+cellWidth) →
    (∀l,value l≠0 → radius l≤2) →
    (∀l,value l≠0 → ‖eisEmbedding (nonzeroJointSourceRow (key l.val)).val‖^2≤Z^(radius l)) →
    (∀l,value l≠0 → X₁ l≤Z^Bscale₀ ∧ X₂ l≤Z^Bscale₀) →
    (∀l:labels,((firstSourceMissing left (key l.val).val.1).absNorm:ℝ)≤Z^(x l 1)) →
    ∀(P:Finset (Ideal O))(poolMesh BD Bsource:ℝ)(depth:ℕ)(H0 mainRadius:labels→ℝ),
      Pool.FixedCellPoolData P Z (sourceAReal n low bcell) ell poolMesh poolLoss BD Bsource depth →
      (∀l,0<H0 l) →
      (∀l,0≤mainRadius l+6*sourceAReal n low bcell ∧ mainRadius l+6*sourceAReal n low bcell≤radiusMax) →
      (∀l,((if reflected then (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)).1.2
        else (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)).1.1).absNorm:ℝ)≤Z^B₁) →
      (∀l,((if second then (datum (row l).val.1).D else (datum (row l).val.1).C).absNorm:ℝ)≤Z^B₂) →
    let extra:=fun l:labels=>((CenteredMomentFirstAnnularMajorant.bands (H0 l)).card:ℝ)*
      ((actualAllocations s.pools (if reflected then (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)).1.2
        else (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)).1.1)).card:ℝ)^2/(P.card:ℝ)*
        ((mainRadius l+6*sourceAReal n low bcell)/ell);
    (∀l,omega l≤
      (‖CoupledFirst.balancedColumnScalar reflected s modifier R₀ seed K Z ξ Dparent
        (Real.logb Z (volume s)) hK bin
        (fun q=>normPhase (CoupledFirst.coordinateBlock s modifier R₀ seed Wa K Z ξ q)) (column l)‖^2*
        extra l*‖frozenCoefficient (sel l).B₁.val
          (if reflected then (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)).1.2
            else (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)).1.1) R₀ s.ν s.W s.P‖^2/volume s)*
        (firstMainRadius reflected K (volume s) Z ξ (3*sourceAReal n low bcell) (reserve l)
          (firstLabel s modifier R₀ seed K Z ξ hK bin (column l))/lower)*
        normalizer (datum (row l).val.1).C (datum (row l).val.1).D (U l)) →
    (∑l:labels,‖positiveNewtonCofactorPlain corner (sel l).finalInput (A₁ l) (A₂ l)
      (Selection.puncture (sel l)) (9/4:ℝ) Snew Anew (τ l) t (z l)*
      (∏i:T,normalizedSlot (τ l) (fixedBadMask*idealGenerator (Selection.puncture (sel l))) 1 (z l)
        (s.slots i) (restoredSlotCoeff s i) t (s.P i))‖^2*weight l)≤
      Cpaid*(p.control Spaid)^2*(1+|t|+height)^J*
        (Cpref*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4:ℝ) (1/4:ℝ)) bin*
          forcedProfileCost s*(max 1 (forcedProfileCost s))^2)*Cslot^N*
        Z^(-8*(n.allowance:ℝ)+εpref+poolLoss+Bmass*εmass+cellWidth+missingWidth+εmask*(Bmissing+missingWidth)+
          2*εlow*densityWidth*N+εsource+loss+2*δ+Bmaskcap*εmask+εwindow) := by
  obtain ⟨meshMax,hm,hglobal⟩ := SelectedLowSourceReindex.global_selected_low_positive_family_injective
    Kgraph n low bcell εsource hg hn hlow ha hq0 hq1 hG hεsource
  refine ⟨meshMax,hm,?_⟩
  intro mesh hmesh α instα decα rayModulus _ Hray hH Mslot hMslot B loss εmask hB hloss hεmask q
    W hWs hW Rwidth dmax τlow εlow e κ η bΦ Mcap Bmask margin densityWidth
    hRw hdmax hτ hεlow he he' hκ hη hbudget hbΦ hmargin hdensity hdsupply hdm
    ηanchor η₀ Q hQray hQ0 hQt hQ72
  have hsourceResult:=hglobal mesh hmesh α rayModulus Hray hH Mslot hMslot B loss εmask hB hloss hεmask
    W hWs hW Rwidth dmax τlow εlow e κ η bΦ Mcap Bmask margin densityWidth
    hRw hdmax hτ hεlow he he' hκ hη hbudget hbΦ hmargin hdensity hdsupply hdm
    ηanchor η₀ Q hQray hQ0 hQt hQ72
  let Cslot:=Classical.choose hsourceResult
  have hCslot:1≤Cslot:=(Classical.choose_spec hsourceResult).1
  have hsource:=(Classical.choose_spec hsourceResult).2
  refine ⟨Cslot,hCslot,?_⟩
  intro N cellWidth Bscale₀ Bmaskcap δ Brestore εwindow hN hcw hBscale hδ hBrestore hεwindow
    B₁ B₂ εpref ell lower radiusMax errv Bmass εmass poolLoss hB₁ hB₂ hεpref hell hlower hmax herrv0 hεmass
    Φ hΦs hΦ hΦone
  intro missingWidth Bmissing hmissingWidth hBmissing
  have hr:=hsource N cellWidth Bscale₀ Bmaskcap δ Brestore εwindow hN hcw hBscale hδ hBrestore hεwindow
    B₁ B₂ εpref ell lower radiusMax errv Bmass εmass poolLoss hB₁ hB₂ hεpref hell hlower hmax herrv0 hεmass
    Φ hΦs hΦ hΦone
  let Cpref:=Classical.choose hr
  have hCpref:0<Cpref:=(Classical.choose_spec hr).1
  have hr₁:=(Classical.choose_spec hr).2
  let J:=Classical.choose hr₁
  have hr₂:=Classical.choose_spec hr₁
  let Spaid:=Classical.choose hr₂
  have hr₃:=Classical.choose_spec hr₂
  let Cpaid:=Classical.choose hr₃
  have hCpaid:0<Cpaid:=(Classical.choose_spec hr₃).1
  have hpaid:=(Classical.choose_spec hr₃).2
  let count:=missingBinCount missingWidth Bmissing
  have hcount:0<(count:ℝ):=by dsimp only [count,missingBinCount]; positivity
  refine ⟨Cpref,hCpref,J,Spaid,(count:ℝ)*Cpaid,mul_pos hcount hCpaid,?_⟩
  filter_upwards [hpaid] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T reflected second s Am₁ Am₂ Dm Km R₀ seed Fm Dparent ξ hK bin hR₀ hanchor
    K modifier left unit Row _ labels key hinj ray₁ ray₂ DataLabel _ column datum first row hfirst hparent hchild hkey hray
    sel L hL Cf hLC hCL Snew Anew d hd hmaskR hmaskcap τ z parentR hrow hsupport hnorm hnonfixed
    p W₁ W₂ θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    corner X₁ X₂ A₁ A₂ omega homega0 weight havoid hcut hmissing0 hmissingcap
    st hQM hQη hcharacter hpuncture hwidth hkeep aLow iBin haLow haLow' hwT hwr hσT hσT' hfreq hheight hActualLow
    D slot value U reserve err rho width Wa x radius annularLoss
    hT hW₁ hW₂ hslots hcoeff hscale hwAll htotal hslower hupper hseed hsourceRadius hC₂ ht
    hmesh0 hmeshSmall hwidth0 hwidthStep hround herrv herr hrho hdelta hloss0 hlossSmall hguard hrad
    hradiusMax hradial hraw hmissingx P poolMesh BD Bsource depth H0 mainRadius
    hpool hH0 hmainRadius hcommon₁ hcommon₂ extra hphase
  let norm:=fun l:labels=>((firstSourceMissing left (key l.val).val.1).absNorm:ℝ)
  have hnorm1 (l:labels):1≤norm l:=CenteredMomentAmplificationChildSourceCaps.norm_ge_one _ (hmissing0 l)
  let index:=fun l:labels=>missingBin missingWidth Z (norm l)
  have hbounds (l:labels):index l<count ∧ 0≤(index l:ℝ)*missingWidth ∧
      Z^((index l:ℝ)*missingWidth)≤norm l ∧ norm l≤Z^(((index l:ℝ)+1)*missingWidth) ∧
      ((index l:ℝ)+1)*missingWidth≤Bmissing+missingWidth ∧
      ((index l:ℝ)+1)*missingWidth≤x l 1+missingWidth:=
    missing_bin_bounds missingWidth Z (norm l) Bmissing (x l 1) hmissingWidth (by linarith only [hZ.1])
      (hnorm1 l) (hmissingcap l) (hmissingx l)
  let energy:=fun l:labels=>
    ‖positiveNewtonCofactorPlain corner (sel l).finalInput (A₁ l) (A₂ l)
      (Selection.puncture (sel l)) (9/4:ℝ) Snew Anew (τ l) t (z l)*
      (∏i:T,normalizedSlot (τ l) (fixedBadMask*idealGenerator (Selection.puncture (sel l))) 1 (z l)
        (s.slots i) (restoredSlotCoeff s i) t (s.P i))‖^2*weight l
  let budget:=Cpaid*(p.control Spaid)^2*(1+|t|+height)^J*
    (Cpref*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4:ℝ) (1/4:ℝ)) bin*
      forcedProfileCost s*(max 1 (forcedProfileCost s))^2)*Cslot^N*
    Z^(-8*(n.allowance:ℝ)+εpref+poolLoss+Bmass*εmass+cellWidth+missingWidth+εmask*(Bmissing+missingWidth)+
      2*εlow*densityWidth*N+εsource+loss+2*δ+Bmaskcap*εmask+εwindow)
  have hbin (k:ℕ)(hk:k<count):
      (∑r:Finset.univ.filter (fun r:labels=>index r=k),energy r.val)≤budget:=by
    let cell:=Finset.univ.filter (fun r:labels=>index r=k)
    let inc:cell→labels:=fun r=>r.val
    have hkrow (r:cell):index (inc r)=k:=(Finset.mem_filter.mp r.property).2
    have hlo (r:cell):Z^((k:ℝ)*missingWidth)≤norm (inc r):=by
      simpa only [hkrow r] using (hbounds (inc r)).2.2.1
    have hhi (r:cell):norm (inc r)≤Z^(((k:ℝ)+1)*missingWidth):=by
      simpa only [hkrow r] using (hbounds (inc r)).2.2.2.1
    have hHcell (r:cell):((k:ℝ)+1)*missingWidth≤x (inc r) 1+missingWidth:=by
      simpa only [hkrow r] using (hbounds (inc r)).2.2.2.2.2
    have hinjcell:Function.Injective (fun r:cell=>key (inc r).val):=by
      intro a b he
      exact Subtype.ext (hinj he)
    have hs:=hZ.2 T reflected second s Am₁ Am₂ Dm Km R₀ seed Fm Dparent ξ hK bin hR₀ hanchor
      cell (fun l:labels=>key l.val) hinjcell ray₁ ray₂
      (fun r=>column (inc r)) datum first (fun r=>row (inc r))
      (fun r=>hfirst (inc r)) (fun r=>hparent (inc r)) (fun r=>hchild (inc r))
      (fun r=>hkey (inc r)) (fun r=>hray (inc r)) (fun r=>sel (inc r))
      L hL (fun r=>hLC (inc r)) (fun r=>hCL (inc r)) Snew Anew hd hmaskR hmaskcap
      (fun r _=>hrow r.val r.property) (fun r _=>hsupport r.val r.property) (fun r _=>hnorm r.val r.property)
      (fun r=>hnonfixed (inc r)) p θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
      corner (fun r=>omega (inc r)) (fun r=>homega0 (inc r)) havoid (fun r=>hcut (inc r))
      ((k:ℝ)*missingWidth) (((k:ℝ)+1)*missingWidth)
      (fun r hr=>hlo ⟨r,hr⟩) (fun r hr=>hhi ⟨r,hr⟩)
      (fun r=>st (inc r)) (fun r=>hQM (inc r)) (fun r=>hQη (inc r))
      (fun r=>hcharacter (inc r)) (fun r=>hpuncture (inc r)) (fun r=>hwidth (inc r)) (fun r=>hkeep (inc r))
      (fun r=>aLow (inc r)) (fun r=>iBin (inc r)) (fun r=>haLow (inc r)) (fun r=>haLow' (inc r))
      hwT hwr hσT hσT' (fun r=>hfreq (inc r)) (fun r=>hheight (inc r)) (fun r=>hActualLow (inc r))
      (fun r=>U (inc r)) (fun r=>reserve (inc r)) (fun r=>err (inc r)) (fun r=>rho (inc r))
      width missingWidth (Bmissing+missingWidth) Wa (fun r=>hT (inc r)) hW₁ hW₂ hslots hcoeff hscale hwAll htotal hslower hupper
      hseed hsourceRadius (fun r=>hC₂ (inc r)) ht hmesh0 hmeshSmall hwidth0 hwidthStep hround herrv
      (fun r=>herr (inc r)) (fun r=>hrho (inc r)) (fun r=>hdelta (inc r)) hloss0 hlossSmall
      (fun r=>hguard (inc r)) (fun r=>hrad (inc r)) (fun r=>hradiusMax (inc r))
      (fun r=>hradial (inc r)) (fun r=>hraw (inc r))
      (missing_bin_upper_le missingWidth Bmissing hmissingWidth hBmissing k hk) (fun r _=>hHcell r)
      P poolMesh BD Bsource depth (fun r=>H0 (inc r)) (fun r=>mainRadius (inc r)) hpool
      (fun r=>hH0 (inc r)) (fun r=>hmainRadius (inc r)) (fun r=>hcommon₁ (inc r))
      (fun r=>hcommon₂ (inc r)) (fun r=>hphase (inc r))
    exact hs
  have hsum:=finite_bin_collection index count energy budget (fun l=>(hbounds l).1) hbin
  simpa (config:={zeta:=false}) only [budget,energy,mul_assoc] using hsum
end
end QRH.Record1252270103Source.Admission.SelectedLowSourceMissingBins
#print axioms QRH.Record1252270103Source.Admission.SelectedLowSourceMissingBins.global_selected_low_positive_family_missing_bins
