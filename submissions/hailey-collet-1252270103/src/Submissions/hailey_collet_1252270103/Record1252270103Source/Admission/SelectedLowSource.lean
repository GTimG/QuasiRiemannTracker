/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual positive row families from one fixed-anchor earlier global source. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.SelectedLowSourceData
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedLowSource
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
theorem global_selected_low_positive_family (Kgraph:ℚ)(n low:Source)(bcell εsource:ℝ)
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
    let τ:=fun l=>(datum (row l).val.1).τ (ray₂ l.val);
    let z:=fun l=>if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val;
    let parentR:=fun l=>((datum (row l).val.1).R*
      (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))*Cf l;
      (∀l∈labels,((Ideal.span {(nonzeroJointSourceRow l).val}).absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((Ideal.span {(nonzeroJointSourceRow l).val}*firstSourceMissing left l.val.1).absNorm:ℝ)≤Z^B) →
      (∀l∈labels,(l.val.1.1.1.absNorm:ℝ)≤Z^B ∧ (l.val.1.1.2.absNorm:ℝ)≤Z^B ∧
        (l.val.2.1.1.absNorm:ℝ)≤Z^B ∧ (l.val.2.1.2.absNorm:ℝ)≤Z^B) →
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
    ∀(lo hi : ℝ),
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
    ∀(U:∀l:labels,Finset (CommonIndex (datum (row l).val.1).C (datum (row l).val.1).D))
      (reserve err rho:labels→ℝ)(width gapH Bmissing:ℝ)(Wa:𝓢(ℝ,ℂ)),
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
    (∀l,value l≠0 → ‖eisEmbedding (nonzeroJointSourceRow l.val).val‖^2≤Z^(radius l)) →
    (∀l,value l≠0 → X₁ l≤Z^Bscale₀ ∧ X₂ l≤Z^Bscale₀) →
    hi≤Bmissing → (∀l,value l≠0 → hi≤x l 1+gapH) →
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
        Z^(-8*(n.allowance:ℝ)+εpref+poolLoss+Bmass*εmass+cellWidth+gapH+εmask*Bmissing+
          2*εlow*densityWidth*N+εsource+loss+2*δ+Bmaskcap*εmask+εwindow) := by
  have hBprev:0≤(low.B:ℝ):=by exact_mod_cast hlow.1.le
  have hhprev:0≤(low.cap:ℝ):=by exact_mod_cast hlow.2.2.2.1
  have hlam:0≤(low.L:ℝ):=by exact_mod_cast (show (0:ℚ)≤low.L by linarith [hlow.2.2.1])
  obtain ⟨meshMax,hm,hglobal⟩:=global_low_paid_positive_family
    (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ) (n.allowance:ℝ) 2 εsource hG hBprev hhprev ha hεsource hlam
  refine ⟨meshMax,hm,?_⟩
  intro mesh hmesh α instα decα rayModulus _ Hray hH Mslot hMslot B loss εmask hB hloss hεmask q
    W hWs hW Rwidth dmax τlow εlow e κ η bΦ Mcap Bmask margin densityWidth
    hRw hdmax hτ hεlow he he' hκ hη hbudget hbΦ hmargin hdensity hdsupply hdm
    ηanchor η₀ Q hQray hQ0 hQt hQ72
  have hdec:decα=Classical.decEq α:=Subsingleton.elim _ _
  cases hdec
  have hbase:=hglobal mesh hmesh α rayModulus Hray hH Mslot hMslot B loss εmask hB hloss hεmask
  have hsourceResult:=hbase q hq0 hq1 W hWs hW Rwidth dmax τlow εlow e κ η bΦ Mcap Bmask margin densityWidth
    hRw hdmax hτ hεlow he he' hκ hη hbudget hbΦ hmargin hdensity hdsupply hdm
    ηanchor η₀ Q hQray hQ0 hQt hQ72
  let Cslot:=Classical.choose hsourceResult
  have hCslot:1≤Cslot:=(Classical.choose_spec hsourceResult).1
  have hsource:=(Classical.choose_spec hsourceResult).2
  refine ⟨Cslot,hCslot,?_⟩
  intro N cellWidth Bscale₀ Bmaskcap δ Brestore εwindow hN hcw hBscale hδ hBrestore hεwindow
    B₁ B₂ εpref ell lower radiusMax errv Bmass εmass poolLoss hB₁ hB₂ hεpref hell hlower hmax herrv0 hεmass
    Φ hΦs hΦ hΦone
  have hprefResult:=uniform_selected_paid_weight N 1 (1/4:ℝ) errv B₁ B₂ εpref ell lower radiusMax
    (by norm_num) (by norm_num) herrv0 hB₁ hB₂ hεpref hell hlower hmax
  let Cpref:=Classical.choose hprefResult
  have hCpref:0<Cpref:=(Classical.choose_spec hprefResult).1
  have hweightUniform:=(Classical.choose_spec hprefResult).2
  have hpaidResult:=hsource N cellWidth Bscale₀ Bmaskcap δ Brestore εwindow
    hN hcw hBscale hδ hBrestore hεwindow Φ hΦs hΦ hΦone
  let J:=Classical.choose hpaidResult
  have hpaidJ:=Classical.choose_spec hpaidResult
  let Spaid:=Classical.choose hpaidJ
  have hpaidS:=Classical.choose_spec hpaidJ
  let Cpaid:=Classical.choose hpaidS
  have hCpaid:0<Cpaid:=(Classical.choose_spec hpaidS).1
  have hpaid:=(Classical.choose_spec hpaidS).2
  refine ⟨Cpref,hCpref,J,Spaid,Cpaid,hCpaid,?_⟩
  filter_upwards [hpaid,hweightUniform] with Z hZsource hZweight
  have hZ:1<Z:=hZweight.1
  refine ⟨hZsource.1,?_⟩
  intro T reflected second s Am₁ Am₂ Dm Km R₀ seed Fm Dparent ξ hK bin hR₀ hanchor
    K modifier left unit labels ray₁ ray₂ DataLabel _ column datum first row hfirst hparent hchild hkey hray
    sel L hL Cf hLC hCL Snew Anew d hd hmaskR hmaskcap τ z parentR hrow hsupport hnorm hnonfixed
    p W₁ W₂ θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    corner X₁ X₂ A₁ A₂ omega homega0 weight havoid hcut lo hi hlo hhi
    st hQM hQη hcharacter hpuncture hwidth hkeep aLow iBin haLow haLow' hwT hwr hσT hσT' hfreq hheight hActualLow
    D slot value U reserve err rho width gapH Bmissing Wa x radius annularLoss
    hT hW₁ hW₂ hslots hcoeff hscale hwAll htotal hslower hupper hseed hsourceRadius hC₂ ht
    hmesh0 hmeshSmall hwidth0 hwidthStep hround herrv herr hrho hdelta hloss0 hlossSmall hguard hrad
    hradiusMax hradial hraw hmissing hHcell P poolMesh BD Bsource depth H0 mainRadius
    hpool hH0 hmainRadius hcommon₁ hcommon₂ extra hphase
  let side:=fun l:labels=>balancedGeometrySide reflected (Real.logb Z (volume s))
    (CoupledFirst.geometryExponents s modifier R₀ seed K Z ξ (column l).1.val)
  have hparentR (l:labels):parentR l=Selection.puncture (sel l):=by
    exact selected_puncture_eq (sel l) _ (hchild l)
  have hgates (l:labels):A₁ l≠0 ∧ A₂ l≠0 ∧ Selection.puncture (sel l)≠0 ∧
      A₁ l*A₂ l∣Selection.puncture (sel l):=actual_frozen_ideal_gates (sel l) hR₀
  have hAR (l:labels):A₁ l*A₂ l∣parentR l:=by rw [hparentR l];exact (hgates l).2.2.2
  have hX (l:labels):0<X₁ l ∧ 0<X₂ l:=by
    have hd₁:0<(d.1.absNorm:ℝ):=zero_lt_one.trans_le (CenteredMomentAmplificationChildSourceCaps.norm_ge_one _ hd.1)
    have hd₂:0<(d.2.absNorm:ℝ):=zero_lt_one.trans_le (CenteredMomentAmplificationChildSourceCaps.norm_ge_one _ hd.2.1)
    dsimp only [X₁,X₂]
    cases corner
    · exact ⟨div_pos (sel l).finalInput.X₁_pos hd₁,div_pos (sel l).finalInput.X₂_pos hd₂⟩
    · exact ⟨div_pos (sel l).finalInput.Y₁_pos hd₁,div_pos (sel l).finalInput.Y₂_pos hd₂⟩
  have hvalue (l:labels):SelectedLowErasure.positiveCorner (sel l) T corner (A₁ l) (A₂ l)
      (9/4:ℝ) Snew Anew (τ l) t (z l)=value l:=by
    have hv:=actual_positive_low_value (sel l) T corner Snew Anew (τ l) t (z l) p
      (fun i=>primePool rayModulus Hray (2:ℝ) (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)
      (fun i=>Z^(w i)) hW₁ hW₂ hslots hcoeff (fun i _=>hscale i)
    apply (selected_positive_corner_eq (sel l) T corner (9/4:ℝ) Snew Anew (τ l) t (z l)).trans
    dsimp only [value,D,slot]
    rw [hparentR l]
    exact hv
  have havoidActual (i:α)(hi:i∈T)(I:Ideal O)(hI:I∈s.pools (Sum.inl i)):IsCoprime I (d.1*d.2):=by
    change I∈s.slots i at hI
    rw [hslots i hi] at hI
    exact havoid i hi I hI
  have hweight0 (l:labels):0≤weight l:=by
    dsimp only [weight,selectedPaidWeight]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (div_nonneg (volume_pos _).le (volume_pos _).le)) (forcedProfileCost_nonneg _)) (homega0 l)
  have hfirstSupport₁:∀v,s.W₁ v≠0→(1/4:ℝ)≤v:=by
    intro v hv
    rw [hW₁] at hv
    exact (p.support 0 hv).1
  have hfirstSupport₂:∀v,s.W₂ v≠0→(1/4:ℝ)≤v:=by
    intro v hv
    rw [hW₂] at hv
    exact (p.support 1 hv).1
  have hz₁:s.W₁ 0=0:=by by_contra hn;have hp:=hfirstSupport₁ 0 hn;norm_num at hp
  have hz₂:s.W₂ 0=0:=by by_contra hn;have hp:=hfirstSupport₂ 0 hn;norm_num at hp
  let factor:=Cpref*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4:ℝ) (1/4:ℝ)) bin*
    forcedProfileCost s*(max 1 (forcedProfileCost s))^2
  have hfactor:0≤factor:=mul_nonneg (mul_nonneg (mul_nonneg hCpref.le
    (geometry_high_factor_pos reflected _ bin (geometrySupportConstant_pos N 1 (1/4:ℝ) (1/4:ℝ)
      (by norm_num) (by norm_num) (by norm_num))).le) (forcedProfileCost_nonneg s)) (sq_nonneg _)
  have hmass (l:labels)(_hn:value l≠0):weight l≤factor*Z^(εpref+poolLoss+Bmass*εmass+x l 0-side l):=by
    have hextra:0≤extra l:=mul_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
      (Nat.cast_nonneg _)) (div_nonneg (hmainRadius l).1 hell.le)
    have hb:=hZweight.2 s modifier R₀ seed Wa Dparent ξ (sourceAReal n low bcell) (reserve l) εmass
      hZ hK hεmass bin reflected second (column l) (datum (row l).val.1).C (datum (row l).val.1).D
      (hC₂ l) (U l) (sel l) (extra l) (omega l) hextra (hphase l) Bmass (err l)
      hN hslower hseed hz₁ hz₂ hsourceRadius hfirstSupport₁ hfirstSupport₂ P poolMesh poolLoss BD Bsource depth
      (H0 l) (mainRadius l) hpool (hH0 l) (hmainRadius l).1 (hmainRadius l).2 rfl (hcommon₁ l) (hcommon₂ l)
    simpa only [factor,weight,Cpref,hprefResult,x,side,K,add_assoc] using hb
  have hchoice (l:labels):∃select:Finset α,select⊆T ∧ (value l≠0→
      (n.allowance:ℝ)≤radius l ∧ RoundedPairAdmission (globalFace (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ)) Z
        (X₁ l) (X₂ l) cellWidth (∑i∈select,w i) (radius l) ∧
      x l 0+x l 1+radius l-side l+q*(∑i∈T\select,w i)≤-8*(n.allowance:ℝ)):=by
    obtain ⟨select,hs,hc⟩:=actual_selected_low_price Kgraph n low bcell hg hn hlow ha.le hq0 hq1
      s Am₁ Am₂ Dm Km R₀ seed Fm K Z ξ hK bin (column l) reflected second (datum (row l).val.1) (U l)
      (sel l) T (hT l) Snew Anew hd w N 2 Dparent (reserve l) width (err l) errv (rho l) mesh
      (9/4:ℝ) cellWidth 0 (n.allowance:ℝ) (by norm_num) hZ hN hupper hscale ht hwAll htotal hmesh0 hwm
      hwidth0 hwidthStep ha (hrho l).1 (hrho l).2 hmeshSmall (herr l) herrv hcw.le hround
      (by linarith only [ha]) (hdelta l) hloss0 hlossSmall (hguard l) (hrad l)
    refine ⟨select,hs,?_⟩
    intro hnval
    have hc':=hc corner (A₁ l) (A₂ l) (hgates l).1 (hgates l).2.1 (hgates l).2.2.2
      havoidActual (τ l) t (z l)
    have hncorner:SelectedLowErasure.positiveCorner (sel l) T corner (A₁ l) (A₂ l)
        (9/4:ℝ) Snew Anew (τ l) t (z l)≠0:=fun hz=>hnval ((hvalue l).symm.trans hz)
    have hgood:=hc'.resolve_left hncorner
    exact ⟨by linarith only [hgood.1,ha],hgood.2.1,by simpa only [add_zero] using hgood.2.2⟩
  choose select hselect hchosen using hchoice
  have hradius (l:labels)(hnval:value l≠0):(n.allowance:ℝ)≤radius l ∧ radius l≤2:=
    ⟨(hchosen l hnval).1,hradiusMax l hnval⟩
  have hadmit (l:labels)(hnval:value l≠0):RoundedPairAdmission (globalFace (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ)) Z
      (X₁ l) (X₂ l) cellWidth (∑i∈select l,w i) (radius l):=(hchosen l hnval).2.1
  have hprice (l:labels)(hnval:value l≠0):x l 0+x l 1+radius l-side l+q*(∑i∈T\select l,w i)≤
      -8*(n.allowance:ℝ):=(hchosen l hnval).2.2
  have hs:=hZsource.2 T reflected second s modifier R₀ seed K ξ hK bin hR₀ hanchor
    labels ray₁ ray₂ column datum first row hfirst hparent hchild hkey hray L hL Cf hLC hCL d hd hmaskR hmaskcap
    hrow hsupport hnorm hnonfixed p θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    weight hweight0 X₁ X₂ hX A₁ A₂ (fun l=>(hgates l).1) (fun l=>(hgates l).2.1) hAR havoid hcut
    lo hi 0 (by norm_num) hlo hhi st hQM hQη hcharacter hpuncture hwidth hkeep aLow iBin
    haLow haLow' hwT hwr hσT hσT' hfreq hheight hActualLow select radius hselect hradius hradial hadmit
    (fun l=>x l 0) (fun l=>x l 1) side factor (εpref+poolLoss+Bmass*εmass) gapH (-8*(n.allowance:ℝ))
    Bmissing hfactor hmissing hraw hmass hHcell hprice
  change (∑l:labels,‖value l‖^2*(weight l*((firstSourceMissing left l.val.val.1).absNorm:ℝ)^(-(0:ℝ))))≤
    Cpaid*(p.control Spaid)^2*(1+|t|+height)^J*factor*Cslot^N*
      Z^(-8*(n.allowance:ℝ)+(εpref+poolLoss+Bmass*εmass)+cellWidth+gapH+εmask*Bmissing+
        2*εlow*densityWidth*N-(0:ℝ)*lo+εsource+loss+2*δ+Bmaskcap*εmask+εwindow) at hs
  have hsum:(∑l:labels,‖positiveNewtonCofactorPlain corner (sel l).finalInput (A₁ l) (A₂ l)
      (Selection.puncture (sel l)) (9/4:ℝ) Snew Anew (τ l) t (z l)*
      (∏i:T,normalizedSlot (τ l) (fixedBadMask*idealGenerator (Selection.puncture (sel l))) 1 (z l)
        (s.slots i) (restoredSlotCoeff s i) t (s.P i))‖^2*weight l)=(∑l:labels,‖value l‖^2*weight l):=by
    apply Finset.sum_congr rfl
    intro l _
    have he:= (selected_positive_corner_eq (sel l) T corner (9/4:ℝ) Snew Anew (τ l) t (z l)).symm.trans (hvalue l)
    exact congrArg (fun v:ℂ=>‖v‖^2*weight l) he
  apply hsum.le.trans
  simpa (config := {zeta := false}) only [neg_zero,Real.rpow_zero,mul_one,zero_mul,sub_zero,add_assoc] using hs

end
end QRH.Record1252270103Source.Admission.SelectedLowSource

#print axioms QRH.Record1252270103Source.Admission.SelectedLowSource.global_selected_low_positive_family
