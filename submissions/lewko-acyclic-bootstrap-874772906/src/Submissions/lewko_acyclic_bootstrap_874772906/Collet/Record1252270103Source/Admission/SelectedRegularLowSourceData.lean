/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual positive row families from one fixed-anchor earlier global source. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedLowBufferedSource
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Admission.SelectedRegularSourceDataState
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.Admission.SelectedRegularLowSource
noncomputable section
open OAI OAI.SevenEighths Cycle61InitialMass LocalMoment
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
local instance selectedRegularLowQuotientFinite (rayModulus:Ideal O)[NeZero rayModulus]:Finite (O⧸rayModulus):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)

open SelectedHighCofactorFamily High.GlobalPhysical SelectedLowPaid SelectedLowDictionary
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open Record12518109Natural Record1252270103Finite Record1252270103StepScalar
open QRH.Record1252270103Graph PhysicalLowReserve High
open OAI.SevenEighths.Record1252270103Source.Collision

open SelectedRegularSourceData SelectedSecondKeyCaps

theorem sum_univ_subtype_filter {ι:Type}[Fintype ι](p:ι→Prop)[DecidablePred p](f:ι→ℝ):
    (∑l∈Finset.univ.filter (fun l:(Finset.univ:Finset ι)=>p l.val),f l.val)=
    ∑l∈Finset.univ.filter p,f l:=by
  apply Finset.sum_bij (fun l _=>l.val)
  · intro l hl
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hl
  · intro a ha b hb he
    exact Subtype.ext he
  · intro b hb
    exact ⟨⟨b,Finset.mem_univ b⟩,by simpa using hb,rfl⟩
  · intro l hl
    rfl

/-- The missing coordinate is unaffected by allocation, forced, or lost-width changes. -/
theorem selected_missing_coordinate {α Label Row:Type}[Fintype α][Fintype Label]
    {Z:ℝ}{a:Anchor α Z}{F:Family a Label}{rows:Finset Row}{second:Bool}
    (G:Selected F Row rows second)(err errv annular:ℝ)(w:α→ℝ)(wmin:ℝ)(T:Finset α)(u:rows):
    G.x err errv annular w wmin T u 1=
      Real.logb Z ((firstSourceMissing (!F.reflected) (G.key u).val.1).absNorm:ℝ):=by
  cases second <;> simp [Selected.x,Selection.coordinate,SelectedHighCofactorCoordinates.cofactorCoordinates,
    HighScalar.lostWidthCoordinates,childHighCoordinates,actualHighCoordinates,Selected.key,FirstFamily.rawKey,
    Family.first] <;> rfl

theorem selected_nonfixed {α Label Row:Type}[Fintype α][Fintype Label]
    {Z:ℝ}{a:Anchor α Z}{F:Family a Label}{rows:Finset Row}{second:Bool}
    (G:Selected F Row rows second)(hm:F.m≠0)(hml:ConcretePrimeRowBridge.goodLambda∣F.m)
    (hm2:(2:O)∣F.m)(hQ:F.Q≤Ideal.span {(72:O)})(u:rows):
    ¬FixedInducingRow (G.τ u) F.Q fixedBadMask 1 (G.z u):=by
  have hk:=SelectedSecondNatural.actual_row_nonexceptional F.slots F.input F.childModifier F.mask F.childSeed
    F.Hmain F.Tsec Z F.ξ CenteredMomentFirstAmplificationChoice.ballProfile F.childSeed_sf (fun _=>F.zero₁) (fun _=>F.zero₂)
    F.Hmain_pos F.χ₀ F.Q F.m (G.row u) (G.ψ u) second hQ hml hm2
  exact (((G.datum u).family.nonexceptional_iff (G.ψ u) F.Q F.m (G.z u) hm hml hm2).mp hk).2

section Pointwise
local instance regularLowPointwiseDecEq {ι:Type*}:DecidableEq ι:=Classical.decEq _
variable {Z:ℝ}
variable {α:Type}[Fintype α]
variable {rayModulus:Ideal O}[NeZero rayModulus]
variable {Hray:Subgroup (O⧸rayModulus)ˣ}{hH:RayOrthogonality.globalUnits rayModulus≤Hray}
variable {n low:Source}{bcell εsource mesh B loss εmask q:ℝ}{Mslot:α→ℝ}{W:ℝ→ℂ}
variable {Rwidth τlow εlow e η bΦ Mcap Bmask densityWidth:ℝ}
variable {ηanchor η₀:Character}{Q:Ideal O}{hQray:Q≤rayModulus}{hQ72:internalQ Q η₀≤Ideal.span {(72:O)}}
variable {N:ℕ}{cellWidth Bscale₀ Bmaskcap δ Brestore εwindow B₁ B₂ εpref ell lower radiusMax errv Bmass εmass poolLoss:ℝ}
variable {missingWidth Bmissing Cslot Cpref Cpaid:ℝ}{J:ℕ}{Spaid:Finset (ℕ×ℕ)}

include hQ72 in
theorem apply_actual_family (hcall:
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
      (∀l,(st l).width≤Mcap) → ∀hkeep : ∀l,(st l).radial.keep (z l),
    ∀select : labels→BufferIndex e,
      (∀l,RetainedZeroBin rayModulus Hray hH (st l) η₀ (hQM l) (hQη l) (z l) (hkeep l) e (Z^τlow) (select l)) →
      (∀l,(st l).radial.profile (‖eisEmbedding (z l)‖^2/(st l).radial.scale)≠0) →
      (∀i∈T,0≤w i) → (∀i∈T,w i/densityWidth≤Rwidth) →
      (∀i∈T,(33/50:ℝ)≤σ i) → (∀i∈T,σ i≤(33/50:ℝ)) →
      (∀i∈T,|t+freq i|≤Z^τlow) →
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
    (∑l∈Finset.univ.filter (fun l:labels=>bufferValue e (select l)<(q+1)/2),‖positiveNewtonCofactorPlain corner (sel l).finalInput (A₁ l) (A₂ l)
      (Selection.puncture (sel l)) (9/4:ℝ) Snew Anew (τ l) t (z l)*
      (∏i:T,normalizedSlot (τ l) (fixedBadMask*idealGenerator (Selection.puncture (sel l))) 1 (z l)
        (s.slots i) (restoredSlotCoeff s i) t (s.P i))‖^2*weight l)≤
      Cpaid*(p.control Spaid)^2*(1+|t|+height)^J*
        (Cpref*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4:ℝ) (1/4:ℝ)) bin*
          forcedProfileCost s*(max 1 (forcedProfileCost s))^2)*Cslot^N*
        Z^(-8*(n.allowance:ℝ)+εpref+poolLoss+Bmass*εmass+cellWidth+missingWidth+εmask*(Bmissing+missingWidth)+
          2*εlow*densityWidth*N+εsource+loss+2*δ+Bmaskcap*εmask+εwindow)) :
    ∀T : Finset α,
    ∀(reflected second : Bool)(s : Input α)(Am₁ Am₂ Dm Km R₀ seed:Ideal O)(Fm:Ideal O→ℂ)
      (Dparent ξ : ℝ)(hK : 0<Z^Dparent)(bin : ℤ×(Fin 5→ℤ))(hR₀:R₀≠0)(hseed:Squarefree seed)(hZanchor:1<Z),
      s.η=ηanchor →
    let K:=Z^Dparent;
    let modifier:=markedSourceModifier Am₁ Am₂ Dm Km Fm;
    let left:=!reflected;
    let unit:=fun l=>(Record12518109Raw.fixedParentUnit left s.η l:O);
    ∀(reserveGeom:ℝ)(manchor:O)(hm:manchor≠0)(hml:ConcretePrimeRowBridge.goodLambda∣manchor)(hm2:(2:O)∣manchor)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0),
    let anchor : Anchor α Z := {
      s := s
      modifier := modifier
      R := R₀
      seed := seed
      R_ne := hR₀
      seed_sf := hseed
      zero₁ := hz₁
      zero₂ := hz₂
      D := Dparent
      ξ := ξ
      reserve := reserveGeom
      hZ := hZanchor
      hK := hK
      bin := bin
      reflected := reflected
      Q := internalQ Q η₀
      m := manchor };
    ∀{Label:Type}[Fintype Label](F:Family anchor Label),
    ∀{Row:Type}(rows:Finset Row)(G:Selected F Row rows second),
      Function.Injective G.key →
    let labels:Finset rows:=Finset.univ;
    let inc : labels → rows := fun l=>l.val;
    let key:=G.key;
    let column:=fun l:labels=>G.column (inc l);
    let datum:=F.datum;
    let first:=F.first;
    let row:=fun l:labels=>G.row (inc l);
    let sel:=fun l:labels=>G.sel (inc l);
    let L:=G.L;
    let Cf:=fun l:labels=>(sel l).Cf;
    ∀(Snew Anew:Finset (Ideal O)),
    let d:=newtonDivisorPair Snew Anew;
      GoodPair d →
      ((geometryRawFixedMask s R₀*L)*(d.1*d.2))≠0 →
      (((geometryRawFixedMask s R₀*L)*(d.1*d.2)).absNorm:ℝ)≤Z^Bmaskcap →
    let τ:=fun l:labels=>G.τ (inc l);
    let z:=fun l=>if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val;
    let parentR:=fun l=>((datum (row l).val.1).R*
      (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))*Cf l;
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
      (∀l:labels,((firstSourceMissing left (key l.val).val.1).absNorm:ℝ)≤Z^Bmissing) →
    ∀states : rows→NaturalState Z Bmask bΦ,
    ∀(hfixed:∀u,(states u).fixedModulus=internalQ Q η₀)(keep:∀u,(states u).radial.keep (G.z u))
      (selector:rows→BufferIndex e),
      (∀u,(states u).character=G.τ u ∧
        (states u).puncture=Selection.puncture (G.sel u)*(d.1*d.2) ∧
        (states u).width≤Mcap ∧
        (states u).radial.profile (‖eisEmbedding (G.z u)‖^2/(states u).radial.scale)≠0 ∧
        RetainedZeroBin rayModulus Hray hH (states u) η₀ ((hfixed u).trans_le (inf_le_left.trans hQray))
          ((hfixed u).trans_le inf_le_right) (G.z u) (keep u) e (Z^τlow) (selector u) ∧
        KeyCaps (G.key u) Z B
          (Real.logb Z ((firstSourceMissing left (G.key u).val.1).absNorm:ℝ))) →
    let st:=fun l:labels=>states (inc l);
    let select:=fun l:labels=>selector (inc l);
      (∀i∈T,0≤w i) → (∀i∈T,w i/densityWidth≤Rwidth) →
      (∀i∈T,(33/50:ℝ)≤σ i) → (∀i∈T,σ i≤(33/50:ℝ)) →
      (∀i∈T,|t+freq i|≤Z^τlow) →
    let D:=fun l : labels=>RetainedLow.positiveFrozenRow
      (rowWeight (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l) t) W₁ W₂
      (A₁ l*d.1) (A₂ l*d.2) (9/4:ℝ) (X₁ l) (X₂ l) (X₁ l*X₂ l)
    let slot:=fun (l : labels) i=>normalizedSlot (τ l) (fixedBadMask*idealGenerator (parentR l)) 1 (z l)
      (primePool rayModulus Hray (2:ℝ) (Z^(w i)))
      (fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I) t (Z^(w i))
    let value:=fun l : labels=>D l*∏i:T,slot l i
    let U:=fun l:labels=>(G.datum (inc l)).inactive;
    let reserve:=fun _:labels=>F.reserve;
    ∀(err rho:labels→ℝ)(width:ℝ)(Wa:𝓢(ℝ,ℂ)),
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
    1≤s.lower → s.upper≤2 →
    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass →
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
    (∑l∈Finset.univ.filter (fun l:labels=>bufferValue e (select l)<(q+1)/2),‖positiveNewtonCofactorPlain corner (sel l).finalInput (A₁ l) (A₂ l)
      (Selection.puncture (sel l)) (9/4:ℝ) Snew Anew (τ l) t (z l)*
      (∏i:T,normalizedSlot (τ l) (fixedBadMask*idealGenerator (Selection.puncture (sel l))) 1 (z l)
        (s.slots i) (restoredSlotCoeff s i) t (s.P i))‖^2*weight l)≤
      Cpaid*(p.control Spaid)^2*(1+|t|+height)^J*
        (Cpref*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4:ℝ) (1/4:ℝ)) bin*
          forcedProfileCost s*(max 1 (forcedProfileCost s))^2)*Cslot^N*
        Z^(-8*(n.allowance:ℝ)+εpref+poolLoss+Bmass*εmass+cellWidth+missingWidth+εmask*(Bmissing+missingWidth)+
          2*εlow*densityWidth*N+εsource+loss+2*δ+Bmaskcap*εmask+εwindow) := by
  intro T reflected second s Am₁ Am₂ Dm Km R₀ seed Fm Dparent ξ hK bin hR₀ hseed hZanchor hanchor
    K modifier left unit reserveGeom manchor hm hml hm2 hz₁ hz₂ anchor Label _ F Row rows G hinj
    labels inc key column datum first row sel L Cf Snew Anew d hd hmaskR hmaskcap τ z parentR
    p W₁ W₂ θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    corner X₁ X₂ A₁ A₂ omega homega0 weight havoid hcut hmissingcap
    states hfixed keep selector hdata st select hwT hwr hσT hσT' hfreqActual
    D slot value U reserve err rho width Wa x radius annularLoss
    hT hW₁ hW₂ hslots hcoeff hscale hwAll htotal hslower hupper hsourceRadius ht
    hmesh0 hmeshSmall hwidth0 hwidthStep hround herrv herr hrho hdelta hloss0 hlossSmall hguard hrad
    hradiusMax hradial hraw P poolMesh BD Bsource depth H0 mainRadius
    hpool hH0 hmainRadius hcommon₁ hcommon₂ extra hphase
  let rays₁:=fun u:rows=>dictionaryRay reflected s modifier R₀ seed K Z ξ hK bin (G.column u)
  let ray₁:=Function.extend G.key rays₁ (fun _=>1)
  let ray₂:=Function.extend G.key G.ψ (fun _=>1)
  have hray₁ (l:labels):ray₁ (key l.val)=rays₁ (inc l):=
    hinj.extend_apply rays₁ (fun _=>1) (inc l)
  have hray₂ (l:labels):ray₂ (key l.val)=G.ψ (inc l):=
    hinj.extend_apply G.ψ (fun _=>1) (inc l)
  have hτ (l:labels):(datum (row l).val.1).τ (ray₂ (key l.val))=τ l:=by
    rw [hray₂ l]
    rfl
  have hparentR (l:labels):parentR l=Selection.puncture (sel l):=by
    change (((F.R*FirstFamily.columnIdeal reflected s modifier R₀ seed K Z ξ hK bin (column l))*
      (if second then (datum (row l).val.1).D else (datum (row l).val.1).C))*Cf l)=_
    rfl
  have hc (l:labels):KeyCaps (key l.val) Z B (x l 1):=by
    have hp:=(hdata (inc l)).2.2.2.2.2
    have hx:x l 1=Real.logb Z ((firstSourceMissing left (key l.val).val.1).absNorm:ℝ):=by
      dsimp only [x,childHighCoordinates,actualHighCoordinates]
      simp only [Matrix.cons_val_one,Matrix.cons_val_zero,Fin.isValue,
        show (1:Fin 4)≠0 by decide,ite_false,add_zero]
      cases second <;> rfl
    rw [hx]
    exact hp
  have hnorm (l:rows)(_hl:l∈labels):
      ((key l).val.1.1.1.absNorm:ℝ)≤Z^B ∧ ((key l).val.1.1.2.absNorm:ℝ)≤Z^B ∧
      ((key l).val.2.1.1.absNorm:ℝ)≤Z^B ∧ ((key l).val.2.1.2.absNorm:ℝ)≤Z^B:=
    (hdata l).2.2.2.2.2.1
  have hmissingx (l:labels):
      ((firstSourceMissing left (key l.val).val.1).absNorm:ℝ)≤Z^(x l 1):=(hc l).2.2.2.2.le
  have hs:=hcall T reflected second s Am₁ Am₂ Dm Km R₀ seed Fm Dparent ξ hK bin hR₀ hanchor
    labels key (fun a b h=>Subtype.ext (hinj h)) ray₁ ray₂ column datum F.first row

  have hs₁:=hs (fun _=>rfl) (fun l=>(G.structural (inc l)).1) (fun l=>(G.structural (inc l)).2.2.1)
    (fun _=>rfl) (fun l=>(hray₁ l).symm) sel L G.L_ne
    (fun l=>G.forced_lower (inc l)) (fun l=>G.forced_upper (inc l)) Snew Anew hd hmaskR hmaskcap
  have hs₂:=hs₁ (fun l _=>(hdata l).2.2.2.2.2.2.1) (fun l _=>(hdata l).2.2.2.2.2.2.2.1) hnorm
    (fun l hn=>selected_nonfixed G hm hml hm2 hQ72 (inc l)
      ((congrArg (fun χ=>FixedInducingRow χ (internalQ Q η₀) fixedBadMask 1 (z l)) (hτ l)).mp hn))
    p θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot corner omega homega0 havoid hcut
  have hs₃:=hs₂ (fun l=>(hc l).2.2.2.1) hmissingcap
    (fun l=>states (inc l)) (fun l=>(hfixed (inc l)).trans_le (inf_le_left.trans hQray))
    (fun l=>(hfixed (inc l)).trans_le inf_le_right)
    (fun l=>(hdata (inc l)).1.trans (hτ l).symm)
    (fun l=>(hdata (inc l)).2.1.trans (congrArg (fun I=>I*(d.1*d.2)) (hparentR l)).symm)
    (fun l=>(hdata (inc l)).2.2.1) (fun l=>keep (inc l)) select
    (fun l=>(hdata (inc l)).2.2.2.2.1) (fun l=>(hdata (inc l)).2.2.2.1)
    hwT hwr hσT hσT' hfreqActual U reserve err rho width Wa
  simp only [hτ] at hs₃
  have hs₄:=hs₃ hT hW₁ hW₂ hslots hcoeff hscale hwAll htotal hslower hupper hseed hsourceRadius (fun l=>(G.datum (inc l)).hC) ht
    hmesh0 hmeshSmall hwidth0 hwidthStep hround herrv herr hrho hdelta hloss0 hlossSmall hguard hrad
    hradiusMax hradial hraw hmissingx P poolMesh BD Bsource depth H0 mainRadius
    hpool hH0 hmainRadius hcommon₁ hcommon₂ hphase
  exact hs₄
end Pointwise

end
end QRH.Record1252270103Source.Admission.SelectedRegularLowSource
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowSource.sum_univ_subtype_filter
#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowSource.selected_missing_coordinate

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowSource.selected_nonfixed

#print axioms QRH.Record1252270103Source.Admission.SelectedRegularLowSource.apply_actual_family
