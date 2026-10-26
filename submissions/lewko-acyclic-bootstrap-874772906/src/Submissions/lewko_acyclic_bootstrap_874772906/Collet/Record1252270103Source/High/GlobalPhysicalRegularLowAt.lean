/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
The genuine LOW source at the single parameter choice used by the joint
collector. Its moving-data contract is kept literal. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularLowParameters
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.GlobalPhysicalRegularCofactor
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.High.GlobalPhysical
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
local instance regularLowAtQuotientFinite (rayModulus:Ideal O)[NeZero rayModulus]:Finite (O⧸rayModulus):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)

open SelectedHighCofactorFamily High.GlobalPhysical SelectedLowPaid SelectedLowDictionary
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open Record12518109Natural Record1252270103Finite Record1252270103StepScalar
open QRH.Record1252270103Graph PhysicalLowReserve High
open OAI.SevenEighths.Record1252270103Source.Collision

open SelectedRegularSourceData SelectedSecondKeyCaps
local instance regularLowAtDecEq {ι:Type*}:DecidableEq ι:=Classical.decEq _

open CenteredMomentSecondInputCapacitySource PhysicalAnalytic

def RegularLowAt {α:Type}[Fintype α]
    (rayModulus:Ideal O)[NeZero rayModulus](Hray:Subgroup (O⧸rayModulus)ˣ)
    (hH:RayOrthogonality.globalUnits rayModulus≤Hray)
    (n low:Source)(bcell θloss mesh εslot τsource:ℝ)(N:ℕ)
    (Mslot:α→ℝ)(W:ℝ→ℂ)(ηanchor η₀:Character)(Q:Ideal O)(hQray:Q≤rayModulus)
    (Cslot Cpref:ℝ)(JL:ℕ)(SL:Finset (ℕ×ℕ))(CL Z:ℝ):Prop:=
    let q:ℝ:=(n.q:ℝ)
    let e:=highBuffer 1 1 εslot (θloss/16)
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
      (((geometryRawFixedMask s R₀*L)*(d.1*d.2)).absNorm:ℝ)≤Z^(10:ℝ) →
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
      (∀l,(9/4:ℝ)^2*X₁ l*X₂ l≤Z^(2:ℝ)) →
      (∀l:labels,((firstSourceMissing left (key l.val).val.1).absNorm:ℝ)≤Z^(6:ℝ)) →
    ∀states : rows→NaturalState Z 20 2,
    ∀(hfixed:∀u,(states u).fixedModulus=internalQ Q η₀)(keep:∀u,(states u).radial.keep (G.z u))
      (selector:rows→BufferIndex e),
      (∀u,(states u).character=G.τ u ∧
        (states u).puncture=Selection.puncture (G.sel u)*(d.1*d.2) ∧
        (states u).width≤40 ∧
        (states u).radial.profile (‖eisEmbedding (G.z u)‖^2/(states u).radial.scale)≠0 ∧
        RetainedZeroBin rayModulus Hray hH (states u) η₀ ((hfixed u).trans_le (inf_le_left.trans hQray))
          ((hfixed u).trans_le inf_le_right) (G.z u) (keep u) e (Z^τsource) (selector u) ∧
        KeyCaps (G.key u) Z 6
          (Real.logb Z ((firstSourceMissing left (G.key u).val.1).absNorm:ℝ))) →
    let st:=fun l:labels=>states (inc l);
    let select:=fun l:labels=>selector (inc l);
      (∀i∈T,0≤w i) → (∀i∈T,w i/100≤1) →
      (∀i∈T,(33/50:ℝ)≤σ i) → (∀i∈T,σ i≤(33/50:ℝ)) →
      (∀i∈T,|t+freq i|≤Z^τsource) →
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
        (sourceAReal n low bcell) ξ (reserve l) (err l)) θloss
    let radius:=fun l:labels=>sourceFReal n low bcell-max
      (labelD reflected (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)) Z-
        labelC reflected (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)) Z) 0-rho l
    let annularLoss:=3*(N:ℝ)*Real.logb Z 2+2*Real.logb Z (max 1 (9/4:ℝ))+2*θloss
    (∀l,T⊆(sel l).full) →
    s.W₁=(p.profile 0:ℝ→ℂ) → s.W₂=(p.profile 1:ℝ→ℂ) →
    (∀i∈T,s.slots i=primePool rayModulus Hray (2:ℝ) (Z^(w i))) →
    (∀i∈T,restoredSlotCoeff s i=(fun I=>idealCoeff (relativeCharacter rayModulus Hray hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (freq i) I)) →
    (∀i,s.P i=Z^(w i)) → (∀i,0≤w i) → (∑i,w i)≤bcell →
    1≤s.lower → s.upper≤2 →
    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^(6:ℝ) →
    length Z s.X₁+length Z s.X₂≤plainBudget n bcell width →
    0≤mesh → mesh≤(n.allowance:ℝ)/4 →
    0≤width → width≤PhysicalLowGuard.step n → θloss≤(n.allowance:ℝ)/4 →
    θloss≤(n.allowance:ℝ)/4 →
    (∀l,err l≤(n.allowance:ℝ)/4) →
    (∀l,0≤rho l ∧ rho l≤(n.allowance:ℝ)/4) →
    (∀l,max (labelD reflected (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)) Z-
      labelC reflected (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)) Z) 0≤
        labelC reflected (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)) Z) →
    0≤annularLoss → annularLoss≤(n.allowance:ℝ)/4 →
    (∀l,annularLoss+(low.B:ℝ)*rho l+2*(n.allowance:ℝ)≤
      (low.B:ℝ)*sourceFReal n low bcell-plainBudget n bcell width-bcell) →
    (∀l,radius l≤x l 2+θloss) →
    (∀l,value l≠0 → radius l≤2) →
    (∀l,value l≠0 → ‖eisEmbedding (nonzeroJointSourceRow (key l.val)).val‖^2≤Z^(radius l)) →
    (∀l,value l≠0 → X₁ l≤Z^(1:ℝ) ∧ X₂ l≤Z^(1:ℝ)) →
        ∀(P:Finset (Ideal O))(poolMesh BD Bsource:ℝ)(depth:ℕ)(H0 mainRadius:labels→ℝ),
      Pool.FixedCellPoolData P Z (sourceAReal n low bcell) (sourceAReal n low bcell/2) poolMesh θloss BD Bsource depth →
      (∀l,0<H0 l) →
      (∀l,0≤mainRadius l+6*sourceAReal n low bcell ∧ mainRadius l+6*sourceAReal n low bcell≤32) →
      (∀l,((if reflected then (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)).1.2
        else (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)).1.1).absNorm:ℝ)≤Z^(2:ℝ)) →
      (∀l,((if second then (datum (row l).val.1).D else (datum (row l).val.1).C).absNorm:ℝ)≤Z^(2:ℝ)) →
    let extra:=fun l:labels=>((CenteredMomentFirstAnnularMajorant.bands (H0 l)).card:ℝ)*
      ((actualAllocations s.pools (if reflected then (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)).1.2
        else (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)).1.1)).card:ℝ)^2/(P.card:ℝ)*
        ((mainRadius l+6*sourceAReal n low bcell)/(sourceAReal n low bcell/2));
    (∀l,omega l≤
      (‖CoupledFirst.balancedColumnScalar reflected s modifier R₀ seed K Z ξ Dparent
        (Real.logb Z (volume s)) hK bin
        (fun q=>normPhase (CoupledFirst.coordinateBlock s modifier R₀ seed Wa K Z ξ q)) (column l)‖^2*
        extra l*‖frozenCoefficient (sel l).B₁.val
          (if reflected then (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)).1.2
            else (firstLabel s modifier R₀ seed K Z ξ hK bin (column l)).1.1) R₀ s.ν s.W s.P‖^2/volume s)*
        (firstMainRadius reflected K (volume s) Z ξ (3*sourceAReal n low bcell) (reserve l)
          (firstLabel s modifier R₀ seed K Z ξ hK bin (column l))/(lowerFactor N 1 (1/4)))*
        normalizer (datum (row l).val.1).C (datum (row l).val.1).D (U l)) →
    (∑l∈Finset.univ.filter (fun l:labels=>bufferValue e (select l)<(q+1)/2),‖positiveNewtonCofactorPlain corner (sel l).finalInput (A₁ l) (A₂ l)
      (Selection.puncture (sel l)) (9/4:ℝ) Snew Anew (τ l) t (z l)*
      (∏i:T,normalizedSlot (τ l) (fixedBadMask*idealGenerator (Selection.puncture (sel l))) 1 (z l)
        (s.slots i) (restoredSlotCoeff s i) t (s.P i))‖^2*weight l)≤
      CL*(p.control SL)^2*(1+|t|+height)^JL*
        (Cpref*geometryHighFactor reflected (geometrySupportConstant N 1 (1/4:ℝ) (1/4:ℝ)) bin*
          forcedProfileCost s*(max 1 (forcedProfileCost s))^2)*Cslot^N*
        Z^(-8*(n.allowance:ℝ)+θloss+θloss+6*(θloss/100)+θloss+θloss+(θloss/100)*(6+θloss)+
          2*εslot*100*N+θloss+θloss+2*θloss+10*(θloss/100)+θloss)


theorem regular_low_controls (Kgraph:ℚ)(n low:Source)(bcell θloss:ℝ)
    (hg:RealGeometry Kgraph n low bcell)(hn:ParentGood n)(hlow:ParentGood low)
    (ha:0<(n.allowance:ℝ))(hqhalf:(1/2:ℝ)≤(n.q:ℝ))(hq1:(n.q:ℝ)≤1)
    (hG:GlobalSource (low.B:ℝ) (low.L:ℝ) (low.cap:ℝ))(hθ:0<θloss)
    {α:Type}[Fintype α](rayModulus:Ideal O)[NeZero rayModulus](Hray:Subgroup (O⧸rayModulus)ˣ)
    (hH:RayOrthogonality.globalUnits rayModulus≤Hray)
    (W:ℝ→ℂ)(hWs:Function.support W⊆Icc (1:ℝ) 2)(hW:ContDiff ℝ ∞ W)
    (Mslot:α→ℝ)(hMslot:∀i,0≤Mslot i)(mesh:ℝ)
    (hmesh:mesh≤regularLowMesh Kgraph n low bcell θloss hg hn hlow ha hqhalf hq1 hG hθ)
    (N:ℕ)(wmin rmin εslot τsource:ℝ)(hc:CardinalityBudget θloss 100 100 1 1 N wmin rmin εslot)
    (hN:Fintype.card α≤N)(hτ:0<τsource)(hτheight:2*τsource<100*(εslot/4))
    (ηanchor η₀:Character)(Q:Ideal O)(hQray:Q≤rayModulus)
    (hQ:internalQ Q η₀≠0)(hQt:internalQ Q η₀≠⊤)(hQ72:internalQ Q η₀≤Ideal.span {(72:O)})
    (Φ:𝓢(ℝ,ℂ))(hΦs:Function.support (Φ:ℝ→ℂ)⊆Iic (2:ℝ))
    (hΦ:∀x,0≤(Φ x).re)(hΦone:∀x∈Icc (0:ℝ) 1,1≤(Φ x).re):
    ∃Cslot Cpref:ℝ,∃JL:ℕ,∃SL:Finset (ℕ×ℕ),∃CL:ℝ,
      1≤Cslot ∧ 0<Cpref ∧ 0<CL ∧ ∀ᶠZ:ℝ in atTop,2≤Z ∧
      RegularLowAt rayModulus Hray hH n low bcell θloss mesh εslot τsource N Mslot W ηanchor η₀ Q hQray
        Cslot Cpref JL SL CL Z:=by
  obtain ⟨Cslot,hCslot,hslots⟩:=regular_low_slot_supply Kgraph n low bcell θloss hg hn hlow ha hqhalf hq1 hG hθ
    rayModulus Hray hH W hWs hW Mslot hMslot mesh hmesh N wmin rmin εslot τsource hc hτ hτheight
    ηanchor η₀ Q hQray hQ hQt hQ72
  have hp:=hslots N θloss 1 10 θloss 2 θloss hN hθ (by norm_num) hθ (by norm_num) hθ
    2 2 θloss (sourceAReal n low bcell/2) (lowerFactor N 1 (1/4)) 32 θloss 6 (θloss/100) θloss
    (by norm_num) (by norm_num) hθ (div_pos hg.a_pos (by norm_num))
    (lowerFactor_pos N 1 (1/4) (by norm_num) (by norm_num)) (by norm_num) hθ
    (div_nonneg hθ.le (by norm_num)) Φ hΦs hΦ hΦone θloss 6 hθ (by norm_num)
  obtain ⟨Cpref,hCpref,JL,SL,CL,hCL,hpaid⟩:=hp
  refine ⟨Cslot,Cpref,JL,SL,CL,hCslot,hCpref,hCL,?_⟩
  unfold RegularLowAt
  exact hpaid
end
end QRH.Record1252270103Source.High.GlobalPhysical
#print axioms QRH.Record1252270103Source.High.GlobalPhysical.regular_low_controls
