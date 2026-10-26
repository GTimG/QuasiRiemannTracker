/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual positive row families from one fixed-anchor earlier global source. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Admission.RetainedLowPaidCells
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
local instance lowPaidQuotientFinite (rayModulus:Ideal O)[NeZero rayModulus]:Finite (O⧸rayModulus):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)

theorem global_low_paid_positive_family (Bprev lam hprev Mmin Mmax εsource:ℝ)
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
    ∃Cslot:ℝ,1≤Cslot ∧
    ∀(N:ℕ)(cellWidth Bscale₀ Bmaskcap δ Brestore εwindow:ℝ),Fintype.card α≤N →
      0<cellWidth → 0≤Bscale₀ → 0<δ → 0≤Brestore → 0<εwindow →
    ∀Φ : 𝓢(ℝ,ℂ),Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ → (∀x,0≤(Φ x).re) →
      (∀x∈Set.Icc (0:ℝ) 1,1≤(Φ x).re) →
    ∃J:ℕ,∃Spaid:Finset (ℕ×ℕ),∃Cpaid:ℝ,0<Cpaid ∧
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
      ((geometryRawFixedMask s R₀*L)*(d.1*d.2))≠0 →
      (((geometryRawFixedMask s R₀*L)*(d.1*d.2)).absNorm:ℝ)≤Z^Bmaskcap →
    let τ:=fun l=>(datum (row l).val.1).τ (ray₂ l.val)
    let z:=fun l=>if second then -(row l).val.2.2.2.val else (row l).val.2.2.2.val
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
    ∀weight : labels→ℝ,(∀l,0≤weight l) →
    ∀(X₁ X₂ : labels→ℝ),
      (∀l,0<X₁ l ∧ 0<X₂ l) →
    ∀(A₁ A₂ : labels→Ideal O),
      (∀l,A₁ l≠0) → (∀l,A₂ l≠0) → (∀l,A₁ l*A₂ l∣parentR l) →
      (∀i∈T,∀I∈primePool rayModulus Hray (2:ℝ) (Z^(w i)),IsCoprime I (d.1*d.2)) →
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
    ∀(select : labels→Finset α)(radius : labels→ℝ),
      (∀l,select l⊆T) →
      (∀l,value l≠0 → Mmin≤radius l ∧ radius l≤Mmax) →
      (∀l,value l≠0 → ‖eisEmbedding (nonzeroJointSourceRow l.val).val‖^2≤Z^(radius l)) →
      (∀l,value l≠0 → RoundedPairAdmission (globalFace Bprev lam hprev) Z
        (X₁ l) (X₂ l) cellWidth (∑i∈select l,w i) (radius l)) →
    ∀(x₀ x₁ side : labels→ℝ)(factor massLoss gapH target Bmissing : ℝ),0≤factor → hi≤Bmissing →
      (∀l,value l≠0 → X₁ l≤Z^Bscale₀ ∧ X₂ l≤Z^Bscale₀) →
      (∀l,value l≠0 → weight l≤factor*Z^(massLoss+x₀ l-side l)) →
      (∀l,value l≠0 → hi≤x₁ l+gapH) →
      (∀l,value l≠0 → x₀ l+x₁ l+radius l-side l+q*∑j∈T\select l,w j≤target) →
    (∑l : labels,‖value l‖^2*(weight l*((firstSourceMissing left l.val.val.1).absNorm:ℝ)^(-γ)))≤
      Cpaid*(p.control Spaid)^2*(1+|t|+height)^J*factor*Cslot^N*
        Z^(target+massLoss+cellWidth+gapH+εmask*Bmissing+2*εlow*densityWidth*N-γ*lo+
          εsource+loss+2*δ+Bmaskcap*εmask+εwindow) := by
  obtain ⟨meshMax,hm,hglobal⟩:=global_low_erased_collected_cells
    Bprev lam hprev Mmin Mmax εsource hG hBprev hhprev hMmin hεsource hlam
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
  refine ⟨Cslot,hCslot,?_⟩
  intro N cellWidth Bscale₀ Bmaskcap δ Brestore εwindow hN hcw hscale hδ hBrestore hεwindow
    Φ hΦs hΦ hΦone
  obtain ⟨J,Spaid,Cpaid,hCpaid,hpaid⟩:=RetainedLow.paid_cell_budgets
    (Fintype.card RayCharacter) N cellWidth Bscale₀ Mmin Mmax hcw hscale hMmin
    (1/4:ℝ) (9/4:ℝ) (by norm_num) TP CP DP C hCP.le hDP.le hC.le degreeP Φ
    Bmaskcap εmask δ Brestore εwindow hεmask.le hεwindow
  refine ⟨J,Spaid,Cpaid,hCpaid,?_⟩
  filter_upwards [hfamilies,hpaid] with Z hZsource hZpaid
  refine ⟨hZsource.1,?_⟩
  intro T reflected second s modifier R₀ seed K ξ hK bin hR₀ hanchor
    left unit labels ray₁ ray₂ DataLabel _ column datum first row hfirst hparent hchild hkey hray
    L hL Cf hLC hCL d hd hmaskR hmaskcap τ z parentR hrow hsupport hnorm hnonfixed
    p W₁ W₂ θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    weight hweight X₁ X₂ hX A₁ A₂ hA₁ hA₂ hAR havoid hcut
    lo hi γ hγ hlo hhi st hQM hQη hcharacter hpuncture hwidth hkeep
    aLow iBin haLow haLow' hwT hwr hσT hσT' hfreq hheight hlow
    D slot value select radius hselect hradius hradial hadmit
    x₀ x₁ side factor massLoss gapH target Bmissing hfactor hmissing hraw hmass hHcell hprice
  have ha : 0<(1/4:ℝ):=by norm_num
  have hb : 0≤(9/4:ℝ):=by norm_num
  have hs₁ : Function.support (W₁:ℝ→ℂ)⊆Set.Icc (1/4:ℝ) (9/4:ℝ):=p.support 0
  have hs₂ : Function.support (W₂:ℝ→ℂ)⊆Set.Icc (1/4:ℝ) (9/4:ℝ):=p.support 1
  obtain ⟨Acell,hA,hAdom,hsum⟩:=hZpaid.2 labels α Finset.univ T
    ((Finset.card_le_univ T).trans hN) p t height εsource loss factor Cslot target massLoss gapH
    εlow densityWidth q hh hfactor hCslot hεlow.le hdensity.le
    ((geometryRawFixedMask s R₀*L)*(d.1*d.2)) hmaskR hmaskcap
    X₁ X₂ weight x₀ x₁ radius side select value w hi Bmissing γ lo hmissing
    (fun l _=>hselect l) (fun l _=>hweight l) (fun l _=>hraw l)
    (fun l _=>hradius l) (fun l _=>hmass l) (fun l _=>hHcell l) (fun l _=>hprice l)
  have hs:=hZsource.2 T reflected second s modifier R₀ seed K ξ hK bin hR₀ hanchor
    labels ray₁ ray₂ column datum first row hfirst hparent hchild hkey hray
    L hL Cf hLC hCL d hd hrow hsupport hnorm hnonfixed
    W₁ W₂ ha hb hs₁ hs₂ θ w σ freq t height hw hwm hσlo hσhi hh hv hprime hβ hslot
    Φ hΦs hΦ weight hweight X₁ X₂ hX A₁ A₂ hA₁ hA₂ hAR havoid δ Brestore hδ hBrestore hcut
    lo hi γ hγ hlo hhi st hQM hQη hcharacter hpuncture hwidth hkeep
    aLow iBin haLow haLow' hwT hwr hσT hσT' hfreq hheight hlow
    select radius cellWidth hcw hselect hradius hradial hΦone hadmit
    Acell hA (fun l=>hAdom l (Finset.mem_univ l))
  dsimp only [RegularLowBudgetControl.cellBudget,RegularLowBudgetControl.positiveWindow] at hsum
  apply hs.trans
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro F _
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [W₁,W₂,profileFloor]
  ring

end
end QRH.Record1252270103Source.Admission
#print axioms QRH.Record1252270103Source.Admission.global_low_paid_positive_family
