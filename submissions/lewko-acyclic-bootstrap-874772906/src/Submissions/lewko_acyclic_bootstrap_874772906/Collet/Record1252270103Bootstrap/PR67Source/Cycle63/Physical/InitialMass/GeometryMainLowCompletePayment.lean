import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainLowFinalPayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainHighQuantitativePayment
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.Endpoint
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic CenteredMomentWholeDivisorShell CenteredMomentSlotRatios
open CenteredMomentCommonPairedSource
open CenteredMomentFirstChildProfileControl
open Cycle63FinalNatural Cycle63Moment.LowBranch
open Filter Set HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentCanonicalFirst
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentFirstAmplificationChoice CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondHeightFamily CenteredMomentSecondRadicalBudget
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentCommonHeightEnvelope CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRectangle CenteredMomentRetainedProfile CenteredMomentAllocatedRayDictionary
open CenteredMomentNaturalFixedRaySource CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentInductionEnergy CenteredMomentEligibleEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRawScale
open CenteredMomentCommonLinearNormalization CenteredMomentSourceLiveColumn
open Cycle63Moment LocalMoment
open CenteredMomentSecondInputCapacitySource
open CenteredMomentChildRows CenteredMomentSecondCanonical CenteredMomentSecondEnergySplit
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

local instance geometryMainLowCompleteDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := geometryMainCoarseFamilySumDecidable

variable [Cycle63.AffineLedger] in
/- The complete canonical ordinary low family, with both fixed ray sums,
exact buffer/sixteen fees and the absolute-box subpower payment composed.
The original full-nonzero filter and actual reduced second seeds remain literal. -/
set_option linter.unusedVariables false in
set_option linter.defProp false in
def MainLowCompletePhysicalSpec {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0<supply)(hev : 0<εv)
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels)
    (Adm : ℝ→ℝ→ℝ→Prop)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (ap εmass Bmass : ℝ)(hap : 0<ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L)
    (εfirst Cfirst εbox Cbox : ℝ)(degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ ℝ)
        (heightV height mesh : ℝ)
        (hcard : Fintype.card α≤N)(hmass : ∀j,s.M j≤Cs)(hsupply' : supply≤ s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)
        (hsupper : s.upper≤bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0≤w j)(hwL : ∀j,w j≤Lslot)
        (hwr : ∀j,w j/d≤Rwidth)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
        (hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤hi)(hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)
        (hT : 2<Z^τ)
        (hfreqbin : |heightV|+height+Z^τ/2≤5*Z^τ)
        (hβhi : HeckeZeroSupremum.beta≤7/8)
        (unit Mrow reserve ξ : ℝ)(hMmin : Mmin≤unit)(hAdm : Adm unit (frequencyLoss Z 32 ξ+reserve) ξ)
        (hω : 0≤frequencyLoss Z 32 ξ+reserve)(hξ : 0≤ξ)
        (hMcap' : unit+εwidth*unit+ξ/2≤Mcap)
        (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit)
        (hzslot : Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit)
        (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
          Cycle63.AffineLedger.B*unit)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=Cycle63.AffineLedger.cellUpper
          (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
        let amp:=unit*Cycle63.AffineLedger.amp cell
        let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let seed:=fun l=>(firstIndex l).1.val.2.1.val
        let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
        let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
          (Fintype.card α) (first l)
        let p:=((bin.2 2:ℝ)+1)*Real.logb Z 2
        let c : Fin 5:=if reflected then 1 else 0
        let exponent:=Real.logb Z (volume s)-(bin.2 c:ℝ)*Real.logb Z 2+
          ((bin.2 3:ℝ)+1)*Real.logb Z 2+((bin.2 4:ℝ)+1)*Real.logb Z 2
        let sideLower:=(bin.2 2:ℝ)*Real.logb Z 2+Real.logb Z (volume s)-
          ((bin.2 c:ℝ)+1)*Real.logb Z 2+(bin.2 3:ℝ)*Real.logb Z 2+(bin.2 4:ℝ)*Real.logb Z 2
        ∀(hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤Z^Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (hfirstproj : ∀l,seed₀∣firstProjectorRadical (first l).1.1 (first l).1.2 (first l).2.val)
          (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
          (hOriginal : ∀r∈rows,
            (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin)∈geometryMainNonzeroBlocks reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin hw₁ hw₂)
          (hU : ∀r∈rows,ActualSecondBlockIndex.IsInactive r.2)
          (box : Finset (Fin 4→ ℤ))
          (hboxCard : (box.card:ℝ)≤Cbox*Z^εbox)
          (hbox : ∀r∈rows,actualSecondDyad (childSrc r.1) (Rchild r.1) (seed r.1)
            (K r.1) (Tsec r.1) Z ξ r.2∈box),
        let datum : rows→ SecondInputDatum α:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
        ∀(B₂ : (r : rows)→ actualAllocations (childSrc r.val.1).pools
            (if second then (datum r).D else (datum r).C))
          (rwitness : (r : rows)→ secondLiveRows (fun _:Unit=>(datum r).block))
          (hf₂ : ∀r,frozenCoefficient (B₂ r).val
            (if second then (datum r).D else (datum r).C) (datum r).R
            (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0),
        let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
        let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          (rwitness r) (hf₁ r.val.1) (hf₂ r)
        ∀(χ₀ : rows→ RayFourExpansion.RayCharacter)
          (m : O)(hm₀ : m≠0)(hml : goodLambda∣m)(hm₂ : (2:O)∣m)
          (hP : ∀r,(q r).R₂*(q r).E₂≠0)
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤Z^Bmask)
          (divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ ℂ))
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ ap≤x)(hplain₂ : ∀x,s.W₂ x≠0→ ap≤x)
          (hpool : ∀j I,I∈s.pools j→ (I.absNorm:ℝ)≤Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j)≤window)
          (hplainScale : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j≤Z^L),
        let st:=fun (r : rows)(ray : RayFourExpansion.RayCharacter)=>retainedState Z Bmask hZ ((g r).datum.τ ray)
          (internalQ Q η₀) ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D
          (g r).datum.inactive
        ∀(left₁ : Bool)(u₀ : O)(unit₁ : FirstSourceLabel→O)(Tz : ℝ),
        left₁=!reflected → u₀≠0 →
        ((∀l,IsUnit (unit₁ l)) ∧ Real.logb Z (normValue u₀)≤ε) →
        let mult:=fun r : rows=>firstRowMultiplier first left₁ u₀ unit₁ r.val
        (∀r,∀ray,∀(W' : ℝ)(hW' : (st r ray).width≤W'),Presented η₀ Z (widenState (st r ray) W' hW') (mult r) Tz) →
        let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
          mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ
            (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
            (by exact hP r) (by exact hPN r) η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*unit+ξ/2-unit*(Cycle63.AffineLedger.lowReserve)+(unit-Mrow)+εold+2*ε*d*(Fintype.card α:ℝ)+
          Cycle63.AffineLedger.lowRate*(frequencyLoss Z 32 ξ+reserve+εpad*unit)+Cycle63.AffineLedger.q*mesh+pad
        let exponentFull:=Bmass*εmass+amp+error+εv+Bnorm*εshell+εlabels
        ∀(t₀ u : ℝ),heightV=t+2*Real.pi*(u-(if second then -t₀ else t₀)) →
        (∀r,divisorSeed r=(datum r).seed) →
        mainLowPhysicalCompleteCost N supply ap second
          (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
          (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u canonical≤
          ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*Cfirst*
            (1/lowerFactor N supply ap)*(Fintype.card (BufferIndex e):ℝ)*64*Cg*
            (2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*Cu*Cbox)*
            (p₀.control Sp)^2*physical*
            Z^(exponentFull+εfirst+(εunion+3*(((N:ℝ)+2)*U)*εshell)+εbox)/(seed₀.absNorm:ℝ)*
            (2*(1+|t|+height+2*Real.pi*(|t₀|+|u|)))^degree

attribute [local irreducible] mainLowPhysicalCompleteCost mainLowFixedRayPhysicalCost
variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 120000 in
theorem main_low_complete_physical_spec_of_final {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0<supply)(hev : 0<εv)
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels)
    (Adm : ℝ→ℝ→ℝ→Prop)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (ap εmass Bmass : ℝ)(hap : 0<ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L)
    (εfirst Cfirst εbox Cbox : ℝ)(degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (Z : ℝ)
    (hCg : 0≤Cg)(hCu : 0≤Cu)(hfirst : 0≤Cfirst)
    (hspec : MainLowFinalPhysicalSpec (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm Presented
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst degree Sp Cg Cu η₀ Q hQM hQ72 Z) :
    MainLowCompletePhysicalSpec (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm Presented
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst εbox Cbox degree Sp Cg Cu η₀ Q hQM hQ72 Z := by
  unfold MainLowCompletePhysicalSpec
  intro hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    unit Mrow reserve ξ hMmin hAdm hω hξ hMcap' hfit hzslot haff Label _ reflected second R seed₀ bin t firstIndex
    first cell amp childSrc Rchild seed K Tsec p c exponent sideLower hf₁ hw₁ hw₂ hsource
    hs₀ hs₀0 hinj hfirstproj rows hOriginal hU box hboxCard hbox datum B₂ rwitness hf₂ q g χ₀ m hm₀ hml hm₂
    hP hPN divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale st leftR uR unitR Tz hleft hu₀ hdict _ hpres canonical firstMass physical error
    exponentFull t₀ u hshift hseed
  have hk:=hspec
  unfold MainLowFinalPhysicalSpec at hk
  have hkfirst:=hk hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    unit Mrow reserve ξ hMmin hAdm hω hξ hMcap' hfit hzslot haff reflected second R seed₀ bin t firstIndex
    hf₁ hw₁ hw₂ hsource hs₀ hs₀0 hinj hfirstproj
  have hkrows:=hkfirst rows hOriginal hU box hbox
  have hkb:=hkrows B₂ rwitness hf₂
  have hray (χ ψ : RayFourExpansion.RayCharacter) :
      mainLowFixedRayPhysicalCost N supply ap second
        (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
        (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u χ ψ
        (fun r=>canonical r χ ψ)≤
      Cfirst*Z^εfirst*((1/lowerFactor N supply ap)*(Fintype.card (BufferIndex e):ℝ)*
        ((64*mainLowQuantitativeFactor Cg b Cs (p₀.control Sp) heightV height physical Z
          exponentFull (seed₀.absNorm:ℝ) N degree box.card)*
          (Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)))) := by
    exact hkb χ₀ χ ψ m hm₀ hml hm₂ hP hPN divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ
      hsourceOriginal hplain₁ hplain₂ hpool hwindowSource hplainScale
      leftR uR unitR Tz hleft hu₀ hdict (fun r W' hW'=>hpres r (if second then ψ⁻¹ else χ) W' hW') t₀ u hshift hseed
  have hfull := Finset.sum_le_sum (s:=Finset.univ) (fun χ _=>
    Finset.sum_le_sum (s:=Finset.univ) (fun ψ _=>hray χ ψ))
  rw [main_low_physical_complete_ray_sum]
  apply le_trans hfull
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [hshift]
  have hseedNorm : 0<(seed₀.absNorm:ℝ) := by
    apply Nat.cast_pos.mpr
    exact Nat.pos_of_ne_zero (fun h=>hs₀0 (Ideal.absNorm_eq_zero_iff.mp h))
  simpa only [pow_two,mul_assoc] using main_low_physical_small_fee_bound N degree e second supply ap Cg Cu Cfirst Cbox b Cs
    (p₀.control Sp) t height t₀ u physical Z exponentFull (seed₀.absNorm:ℝ)
    εfirst (εunion+3*(((N:ℝ)+2)*U)*εshell) εbox box.card
    (lowerFactor_pos N supply ap hsupply hap) hCg hCu hfirst (zero_le_one.trans hCs) hheight
    (geometry_high_factor_pos reflected (geometrySupportConstant N supply ap ap) bin
      (geometrySupportConstant_pos N supply ap ap hsupply hap hap)).le
    (zero_lt_one.trans hZ) hseedNorm hboxCard

attribute [local irreducible] MainLowCompletePhysicalSpec MainLowFinalPhysicalSpec
variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 100000 in
def actual_main_low_complete_physical_bins {Adm : ℝ→ℝ→ℝ→Prop} {labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ}
    {Presented : (Bmask : ℝ) → Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop}
    (hgate : LowBinGate labelExp 6) {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0<supply)(hev : 0<εv)
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels)
    (hrow5 : LowSelectedStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin
      εshell N Cs supply εv Bnorm εlabels Adm labelExp (Presented Bmask))
    (ap εmass Bmass : ℝ)(hap : 0<ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L) (hτgap : 2*τ<d*η) (hBstrong : Bmass+1≤Bnorm) (εfirst : ℝ)(hefirst : 0<εfirst) (εbox Cbox : ℝ) :
    ∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤M),
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀≤Ideal.span {(72:O)},
      Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,ΣCfirst : ℝ,
        PLift (0<Cu ∧ 0<Cfirst) ×
        ΣCg : ℝ,PLift (0<Cg ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
          MainLowCompletePhysicalSpec (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm (Presented Bmask)
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst εbox Cbox degree Sp Cg Cu η₀ Q hQM hQ72 Z) := by
  intro η₀ Q hQM hQ0 hQt hQ72
  let k:=actual_main_low_final_physical_bins (α:=α) M H hH hgate
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel hrow5
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      hτgap hBstrong εfirst hefirst η₀ Q hQM hQ0 hQt hQ72
  refine ⟨k.1,k.2.1,k.2.2.1,k.2.2.2.1,k.2.2.2.2.1,?_⟩
  let hc:=k.2.2.2.2.2
  refine ⟨hc.1,PLift.up ⟨hc.2.down.1,?_⟩⟩
  filter_upwards [hc.2.down.2] with Z hz
  refine ⟨hz.1,?_⟩
  exact main_low_complete_physical_spec_of_final (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm (Presented Bmask)
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst k.2.2.2.1 εbox Cbox k.1 k.2.1 hc.1 k.2.2.1 η₀ Q hQM hQ72 Z
      hc.2.down.1.le k.2.2.2.2.1.down.1.le k.2.2.2.2.1.down.2.le hz.2

open CenteredMomentOriginalCommonHarmonic CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCommonPairedSource

variable [Cycle63.AffineLedger] in
/-- Exact ordinary image of the selected original blocks, retaining both rays and the signed row. -/
def mainLowCompleteImageRows {Label Original : Type*} [Fintype Label] [Fintype Original]
    (embed : Label→Original)(d : Original→SecondInputDatum α)
    (χ₀ : Label→RayFourExpansion.RayCharacter)(Q : Label→ Ideal O)(m : Label→O)
    (hrows : ∀l,(d (embed l)).rows=sourceRows
      (d (embed l)).C (d (embed l)).D (d (embed l)).inactive (d (embed l)).radius)
    (second : Bool){e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l))
        (fun _=>True)→BufferIndex e) :=
  ((mainLowPhysicalOrdinaryRows second
    (fun l=>ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l)) select).image
      (ordinaryHighOriginalRow (fun l=>d (embed l)) χ₀ Q m hrows)).image
        (mainLowOriginalLabelRow embed d)

variable [Cycle63.AffineLedger] in
theorem main_low_complete_image_cost {Label Original : Type*}
    [Fintype Label] [Fintype Original]
    (embed : Label→Original)(hinj : Function.Injective embed)
    (N : ℕ)(a ap : ℝ)(second : Bool)(d : Original→SecondInputDatum α)
    (χ₀ : Label→RayFourExpansion.RayCharacter)(Q : Label→ Ideal O)(m : Label→O)
    (hrows : ∀l,(d (embed l)).rows=sourceRows
      (d (embed l)).C (d (embed l)).D (d (embed l)).inactive (d (embed l)).radius)
    (coefficient : Original→ℝ)(t u : ℝ){e : ℝ}
    (select : (l : Label)→(χ ψ : RayFourExpansion.RayCharacter)→
      mainLowSourceRows second (ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l))
        (fun _=>True)→BufferIndex e) :
    mainLowPhysicalCompleteCost N a ap second
      (fun l=>ordinarySecondDatum (d (embed l)) (χ₀ l) (Q l) (m l))
      (fun l=>coefficient (embed l)) t u select=
    ∑r : mainLowCompleteImageRows embed d χ₀ Q m hrows second select,
      (coefficient r.val.val.1*((d r.val.val.1).K/lowerFactor N a ap)*
        normalizer (d r.val.val.1).C (d r.val.val.1).D (d r.val.val.1).inactive)*
      highNormalizedRowCost second d r.val
        ((d r.val.val.1).input.t+2*Real.pi*(u-(if second then -t else t)))
        ((d r.val.val.1).block.divisors.filter Squarefree) := by
  rw [actual_main_low_physical_full_original_row_cost embed hinj]
  exact (Finset.sum_coe_sort _ _).symm

private theorem low_complete_scalar_sum {J : Type*}[Fintype J]
    (mass radius volume normal value : J→ℝ)(lower : ℝ) :
    (∑r,mass r/volume r*(radius r/lower)*normal r*value r)=
      ∑r,mass r*(radius r/volume r)*normal r/lower*value r := by
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

attribute [local irreducible] mainLowCompleteImageRows

variable [Cycle63.AffineLedger] in
def MainLowCompleteCoarseSpec {α : Type} [Fintype α] [DecidableEq α]
    (N : ℕ) (B Cs b bs window plainCap lo ap εmass ξ U exponent K Z : ℝ) : Prop :=
    ∀hZ : 1<Z,
      ∀{Label : Type}[Fintype Label]
      (reflected : Bool)(s : Input α)(R seed : Ideal O)(Dfirst a reserve t : ℝ)(hK : 0<Z^Dfirst),
      Squarefree seed → Endpoints b bs bs s →
      lo≤ s.lower → sourceRadius s≤Z^B → |Real.logb Z (volume s)|≤B → |Dfirst|≤B →
      |a|≤B → |frequencyLoss Z 32 ξ+reserve|≤B → (∀j,s.M j≤Cs) →
      (∀j,CenteredMomentSlotRatios.logWindow (s.lo j) (s.hi j)≤window) →
      (∀second j,Cycle63.Physical.sourcePlainScales s.toData.toSource second j≤Z^plainCap) →
      (∀j,s.P j≤Z^plainCap) →
      (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
      (∀x,s.W₁ x≠0→ap≤x) → (∀x,s.W₂ x≠0→ap≤x) →
      ∀(hs₁ : s.W₁ 0=0)(hs₂ : s.W₂ 0=0),0≤a → 0≤ reserve →
      ∀(bin : ℤ×(Fin 5→ℤ))
        (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Dfirst) Z ξ hK bin),
      Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val,
        (firstIndex l).1.val.2.1.val)) →
      (∀l,frozenCoefficient (firstIndex l).2.val
        (geometryColumnIdeal reflected s R seed (Z^Dfirst) Z ξ hK bin (firstIndex l).1.val) R s.ν s.W s.P≠0) →
      let Index := (l : Label)×GeometryLowSecondIndex reflected s R seed Z Dfirst a ξ reserve b t N hZ bin (firstIndex l)
      let datum : Index→SecondInputDatum α := fun q=>geometryLowSecondDatum reflected s R seed Z Dfirst a ξ reserve b t N hZ bin
        (firstIndex q.1) hs₁ hs₂ q.2
      ∀(rows : Finset Index)(second : Bool)(W : 𝓢(ℝ,ℂ))
        (χ₀ : rows→RayFourExpansion.RayCharacter)(Q : rows→ Ideal O)(m : rows→O)
        (t₀ u e control B₁ B₂ : ℝ),
      0≤ control → 0≤B₁ → 0≤B₂ →
      (∀x,‖s.W₁ x‖≤B₁) → (∀x,‖s.W₂ x‖≤B₂) → (B₁*B₂)^2≤ control →
      ∀select : (r : rows)→(χ ψ : RayFourExpansion.RayCharacter)→
        mainLowSourceRows second (ordinarySecondDatum (datum r.val) (χ₀ r) (Q r) (m r))
          (fun _=>True)→BufferIndex e,
      mainLowPhysicalCompleteCost N lo ap second
        (fun r : rows=>ordinarySecondDatum (datum r.val) (χ₀ r) (Q r) (m r))
        (fun r=>geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
          (firstIndex r.val.1).1.val /
          volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hK bin t
            (firstIndex r.val.1))) t₀ u select≤
        K*control*geometryHighFactor reflected (geometrySupportConstant N lo ap ap) bin*Z^exponent

attribute [local irreducible] MainLowCompleteCoarseSpec
variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 120000 in
theorem main_low_complete_coarse_spec_of_original {α : Type} [Fintype α] [DecidableEq α]
    (N : ℕ) (B Cs b bs window plainCap lo ap εmass ξ U exponent K Z : ℝ)
    (hc : MainHighCoarseSideSpec (α:=α) N B Cs b bs window plainCap lo ap εmass ξ U exponent K Z) :
    MainLowCompleteCoarseSpec (α:=α) N B Cs b bs window plainCap lo ap εmass ξ U exponent K Z := by
  unfold MainLowCompleteCoarseSpec
  intro hZ Label _ reflected s R seed Dfirst a reserve t hK hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin firstIndex hinj halloc Index datum
    rows second W χ₀ Q m t₀ u e control B₁ B₂ hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB select
  have hk:=hc
  unfold MainHighCoarseSideSpec at hk
  have hkfirst:=hk hZ reflected s R seed Dfirst a reserve t hK hseed he hlow hsource hA hMbox habox hω
    hM hwin hscales hP hpool hsap₁ hsap₂ hs₁ hs₂ ha hreserve bin firstIndex hinj halloc
  let coefficient : Index→ℝ:=fun r=>
    geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin (firstIndex r.1).1.val /
      volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hK bin t (firstIndex r.1))
  have hrows : ∀r : rows,(datum r.val).rows=sourceRows
      (datum r.val).C (datum r.val).D (datum r.val).inactive (datum r.val).radius := by
    intro r
    rfl
  let imageRows:=mainLowCompleteImageRows (fun r : rows=>r.val) datum χ₀ Q m hrows second select
  rw [main_low_complete_image_cost (fun r : rows=>r.val) Subtype.val_injective
    N lo ap second datum χ₀ Q m hrows coefficient t₀ u select]
  have hraw:=hkfirst imageRows second W
    (fun r=>(datum r.val.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
    (fun r=>(datum r.val.val.1).block.divisors.filter Squarefree)
    control B₁ B₂ hcontrol hB₁ hB₂ hW₁ hW₂ hcontrolB
    (fun r D hD=>Finset.mem_filter.mp hD)
  have hdatumK : ∀r : imageRows,(datum r.val.val.1).K=
      firstMainRadius reflected (Z^Dfirst) (volume s) Z ξ (3*a) reserve
        (geometryFirstLabel s R seed (Z^Dfirst) Z ξ hK bin (firstIndex r.val.val.1.1).1.val) := fun _=>rfl
  simp_rw [←hdatumK] at hraw
  change (∑r : imageRows,
    (geometryFirstHighMass reflected s R seed W Dfirst Z ξ εmass hK bin
      (firstIndex r.val.val.1.1).1.val /
      volume (geometryLowFirstChild reflected s R seed (Z^Dfirst) Z ξ hK bin t
        (firstIndex r.val.val.1.1)))*((datum r.val.val.1).K/lowerFactor N lo ap)*
      normalizer (datum r.val.val.1).C (datum r.val.val.1).D (datum r.val.val.1).inactive*
      highNormalizedRowCost second datum r.val
        ((datum r.val.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((datum r.val.val.1).block.divisors.filter Squarefree))≤_
  rw [low_complete_scalar_sum]
  exact hraw

/-- This degree depends only on the scalar coarse exponent, target floor,
common positive tau and already saved low degree. -/
def mainLowCompleteHeightDegree (coarse targetMin τ : ℝ)(hτ : 0<τ)(smallDegree : ℕ) : ℕ :=
  Classical.choose (geometry_uniform_shifted_height_splice coarse targetMin τ hτ smallDegree)

def mainLowCompleteFee (N : ℕ)(e supply ap Cg Cu Cfirst Cbox b Cs : ℝ) : ℝ :=
  (Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*Cfirst*
    (1/lowerFactor N supply ap)*(Fintype.card (BufferIndex e):ℝ)*64*Cg*
    (2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*Cu*Cbox

def mainLowCompleteHeightConstant (N degreeAll : ℕ)(e supply ap Cg Cu Cfirst Cbox b Cs Kcoarse : ℝ) : ℝ :=
  (2+4*Real.pi)^degreeAll*(1+mainLowCompleteFee N e supply ap Cg Cu Cfirst Cbox b Cs+Kcoarse)

open CenteredMomentNaturalRowSource

variable [Cycle63.AffineLedger] in
theorem actual_main_low_complete_coarse_payment {α : Type}[Fintype α][DecidableEq α]
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (N : ℕ)(hα : Fintype.card α≤N)
    (B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U : ℝ)
    (hB : 0≤B)(hloss : 0<loss)(hε : 0<ε)(hpad : 0<pad)
    (hCs : 1≤Cs)(hb : 1≤b)(hbs : 1≤bs)(hwindow : 0≤window)(hcap : 0≤plainCap)
    (hlo : 0<lo)(hap : 0<ap)(hev : 0<εvolume)(hem : 0≤εmass)
    (hξ : 0≤ξ)(hξε : ξ≤loss)(hU : 0≤U) :
    ∃K : ℝ,0<K ∧ ∀ᶠ Z : ℝ in atTop,
      MainLowCompleteCoarseSpec (α:=α) N B Cs b bs window plainCap lo ap εmass ξ U
        (B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
          8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε+B) K Z := by
  have hc:=actual_main_high_original_coarse_side_payment
    η₀ u₀ F₀ R₀ hu₀ N hα B loss ε pad Cs b bs window plainCap lo ap εvolume εmass ξ U
    hB hloss hε hpad hCs hb hbs hwindow hcap hlo hap hev hem hξ hξε hU
  obtain ⟨K,hK,hc⟩:=hc
  refine ⟨K,hK,?_⟩
  filter_upwards [hc] with Z hz
  exact main_low_complete_coarse_spec_of_original N B Cs b bs window plainCap lo ap εmass ξ U
    (B+(39*(B+loss)+(B+loss)*εmass+(B+loss)*ε+εvolume)+
      8*(B+loss)+3*loss+((N:ℝ)+2)*plainCap+2*pad+3*(((N:ℝ)+2)*U)*ε+B) K Z hz

variable [Cycle63.AffineLedger] in
set_option linter.unusedVariables false in
set_option linter.defProp false in
set_option maxHeartbeats 180000 in
def MainLowCompleteAllHeightSpec {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0<supply)(hev : 0<εv)
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels)
    (Adm : ℝ→ℝ→ℝ→Prop)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (ap εmass Bmass : ℝ)(hap : 0<ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L)
    (εfirst Cfirst εbox Cbox ξ₀ Bcoarse plainCap targetMin Kall : ℝ)(degreeAll : ℕ)(degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ ℝ)
        (heightV height mesh : ℝ)
        (hcard : Fintype.card α≤N)(hmass : ∀j,s.M j≤Cs)(hsupply' : supply≤ s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)
        (hsupper : s.upper≤bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0≤w j)(hwL : ∀j,w j≤Lslot)
        (hwr : ∀j,w j/d≤Rwidth)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
        (hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤hi)(hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)
        (hT : 2<Z^τ)
        (hβhi : HeckeZeroSupremum.beta≤7/8)
        (unit Mrow reserve ξ : ℝ)(hMmin : Mmin≤unit)(hAdm : Adm unit (frequencyLoss Z 32 ξ+reserve) ξ)
        (hω : 0≤frequencyLoss Z 32 ξ+reserve)(hξ : 0≤ξ)
        (hMcap' : unit+εwidth*unit+ξ/2≤Mcap)
        (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit)
        (hzslot : Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit)
        (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
          Cycle63.AffineLedger.B*unit)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=Cycle63.AffineLedger.cellUpper
          (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
        let amp:=unit*Cycle63.AffineLedger.amp cell
        let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let seed:=fun l=>(firstIndex l).1.val.2.1.val
        let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
        let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
          (Fintype.card α) (first l)
        let p:=((bin.2 2:ℝ)+1)*Real.logb Z 2
        let c : Fin 5:=if reflected then 1 else 0
        let exponent:=Real.logb Z (volume s)-(bin.2 c:ℝ)*Real.logb Z 2+
          ((bin.2 3:ℝ)+1)*Real.logb Z 2+((bin.2 4:ℝ)+1)*Real.logb Z 2
        let sideLower:=(bin.2 2:ℝ)*Real.logb Z 2+Real.logb Z (volume s)-
          ((bin.2 c:ℝ)+1)*Real.logb Z 2+(bin.2 3:ℝ)*Real.logb Z 2+(bin.2 4:ℝ)*Real.logb Z 2
        ∀(hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤Z^Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (hfirstproj : ∀l,seed₀∣firstProjectorRadical (first l).1.1 (first l).1.2 (first l).2.val)
          (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
          (hOriginal : ∀r∈rows,
            (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin)∈geometryMainNonzeroBlocks reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin hw₁ hw₂)
          (hU : ∀r∈rows,ActualSecondBlockIndex.IsInactive r.2)
          (box : Finset (Fin 4→ ℤ))
          (hboxCard : (box.card:ℝ)≤Cbox*Z^εbox)
          (hbox : ∀r∈rows,actualSecondDyad (childSrc r.1) (Rchild r.1) (seed r.1)
            (K r.1) (Tsec r.1) Z ξ r.2∈box),
        let datum : rows→ SecondInputDatum α:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
        ∀(B₂ : (r : rows)→ actualAllocations (childSrc r.val.1).pools
            (if second then (datum r).D else (datum r).C))
          (rwitness : (r : rows)→ secondLiveRows (fun _:Unit=>(datum r).block))
          (hf₂ : ∀r,frozenCoefficient (B₂ r).val
            (if second then (datum r).D else (datum r).C) (datum r).R
            (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0),
        let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
        let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          (rwitness r) (hf₁ r.val.1) (hf₂ r)
        ∀(χ₀ : rows→ RayFourExpansion.RayCharacter)
          (m : O)(hm₀ : m≠0)(hml : goodLambda∣m)(hm₂ : (2:O)∣m)
          (hP : ∀r,(q r).R₂*(q r).E₂≠0)
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤Z^Bmask)
          (divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ ℂ))
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ ap≤x)(hplain₂ : ∀x,s.W₂ x≠0→ ap≤x)
          (hpool : ∀j I,I∈s.pools j→ (I.absNorm:ℝ)≤Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j)≤window)
          (hplainScale : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j≤Z^L)
          (hend : Endpoints b bs bs s)
          (hsourceCoarse : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bcoarse)
          (hvolumeCoarse : |Real.logb Z (volume s)|≤Bcoarse)
          (hMrowCoarse : |Mrow|≤Bcoarse)(hampCoarse : |amp|≤Bcoarse)
          (homegaCoarse : |frequencyLoss Z 32 ξ+reserve|≤Bcoarse)
          (hscalesCoarse : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j≤Z^plainCap)
          (hprimeCoarse : ∀j,s.P j≤Z^plainCap)
          (hamp0 : 0≤amp)(hreserve0 : 0≤ reserve)(hξeq : ξ=ξ₀)
          (B₁ B₂ : ℝ)(hB₁ : 0≤B₁)(hB₂ : 0≤B₂)
          (hnorm₁ : ∀x,‖s.W₁ x‖≤B₁)(hnorm₂ : ∀x,‖s.W₂ x‖≤B₂)
          (hcontrol : (B₁*B₂)^2≤(p₀.control Sp)^2),
        let st:=fun (r : rows)(ray : RayFourExpansion.RayCharacter)=>retainedState Z Bmask hZ ((g r).datum.τ ray)
          (internalQ Q η₀) ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D
          (g r).datum.inactive
        ∀(left₁ : Bool)(u₀ : O)(unit₁ : FirstSourceLabel→O)(Tz : ℝ),
        left₁=!reflected → u₀≠0 →
        ((∀l,IsUnit (unit₁ l)) ∧ Real.logb Z (normValue u₀)≤ε) →
        let mult:=fun r : rows=>firstRowMultiplier first left₁ u₀ unit₁ r.val
        (∀r,∀ray,∀(W' : ℝ)(hW' : (st r ray).width≤W'),Presented η₀ Z (widenState (st r ray) W' hW') (mult r) Tz) →
        let canonical:=fun (r : rows) (χ ψ : RayFourExpansion.RayCharacter)=>
          mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ
            (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
            (by exact hP r) (by exact hPN r) η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*unit+ξ/2-unit*(Cycle63.AffineLedger.lowReserve)+(unit-Mrow)+εold+2*ε*d*(Fintype.card α:ℝ)+
          Cycle63.AffineLedger.lowRate*(frequencyLoss Z 32 ξ+reserve+εpad*unit)+Cycle63.AffineLedger.q*mesh+pad
        let exponentFull:=Bmass*εmass+amp+error+εv+Bnorm*εshell+εlabels
        let target:=exponentFull+εfirst+(εunion+3*(((N:ℝ)+2)*U)*εshell)+εbox
        ∀(htarget : targetMin≤target)(t₀ u : ℝ),heightV=t+2*Real.pi*(u-(if second then -t₀ else t₀)) →
        (∀r,divisorSeed r=(datum r).seed) →
        mainLowPhysicalCompleteCost N supply ap second
          (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
          (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u canonical≤
          Kall*(p₀.control Sp)^2*physical*Z^target*
            (1+|t|+height)^degreeAll*(1+|t₀|)^degreeAll*(1+|u|)^degreeAll

attribute [local irreducible] MainLowCompleteAllHeightSpec
variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 140000 in
theorem main_low_complete_all_height_spec_of_receipts {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0< margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell) (N : ℕ)(Cs : ℝ)(hCs : 1≤Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0<supply)(hev : 0<εv)
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels)
    (Adm : ℝ→ℝ→ℝ→Prop)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (ap εmass Bmass : ℝ)(hap : 0<ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L)
    (εfirst Cfirst εbox Cbox ξ₀ Bcoarse plainCap targetMin coarse Kcoarse : ℝ)(degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M) (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) (Z : ℝ)
    (hCg : 0≤Cg)(hCu : 0≤Cu)(hfirst : 0≤Cfirst)(hboxC : 0≤Cbox)(hKcoarse : 0<Kcoarse)
    (hN : N=Fintype.card α)(hbsb : bs=b)
    (hspec : MainLowCompletePhysicalSpec (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm Presented
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst εbox Cbox degree Sp Cg Cu η₀ Q hQM hQ72 Z)
    (hc : MainLowCompleteCoarseSpec (α:=α) N Bcoarse Cs b bs window plainCap supply ap
      εmass ξ₀ U coarse Kcoarse Z) :
    0< mainLowCompleteHeightConstant N (mainLowCompleteHeightDegree coarse targetMin τ hτ degree)
      e supply ap Cg Cu Cfirst Cbox b Cs Kcoarse ∧ MainLowCompleteAllHeightSpec (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm Presented
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst εbox Cbox ξ₀ Bcoarse plainCap targetMin
        (mainLowCompleteHeightConstant N (mainLowCompleteHeightDegree coarse targetMin τ hτ degree)
          e supply ap Cg Cu Cfirst Cbox b Cs Kcoarse)
        (mainLowCompleteHeightDegree coarse targetMin τ hτ degree) degree Sp Cg Cu η₀ Q hQM hQ72 Z := by
  subst N bs
  let fee := (Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*Cfirst*
    (1/lowerFactor (Fintype.card α) supply ap)*(Fintype.card (BufferIndex e):ℝ)*64*Cg*
    (2*b^2*Cs^(4*Fintype.card α))*QuadraticInitialBound.diagonalControl ballProfile*Cu*Cbox
  have hfee : 0≤fee := by
    dsimp only [fee]
    have hl := (lowerFactor_pos (Fintype.card α) supply ap hsupply hap).le
    have hd := QuadraticInitialBound.diagonalControl_nonneg ballProfile
    positivity
  let Csmall:=1+fee
  have hCsmall : 0<Csmall := by dsimp only [Csmall]; linarith
  let degreeAll:=mainLowCompleteHeightDegree coarse targetMin τ hτ degree
  have hext:=Classical.choose_spec (geometry_uniform_shifted_height_splice coarse targetMin τ hτ degree)
  let Kall:=(2+4*Real.pi)^degreeAll*(Csmall+Kcoarse)
  have hKall : 0<Kall := by dsimp only [Kall]; positivity
  refine ⟨hKall,?_⟩
  unfold MainLowCompleteAllHeightSpec
  intro hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hβhi
    unit Mrow reserve ξ hMmin hAdm hω hξ hMcap' hfit hzslot haff Label _ reflected second R seed₀ bin t firstIndex
    first cell amp childSrc Rchild seed K Tsec p c exponent sideLower hf₁ hw₁ hw₂ hsource
    hs₀ hs₀0 hinj hfirstproj rows hOriginal hU box hboxCard hbox datum B₂ rwitness hf₂ q g χ₀ m hm₀ hml hm₂
    hP hPN divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale hend hsourceCoarse hvolumeCoarse hMrowCoarse hampCoarse homegaCoarse
    hscalesCoarse hprimeCoarse hamp0 hreserve0 hξeq B₁ B₂bound hB₁ hB₂ hnorm₁ hnorm₂ hcontrol
    st leftR uR unitR Tz hleft hu₀ hdict _ hpres canonical firstMass physical error exponentFull target htarget t₀ u
    hshift hseed
  let E:=mainLowPhysicalCompleteCost (Fintype.card α) supply ap second
    (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
    (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u canonical
  have hphysical : 0≤physical := (geometry_high_factor_pos reflected
    (geometrySupportConstant (Fintype.card α) supply ap ap) bin
    (geometrySupportConstant_pos (Fintype.card α) supply ap ap hsupply hap hap)).le
  have hsmall : 2*(1+|t|+height+2*Real.pi*(|t₀|+|u|))≤Z^τ →
      E≤Csmall*((p₀.control Sp)^2*physical)*Z^target*
        (2*(1+|t|+height+2*Real.pi*(|t₀|+|u|)))^degree := by
    intro hH
    have hfreqbin : |heightV|+height+Z^τ/2≤5*Z^τ := by
      rw [hshift]
      exact main_low_payment_shifted_height_envelope second t height t₀ u (Z^τ)
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hH
    have hs:=hspec
    unfold MainLowCompletePhysicalSpec at hs
    have hsfirst:=hs hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsupper hsb₁ hsb₂
      hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
      unit Mrow reserve ξ hMmin hAdm hω hξ hMcap' hfit hzslot haff reflected second R seed₀ bin t firstIndex
      hf₁ hw₁ hw₂ hsource hs₀ hs₀0 hinj hfirstproj
    have hsrows:=hsfirst rows hOriginal hU box hboxCard hbox
    have hsalloc:=hsrows B₂ rwitness hf₂ χ₀ m hm₀ hml hm₂ hP hPN divisorSeed hE₂ hdivisor
    have hbound:=hsalloc p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool hwindowSource hplainScale
      leftR uR unitR Tz hleft hu₀ hdict hpres t₀ u hshift hseed
    have hseedNorm : (1:ℝ)≤(seed₀.absNorm:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hs₀0)
    have hY : 0≤fee*((p₀.control Sp)^2*physical)*Z^target*
        (2*(1+|t|+height+2*Real.pi*(|t₀|+|u|)))^degree :=
      mul_nonneg (mul_nonneg (mul_nonneg hfee (mul_nonneg (sq_nonneg _) hphysical))
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) (by positivity)
    have hbound' : E≤fee*((p₀.control Sp)^2*physical)*Z^target*
        (2*(1+|t|+height+2*Real.pi*(|t₀|+|u|)))^degree := by
      refine le_trans ?_ (div_le_self hY hseedNorm)
      convert hbound using 1; ring
    apply hbound'.trans
    have hf : fee≤Csmall := by dsimp only [Csmall]; linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hf (by positivity))
        (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)) (by positivity)
  have hb : E≤Kcoarse*((p₀.control Sp)^2*physical)*Z^coarse := by
    have hcξ:=hc
    rw [←hξeq] at hcξ
    unfold MainLowCompleteCoarseSpec at hcξ
    have hcfirst:=hcξ hZ reflected s R seed₀ Mrow amp reserve t
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hs₀ hend hsupply' hsourceCoarse
      hvolumeCoarse hMrowCoarse hampCoarse homegaCoarse hmass hwindowSource hscalesCoarse hprimeCoarse
      hpool hplain₁ hplain₂ hw₁ hw₂ hamp0 hreserve0 bin firstIndex hinj hf₁
    have hcb:=hcfirst rows second Ψ χ₀ (fun _=>internalQ Q η₀) (fun _=>m) t₀ u e
      ((p₀.control Sp)^2) B₁ B₂bound (sq_nonneg _) hB₁ hB₂ hnorm₁ hnorm₂ hcontrol canonical
    simpa only [E,datum,firstMass,childSrc,physical,mul_assoc] using hcb
  have hout:=hext Z target t height t₀ u E Csmall Kcoarse ((p₀.control Sp)^2*physical)
    hZ.le htarget hheight hCsmall.le hKcoarse.le (by positivity) hsmall hb
  dsimp only [mainLowCompleteHeightConstant,mainLowCompleteFee,mainLowCompleteHeightDegree]
  convert hout using 1
  dsimp only [Csmall,fee]
  ring

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
