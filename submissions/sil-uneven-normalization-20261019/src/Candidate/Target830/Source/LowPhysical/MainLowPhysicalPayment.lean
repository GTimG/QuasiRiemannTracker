import Candidate.Target830.Parameters
import Candidate.Target830.Source.Low.PaidMain
import Candidate.Target830.Source.LowPhysical.MainLowPhysicalCost
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPhysicalPayment
import Candidate.Target830.Source.Low.PaidMain
import Candidate.Target830.Source.LowPhysical.MainLowQuantitativePayment
import Candidate.Target830.Source.LowPhysical.MainLowNormalizedPayment
import Candidate.Cycle63.Physical.InitialMass.SecondLowSourceCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryShiftedHeight
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.Target830.Source.LowPhysical
noncomputable section
open OAI OAI.SevenEighths
open OAI.SevenEighths.Target830.Source.LowBranch
open OAI.SevenEighths.Cycle63InitialMass
open scoped Classical BigOperators SchwartzMap ContDiff
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
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

local notation "O" => HeckeFamily.O
local instance geometryMainLowPhysicalRestDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _


def MainLowPhysicalBinSpec (P : SourcePlane) {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (ha : 0 < a) (ha' : a ≤ 1/4) (hb : 1 ≤ b)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1 ≤ bs) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin)
    (εshell : ℝ) (heshell : 0 < εshell) (N : ℕ)(Cs : ℝ)(hCs : 1 ≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0 < supply)(hev : 0 < εv)
    (hBnorm : 0 ≤ Bnorm)(hel : 0 < εlabels)
    (ap εmass Bmass : ℝ)(hap : 0 < ap)(hemass : 0 ≤ εmass)
    (U εunion : ℝ)(hUcap : 0 ≤ U)(heunion : 0 < εunion)
    (window pad : ℝ)(hwindow : 0 ≤ window)(hpad : 0 < pad)(hL0 : 0 ≤ L)
    (degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q ≤ M) (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (Z : ℝ) : Prop :=
  ∀(hZ : 1 < Z)(s : Input α)(θ : α→ RayQuotient.Characters M H)(w σ freq : α→ ℝ)
        (heightV height mesh : ℝ)
        (hcard : Fintype.card α ≤ N)(hmass : ∀j,s.M j ≤ Cs)(hsupply' : supply ≤ s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)(hsη : s.η=ηseed)
        (hsupper : s.upper ≤ bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0 ≤ w j)(hwL : ∀j,w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold)
        (hwr : ∀j,w j/d ≤ Rwidth)(hmesh : 0 ≤ mesh)(hwm : ∀j,w j ≤ mesh)
        (hσlo : ∀j,lo ≤ σ j)(hσhi : ∀j,σ j ≤ hi)(hheight : 0 ≤ height)(hfreq : ∀j,|freq j| ≤ height)
        (hT : 2 < Z^τ)
        (hfreqbin : |heightV|+height+Z^τ/2 ≤ 5*Z^τ)
        (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
        (Mrow reserve ξ : ℝ)(hMmin : Mmin ≤ Mrow)
        (hω : 0 ≤ frequencyLoss Z 32 ξ+reserve)(hξ : 0 ≤ ξ)
        (hMcap' : Mrow+εwidth*Mrow+ξ/2 ≤ Mcap)
        (hzslot : (17/500)*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j)) ≤ (1/25)*Mrow)
        (haff : length Z s.X₁+length Z s.X₂+P.lambda*(∑j,Real.logb Z (s.P j)) ≤ 
          P.B*Mrow)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ ℤ))(t : ℝ)
        (firstIndex : Label→ GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=widthCellUpper ((∑j,Real.logb Z (s.P j))/Mrow)
        let amp:=Mrow*P.amp cell
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
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l) ≤ Z^Bnorm)
          (Tfirst : ℝ)(hTfirst : 1 ≤ Tfirst)(hp : p ≤ Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (hfirstshell : ∀l,Tfirst ≤ ((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ) < 2*Tfirst)
          (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
          (hOriginal : ∀r∈rows,
            (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin)∈geometryMainNonzeroBlocks reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin hw₁ hw₂)
          (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
          (box : Finset (Fin 4→ ℤ))
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
        ∀(χ₀ : rows→ RayFourExpansion.RayCharacter)(χ ψ : RayFourExpansion.RayCharacter)
          (m : O)(hm₀ : m≠0)(hml : goodLambda∣m)(hm₂ : (2:O)∣m)
          (hP : ∀r,(q r).R₂*(q r).E₂≠0)
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ) ≤ Z^Bmask)
          (divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ ℂ))
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s ≤ Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ ap ≤ x)(hplain₂ : ∀x,s.W₂ x≠0→ ap ≤ x)
          (hpool : ∀j I,I∈s.pools j→ (I.absNorm:ℝ) ≤ Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j) ≤ window)
          (hplainScale : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j ≤ Z^L),
        let ray:=if second then ψ⁻¹ else χ
        let ordinaryRows:=fun r : rows=>mainLowSourceRows second
          (ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m) (fun _=>True)
        let canonical:=fun r : rows=>mainLowCanonicalSelector (P := P) M H hH (datum r) (χ₀ r) χ ψ
          (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
          (by exact hP r) (by exact hPN r) η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
        ∃select : (r : rows)→ ordinaryRows r→ BufferIndex e,
          (∀r,select r=canonical r) ∧
          (∀r pbin z,z∈mainLowPaymentRows (P := P) (ordinaryRows r) (select r) pbin→ 1 ≤ pbin.1.val) ∧
        let src:=fun r=>withHeight (q r).first ((g r).datum.τ ray) heightV
        let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
        let unionDs:=sharedProjectors Ds
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*Mrow+ξ/2-Mrow*lowReserve+εold+2*ε*d*(Fintype.card α:ℝ)+
          (P.q/(6*incumbentKappa))*(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)+P.q*mesh+pad
        let exponentFull:=Bmass*εmass+amp+error+εv+Bnorm*εshell+εlabels
        let factor : ℝ:=mainLowQuantitativeFactor (P := P) Cg b Cs (p₀.control Sp) heightV height physical Z
          exponentFull (seed₀.absNorm:ℝ) N degree box.card
        let coefficient:=fun (r : rows)(_D : Ideal O)=>
          firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
            normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
        let value:=fun (r : rows)(D : Ideal O)(z : O)=>
          ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2
        ∀(t₀ u : ℝ),heightV=t+2*Real.pi*(u-(if second then -t₀ else t₀)) →
        (∀r,divisorSeed r=(datum r).seed) →
        mainLowFixedRayPhysicalCost (P := P) N supply ap second
          (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
          (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u χ ψ select ≤ 
          (1/lowerFactor N supply ap)*(Fintype.card (BufferIndex e):ℝ)*
            ((16*factor)*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)))

attribute [local irreducible] MainLowPhysicalBinSpec actual_main_low_quantitative_bins
  MainLowQuantitativeBinSpec geometryMainNonzeroBlocks
set_option maxHeartbeats 320000 in
def actual_main_low_physical_bins (P : SourcePlane) {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (ha : 0 < a) (ha' : a ≤ 1/4) (hb : 1 ≤ b)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1 ≤ bs) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin)
    (εshell : ℝ) (heshell : 0 < εshell) (N : ℕ)(Cs : ℝ)(hCs : 1 ≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0 < supply)(hev : 0 < εv)
    (hBnorm : 0 ≤ Bnorm)(hel : 0 < εlabels)
    (ap εmass Bmass : ℝ)(hap : 0 < ap)(hemass : 0 ≤ εmass)
    (U εunion : ℝ)(hUcap : 0 ≤ U)(heunion : 0 < εunion)
    (window pad : ℝ)(hwindow : 0 ≤ window)(hpad : 0 < pad)(hL0 : 0 ≤ L) (hτgap : 2*τ < d*η) (hBmassNorm : Bmass ≤ Bnorm) :
    Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,
      PLift (0 < Cu) ×
      (∀(η₀ : Character)(Q : Ideal O)(hQM : Q ≤ M),
        internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)},     
        ΣCg : ℝ,PLift (0 < Cg ∧ ∀ᶠZ : ℝ in atTop,2 ≤ Z ∧
          MainLowPhysicalBinSpec (P := P) (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      degree Sp Cg Cu η₀ Q hQM hQ72 Z)) := by
  let k:=actual_main_low_quantitative_bins (P := P) (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0 hτgap hBmassNorm
  refine ⟨k.1,k.2.1,k.2.2.1,k.2.2.2.1,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  let hc:=k.2.2.2.2 η₀ Q hQM hQ0 hQt hQ72
  refine ⟨hc.1,PLift.up ⟨hc.2.down.1,?_⟩⟩
  filter_upwards [hc.2.down.2] with Z hz
  refine ⟨hz.1,?_⟩
  unfold MainLowPhysicalBinSpec
  intro hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff Label _ reflected second R seed₀ bin t firstIndex
    first cell amp childSrc Rchild seed K Tsec p c exponent sideLower hf₁ hw₁ hw₂ hsource
    Tfirst hTfirst hp hs₀ hs₀0 hinj hfirstshell
    rows hOriginal hU box hbox datum B₂ rwitness hf₂ q g χ₀ χ ψ m hm₀ hml hm₂ hP hPN
    divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale ray ordinaryRows canonical
  have hzq:=hz.2
  unfold MainLowQuantitativeBinSpec at hzq
  obtain ⟨select,heq,hpos,hbins,hfull⟩:=hzq hZ s θ w σ freq heightV height mesh hcard hmass
    hsupply' hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    Mrow reserve ξ hMmin hω hξ hMcap' hzslot haff reflected second R seed₀ bin t firstIndex
    hf₁ hw₁ hw₂ hsource Tfirst hTfirst hp hs₀ hs₀0 hinj hfirstshell
    rows hOriginal hU box hbox B₂ rwitness hf₂ χ₀ χ ψ m hm₀ hml hm₂ hP hPN
    divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale
  refine ⟨select,heq,hpos,?_⟩
  intro src Ds unionDs firstMass physical error exponentFull factor coefficient value t₀ u hshift hseed
  have hb:=fixed_ray_source_transport (P := P) (Label:=rows) N supply ap second
    (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
    (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u χ ψ select coefficient value _
    (lowerFactor_pos N supply ap hsupply hap)
    (fun _ _=>rfl)
    (fun r D z=>by
      change ‖normalizedColumn
        (withHeight (datum r).input (if second then (datum r).τ ψ⁻¹ else (datum r).τ χ)
          (t+2*Real.pi*(u-(if second then -t₀ else t₀))))
        (if second then (datum r).D else (datum r).C) _ (datum r).R (datum r).seed D z‖^2=_
      rw [←hshift,←hseed r]
      cases second <;> rfl)
    hfull
  convert hb using 1
  ring

/-- The kernel's actual signed height is paid by the same envelope used
by the all-height splice; neither Mellin variable is dropped. -/
theorem main_low_physical_signed_height (P : SourcePlane) (second : Bool) (v height t u : ℝ)
    (hh : 0 ≤ height) :
    1+|v+2*Real.pi*(u-(if second then -t else t))|+height ≤ 
      2*(1+|v|+height+2*Real.pi*(|t|+|u|)) := by
  have hs : |(if second then -t else t)|=|t| := by cases second <;> simp
  have hsub : |u-(if second then -t else t)| ≤ |u|+|t| := by
    simpa only [sub_zero,zero_sub,abs_neg,hs] using
      abs_sub_le u 0 (if second then -t else t)
  have hshift : |v+2*Real.pi*(u-(if second then -t else t))| ≤ 
      |v|+2*Real.pi*(|u|+|t|) := by
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
    simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hsub
      (show 0 ≤ 2*Real.pi by positivity)) |v|
  have hp : 0 ≤ 2*Real.pi*(|t|+|u|) := by positivity
  linarith [abs_nonneg v]

/-- Collapse the genuine kernel's exact sixteen, finite buffered-bin fee,
fixed rays and BOTH common-projector/absolute-box fees into the small-height
form. The original reciprocal seed and physical outer factor are retained. -/
theorem main_low_physical_small_fee_bound (P : SourcePlane)
    (N degree : ℕ) (e : ℝ) (second : Bool)
    (a ap Cg Cu Cfirst Cbox b Cs control v height t u physical Z exponent seedNorm
      εfirst εsecond εbox : ℝ) (boxCard : ℕ)
    (hlower : 0 < lowerFactor N a ap)
    (hCg : 0 ≤ Cg)(hCu : 0 ≤ Cu)(hfirst : 0 ≤ Cfirst)
    (hCs : 0 ≤ Cs)(hh : 0 ≤ height)(hphysical : 0 ≤ physical)(hZ : 0 < Z)(hseed : 0 < seedNorm)
    (hbox : (boxCard:ℝ) ≤ Cbox*Z^εbox) :
    (Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(Cfirst*Z^εfirst*
      ((1/lowerFactor N a ap)*(Fintype.card (BufferIndex e):ℝ)*
        ((16*mainLowQuantitativeFactor (P := P) Cg b Cs control
          (v+2*Real.pi*(u-(if second then -t else t))) height physical Z exponent seedNorm
          N degree boxCard)*(Cu*Z^εsecond)))) ≤ 
      ((Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*Cfirst*
        (1/lowerFactor N a ap)*(Fintype.card (BufferIndex e):ℝ)*16*Cg*
        (2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*Cu*Cbox)*
        control^2*physical*Z^(exponent+εfirst+εsecond+εbox)/seedNorm*
        (2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^degree := by
  have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
  have hheight:=pow_le_pow_left₀ (by positivity :
      0 ≤ 1+|v+2*Real.pi*(u-(if second then -t else t))|+height)
    (main_low_physical_signed_height (P := P) second v height t u hh) degree
  unfold mainLowQuantitativeFactor
  calc
    _ ≤ (Fintype.card RayFourExpansion.RayCharacter:ℝ)^2*(Cfirst*Z^εfirst*
      ((1/lowerFactor N a ap)*(Fintype.card (BufferIndex e):ℝ)*
        ((16*(Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*control^2*
          (2*(1+|v|+height+2*Real.pi*(|t|+|u|)))^degree*(Cbox*Z^εbox)*physical*
          Z^exponent/seedNorm))*(Cu*Z^εsecond)))) := by
      gcongr
    _=_ := by rw [Real.rpow_add hZ,Real.rpow_add hZ,Real.rpow_add hZ]; ring

end
end OAI.SevenEighths.Target830.Source.LowPhysical
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.main_low_physical_source_sum
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.actual_main_low_complete_physical_reindex

#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.actual_main_low_fixed_ray_physical_reindex
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.main_low_physical_fixed_ray_sum_le

#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.actual_main_low_physical_bins

#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.main_low_fixed_ray_sigma
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.main_low_physical_first_shell_reindex
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.main_low_physical_complete_ray_sum
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.main_low_physical_first_shell_payment

#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.actual_main_low_physical_ordinary_row_cost
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.actual_main_low_physical_original_row_cost

#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.main_low_original_label_row_injective
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.main_low_original_label_row_cost
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.actual_main_low_physical_full_original_row_cost

#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.eventual_actual_main_low_physical_first_shell_contraction

#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.main_low_physical_signed_height
#print axioms OAI.SevenEighths.Target830.Source.LowPhysical.main_low_physical_small_fee_bound
