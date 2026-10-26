/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainParameters
import Candidate.Uneven.MainLowPaidMain
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowFull
import Candidate.Uneven.MainPhysicalSelected
import Candidate.Cycle63.Physical.InitialMass.SecondLowSourceCaps
import Candidate.Cycle63.Physical.InitialMass.GeometryShiftedHeight
import Candidate.Cycle63.Physical.InitialMass.GeometryHighPayment
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl

set_option autoImplicit false
set_option maxHeartbeats 100000
namespace OAI.SevenEighths.MainPhysical
noncomputable section
open Sil.Uneven.MainSource
open OAI OAI.SevenEighths
open OAI.SevenEighths.MainLow
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
open Cycle63Moment
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

local notation "O" => HeckeFamily.O
local instance geometryMainLowFullDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

private theorem shared_squarefree_shells (P : Plane) {Label : Type*} [Fintype Label]
    (Ds : Label→Finset (Ideal O)) :
    selectedShells (sharedProjectors (fun l=>(Ds l).filter Squarefree))=
      selectedShells (sharedProjectors Ds) := by
  have hlive : live (sharedProjectors (fun l=>(Ds l).filter Squarefree))=
      live (sharedProjectors Ds) := by
    ext D
    simp only [mem_live,sharedProjectors,Finset.mem_biUnion,Finset.mem_univ,true_and,
      Finset.mem_filter]
    constructor
    · rintro ⟨⟨l,hl,_⟩,hm⟩
      exact ⟨⟨l,hl⟩,hm⟩
    · rintro ⟨⟨l,hl⟩,hm⟩
      exact ⟨⟨l,hl,squarefree_of_moebius_ne_zero D hm⟩,hm⟩
  exact congrArg (fun S=>S.image normKey) hlive

private theorem low_shared_shell_contraction (P : Plane) {Label : Type*} [Fintype Label]
    (Ds : Label→Finset (Ideal O))(hs : ∀l D,D∈Ds l→Squarefree D)
    (cost : Label→Ideal O→ℝ)(hc : ∀l D,0 ≤ cost l D)
    (factor εshell : ℝ)
    (hbound : ∀n∈selectedShells (sharedProjectors Ds),
      (∑l,∑D∈shell (sharedProjectors Ds) n,cost l D) ≤ 
        factor*(2*dyadicScale n)^(3*εshell)) :
    (∑l,∑D∈Ds l,cost l D) ≤ factor*
      (∑n∈selectedShells (sharedProjectors Ds),(2*dyadicScale n)^(3*εshell)) := by
  apply (shared_projector_shell_sum_le Ds hs cost hc).trans
  calc
    _ ≤ ∑n∈selectedShells (sharedProjectors Ds),factor*(2*dyadicScale n)^(3*εshell) :=
      Finset.sum_le_sum hbound
    _=_ := (Finset.mul_sum _ _ _).symm


theorem actual_geometry_low_second_source_caps (P : Plane)
    (reflected : Bool)(s : Input α)(R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ)(N : ℕ)(hZ : 1 < Z)(bin : ℤ×(Fin 5→ℤ))
    (j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j)
    (Ncap : ℕ)(hN : Fintype.card α ≤ Ncap)(Y : ℝ)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ) ≤ Y) :
    let datum:=geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j hw₁ hw₂ n
    Fintype.card datum.slots ≤ Ncap ∧
      (∀i I,I∈datum.input.pools i→(I.absNorm:ℝ) ≤ Y) := by
  intro datum
  constructor
  · apply le_trans _ hN
    change Fintype.card (liveIndices j.2.val) ≤ Fintype.card α
    simpa only [Fintype.card_coe] using Finset.card_le_univ (liveIndices j.2.val)
  · exact actual_child_pool_cap s _ R j.2 _ t Y hpool

attribute [local irreducible] geometryLowActualChain geometryLowActualGeometry geometryLowSecondDatum
attribute [-instance] geometryMainLowFullDecidable in
private theorem eventual_low_chain_source_caps (P : Plane) (N : ℕ) (window bs pad L : ℝ)
    (hwindow : 0 ≤ window) (hbs : 1 ≤ bs) (hpad : 0 < pad) (hL : 0 ≤ L) :
    ∀ᶠZ : ℝ in atTop,1 < Z ∧
      ∀{ι : Type}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι ≤ N → (∀i,logWindow (s.lo i) (s.hi i) ≤ window) →
      s.b₁ ≤ bs → s.b₂ ≤ bs →
      (∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j ≤ Z^L) →
      ∀(q : Chain s)(B₂ : actualAllocations q.first.pools q.E₂)(χ₂ : Character)(t₂ : ℝ),
      let src:=commonData (withHeight q.first χ₂ t₂) q.E₂ q.R₂ B₂
      src.toSource.allowance Z ≤ pad ∧
        ∀(D : Ideal O)(alloc : Allocation D (Finset.univ : Finset _))
          (side : Bool)(j : Fin 2),finalPlain src side D alloc j ≤ Z^L := by
  filter_upwards [eventual_two_common_low_source_caps N window bs pad L hwindow hbs hpad hL] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ s hcard hw hb₁ hb₂ hplain q B₂ χ₂ t₂
  exact hz.2 s hcard hw hb₁ hb₂ hplain q.C₁ q.R₁ q.B₁ q.η₁ q.t₁ q.E₂ q.R₂ B₂ χ₂ t₂

set_option linter.defProp false in
private def lowFullDynamicSpec (P : Plane) {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (_hA : 0 < A) (_hWs : Function.support W⊆Icc A B) (_hW : ContDiff ℝ ∞ W)
    (_hB : 0 ≤ B) (_ha : 0 < a) (_ha' : a ≤ 1/4) (_hb : 1 ≤ b)
    (_hBmask : 0 ≤ Bmask) (_hMcap : 0 < Mcap) (_hεold : 0 < εold)
    (_hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (_hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ P.incumbent)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (_hRw : 0 ≤ Rwidth) (_hdmax : 0 ≤ dmax) (_hτ : 0 < τ) (_hε : 0 < ε)
    (_he : 0 < e) (_he' : e < 1/1000) (_hκ : 0 < κ) (_hη : 0 ≤ η)
    (_hbudget : 8*e*Rwidth+κ ≤ ε) (_hmargin : 0 < margin)
    (_hd : 0 < d) (_hdsupply : Mcap+Bmask+margin ≤ d) (_hdm : d ≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (_hbs : 1 ≤ bs) (_hew : 0 < εwidth) (_hep : 0 < εpad) (_hmin : 0 < Mmin)
    (εshell : ℝ) (_heshell : 0 < εshell) (N : ℕ)(Cs : ℝ)(_hCs : 1 ≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(_hsupply : 0 < supply)(_hev : 0 < εv)
    (_hBnorm : 0 ≤ Bnorm)(_hel : 0 < εlabels)
    (degree : ℕ)(Sp : Finset (ℕ×ℕ))
    (η₀ : Character)(Q : Ideal O)(hQM : Q ≤ M)(Cg Z : ℝ) : Prop :=
    ∀(hZ : 1 < Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Fintype.card α ≤ N → (∀j,s.M j ≤ Cs) →
      supply ≤ s.lower → Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper ≤ bs → s.b₁=b → s.b₂=b →
      (∀j,0 ≤ w j) → (∀j,w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d ≤ Rwidth) → 0 ≤ mesh → (∀j,w j ≤ mesh) → (∀j,lo ≤ σ j) → (∀j,σ j ≤ hi) →
      0 ≤ height → (∀j,|freq j| ≤ height) → 51/100 ≤ aLow → aLow ≤ ((1+P.q)/2) →
      |v|+height+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2 ≤ (Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin ≤ Mrow → 0 ≤ omega → 0 ≤ ξ → Mrow+εwidth*Mrow+ξ/2 ≤ Mcap →
      ((17/500)*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j)) ≤ (1/25)*Mrow) →
      length Z s.X₁+length Z s.X₂+P.lambda*(∑j,Real.logb Z (s.P j)) ≤ P.B*Mrow →
    ∀{Label : Type}[Fintype Label],∀(reflected second : Bool)
      (first : Label→FirstSourceLabel)
      (_hf : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2)
      (_heq : ∀l,primeSupport (first l).1.1=primeSupport (first l).1.2)
      (Rfirst : Ideal O)
      (alloc : (l : Label)→actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χfirst : Label→Character)(tfirst : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let childSrc := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χfirst l) (tfirst l)
    ∀(R seed : Label→Ideal O)(K Tsec : Label→ℝ)(reserve : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(childSrc l).W₁ 0=0) → (∀l,(childSrc l).W₂ 0=0) →
    (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l) ≤ Z^Bnorm) →
    ∀(Tfirst p exponent : ℝ),1 ≤ Tfirst → p ≤ Bnorm →
    ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    Function.Injective (fun l=>(first l,seed l)) →
    (∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2) →
    (∀l,((first l).1.1.absNorm:ℝ) ≤ Z^Bnorm ∧ ((first l).1.2.absNorm:ℝ) ≤ Z^Bnorm) →
    (∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ) ≤ Z^p) →
    (∀l,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l) ≤ exponent) →
    (∀l,Tfirst ≤ ((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ) < 2*Tfirst) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (childSrc l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
      (box : Finset (Fin 4→ℤ)),
    (∀r∈rows,actualSecondDyad (childSrc r.1) (R r.1) (seed r.1)
      (K r.1) (Tsec r.1) Z ξ r.2∈box) →
    let label := fun r : rows=>actualSecondSupportedLabel (childSrc r.val.1)
      (R r.val.1) (seed r.val.1) (K r.val.1) (Tsec r.val.1) Z ξ r.val.2 (hU r.val r.property)
    let cell := widthCellUpper ((∑j,Real.logb Z (s.P j))/Mrow)
    let amp := Mrow*Sil.Uneven.MainSource.amp P cell
    ∀q : rows→Chain s,
    ∀g : (r : rows)→LiveMainGeometry s (q r) Z Mrow amp omega ξ bs (Fintype.card α),
    (∀r,(q r).C₁=(if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)) →
    (∀r,(g r).D₁=(if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)) →
    (∀r,(g r).datum.C=(label r).1.1) → (∀r,(g r).datum.D=(label r).1.2) →
    (∀r,HEq (g r).datum.inactive (label r).2.val) →
    (∀r,(q r).E₂=(if second then (label r).1.2 else (label r).1.1)) →
    (∀r,(g r).datum.K=firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)) →
    omega=frequencyLoss Z 32 ξ+reserve →
    ∀(χ : rows→RayFourExpansion.RayCharacter)(hP : ∀r,(q r).R₂*(q r).E₂≠0)
      (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ) ≤ Z^Bmask),
    let st := fun r=>retainedState Z Bmask hZ ((g r).datum.τ (χ r)) (internalQ Q η₀)
      ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
    let src := fun r=>withHeight (q r).first ((g r).datum.τ (χ r)) v
    ∀(divisorSeed : rows→Ideal O)(hE₂ : ∀r,Supported (q r).E₂),(∀r,divisorSeed r∣(q r).E₂) →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ),1 ≤ T →
      (∀D∈Ds,Squarefree D ∧ T ≤ (D.absNorm:ℝ) ∧ (D.absNorm:ℝ) < 2*T) →
    ∀p₀ : Profiles a b,s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      (commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.allowance Z ≤ pad) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      ∀D∈Ds,∀al∈(commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.active D,∀side : Bool,
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 0 ≤ Z^L ∧
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 1 ≤ Z^L) →
    let low := fun r=>ActualLow M H hH (st r) η₀ (inf_le_left.trans hQM) inf_le_right
      aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : rows→Finset O)(weight : rows→O→ℝ),(∀r,∀z∈zs r,0 ≤ weight r z) →
      (∀r,∀z∈zs r,(st r).radial.keep z ∧ low r z) →
      (∀r,∀z∈zs r,weight r z ≤ ((st r).radial.profile (‖eisEmbedding z‖^2/(st r).radial.scale)).re) →
    ∀(mass : Label→ℝ)(physical loss : ℝ),0 ≤ physical → (∀l,0 ≤ mass l) →
      (∀l,mass l ≤ physical*Z^loss) →
    let c := fun r=>mass r.val.1/volume (childSrc r.val.1)*
      (g r).datum.K*normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
    let error := εwidth*Mrow+ξ/2-Mrow*lowReserve+εold+2*ε*d*(Fintype.card α:ℝ)+
      (P.q/(6*(incumbentKappa P)))*(omega+εpad*Mrow)+P.q*mesh+pad
    (∑r,c r*(∑D∈Ds,∑z∈zs r,weight r z*
      ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2)) ≤ 
      Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(2*T)^(3*εshell)*(box.card:ℝ)*physical*
        Z^(loss+amp+p+exponent+error+εv+Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ)

set_option linter.defProp false in
private def lowFullSpec (P : Plane) {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (ha : 0 < a) (ha' : a ≤ 1/4) (hb : 1 ≤ b)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ P.incumbent)
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
    (degree : ℕ)(Sp : Finset (ℕ×ℕ)) : Prop :=
    ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q ≤ M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0 < Cg ∧ ∀ᶠZ : ℝ in atTop,2 ≤ Z ∧
    lowFullDynamicSpec (P := P) (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta hκbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel degree Sp η₀ Q hQM Cg Z

set_option linter.defProp false in
private def lowFullKernel (P : Plane) {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (ha : 0 < a) (ha' : a ≤ 1/4) (hb : 1 ≤ b)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ P.incumbent)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0 ≤ Rwidth) (hdmax : 0 ≤ dmax) (hτ : 0 < τ) (hε : 0 < ε)
    (he : 0 < e) (he' : e < 1/1000) (hκ : 0 < κ) (hη : 0 ≤ η)
    (hbudget : 8*e*Rwidth+κ ≤ ε) (hmargin : 0 < margin)
    (hd : 0 < d) (hdsupply : Mcap+Bmask+margin ≤ d) (hdm : d ≤ dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1 ≤ bs) (hew : 0 < εwidth) (hep : 0 < εpad) (hmin : 0 < Mmin)
    (εshell : ℝ) (heshell : 0 < εshell) (N : ℕ)(Cs : ℝ)(hCs : 1 ≤ Cs)
    (supply εv Bnorm εlabels : ℝ)(hsupply : 0 < supply)(hev : 0 < εv)
    (hBnorm : 0 ≤ Bnorm)(hel : 0 < εlabels) :
    Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),PLift (lowFullSpec (P := P) (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta hκbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel degree Sp)
 :=
  let hbase := actual_selected_low_paid_columns (P := P) (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta hκbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
    supply εv Bnorm εlabels hsupply hev hBnorm hel
  let degree:=Classical.choose hbase
  let hd:=Classical.choose_spec hbase
  let Sp:=Classical.choose hd
  let hcolumn:=Classical.choose_spec hd
  ⟨degree,Sp,PLift.up hcolumn⟩

attribute [local irreducible] lowFullKernel

private def lowFullScalarFactor (P : Plane)
    (Cg b Cs control v height physical Z exponent seedNorm : ℝ)
    (N degree boxCard : ℕ) : ℝ :=
  Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*control^2*
    (1+|v|+height)^degree*(boxCard:ℝ)*physical*Z^exponent/seedNorm

private theorem lowFullScalarFactor_nonneg (P : Plane)
    (Cg b Cs control v height physical Z exponent seedNorm : ℝ)
    (N degree boxCard : ℕ)
    (hCg : 0 ≤ Cg)(hCs : 0 ≤ Cs)(hheight : 0 ≤ height)(hphysical : 0 ≤ physical)
    (hZ : 0 < Z)(hseed : 0 ≤ seedNorm) :
    0 ≤ lowFullScalarFactor (P := P) Cg b Cs control v height physical Z exponent seedNorm N degree boxCard := by
  have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
  unfold lowFullScalarFactor
  positivity

set_option maxHeartbeats 200000 in
set_option linter.unusedVariables false in
set_option linter.defProp false in
private def lowFullLiteralSpec (P : Plane) {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (ha : 0 < a) (ha' : a ≤ 1/4) (hb : 1 ≤ b)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ P.incumbent)
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
    (η₀ : Character)(Q : Ideal O)(hQM : Q ≤ M)(Z : ℝ) : Prop :=
  ∀(hZ : 1 < Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
        (heightV height mesh aLow : ℝ)(i : ℕ)
        (hcard : Fintype.card α ≤ N)(hmass : ∀j,s.M j ≤ Cs)(hsupply' : supply ≤ s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)(hsη : s.η=ηseed)
        (hsupper : s.upper ≤ bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0 ≤ w j)(hwL : ∀j,w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold)
        (hwr : ∀j,w j/d ≤ Rwidth)(hmesh : 0 ≤ mesh)(hwm : ∀j,w j ≤ mesh)
        (hσlo : ∀j,lo ≤ σ j)(hσhi : ∀j,σ j ≤ hi)(hheight : 0 ≤ height)(hfreq : ∀j,|freq j| ≤ height)
        (haLow : 51/100 ≤ aLow)(haLow' : aLow ≤ ((1+P.q)/2))
        (hfreqbin : |heightV|+height+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ)
        (hhigh : (3+(3*i+2:ℕ)*Z^τ)^2 ≤ (Z^d)^η)
        (Mrow reserve ξ : ℝ)(hMmin : Mmin ≤ Mrow)
        (hω : 0 ≤ frequencyLoss Z 32 ξ+reserve)(hξ : 0 ≤ ξ)
        (hMcap' : Mrow+εwidth*Mrow+ξ/2 ≤ Mcap)
        (hzslot : (17/500)*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j)) ≤ (1/25)*Mrow)
        (haff : length Z s.X₁+length Z s.X₂+P.lambda*(∑j,Real.logb Z (s.P j)) ≤ 
          P.B*Mrow)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
        (firstIndex : Label→GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin),
        let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let cell:=widthCellUpper ((∑j,Real.logb Z (s.P j))/Mrow)
        let amp:=Mrow*Sil.Uneven.MainSource.amp P cell
        let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let seed:=fun l=>(firstIndex l).1.val.2.1.val
        let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
        let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
          (Fintype.card α) (first l)
        ∀(hf : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2)
          (heq : ∀l,primeSupport (first l).1.1=primeSupport (first l).1.2)
          (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l) ≤ Z^Bnorm)
          (Tfirst p exponent : ℝ)(hTfirst : 1 ≤ Tfirst)(hp : p ≤ Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (hfirstseed : ∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2)
          (hfirstnorm : ∀l,((first l).1.1.absNorm:ℝ) ≤ Z^Bnorm ∧ ((first l).1.2.absNorm:ℝ) ≤ Z^Bnorm)
          (hrad : ∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ) ≤ Z^p)
          (hgeom : ∀l,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l) ≤ exponent)
          (hfirstshell : ∀l,Tfirst ≤ ((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ) < 2*Tfirst)
          (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
          (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
          (box : Finset (Fin 4→ℤ))
          (hbox : ∀r∈rows,actualSecondDyad (childSrc r.1) (Rchild r.1) (seed r.1)
            (K r.1) (Tsec r.1) Z ξ r.2∈box),
        let datum : rows→SecondInputDatum α:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
        ∀(B₂ : (r : rows)→actualAllocations (childSrc r.val.1).pools
            (if second then (datum r).D else (datum r).C))
          (rwitness : (r : rows)→secondLiveRows (fun _:Unit=>(datum r).block))
          (hf₂ : ∀r,frozenCoefficient (B₂ r).val
            (if second then (datum r).D else (datum r).C) (datum r).R
            (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0),
        let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
        let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          (rwitness r) (hf₁ r.val.1) (hf₂ r)
        ∀(χ : rows→RayFourExpansion.RayCharacter)
          (hP : ∀r,(q r).R₂*(q r).E₂≠0)
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ) ≤ Z^Bmask),
        let st:=fun r=>retainedState Z Bmask hZ ((g r).datum.τ (χ r)) (internalQ Q η₀)
          ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
        let low:=fun r=>ActualLow M H hH (st r) η₀ (inf_le_left.trans hQM) inf_le_right
          aLow e (3*(i+1:ℕ)*Z^τ)
        ∀(divisorSeed : rows→Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ℂ))
          (zs : rows→Finset O)(weight : rows→O→ℝ)
          (hnonneg : ∀r,∀z∈zs r,0 ≤ weight r z)
          (hkeep : ∀r,∀z∈zs r,(st r).radial.keep z ∧ low r z)
          (hweight : ∀r,∀z∈zs r,weight r z ≤ 
            ((st r).radial.profile (‖eisEmbedding z‖^2/(st r).radial.scale)).re)
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s ≤ Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ap ≤ x)(hplain₂ : ∀x,s.W₂ x≠0→ap ≤ x)
          (sideLower : ℝ)
          (hside : ∀l,sideLower ≤ geometryHighSide reflected (Real.logb Z (volume s))
            (geometryExponents s R seed₀ (Z^Mrow) Z ξ (firstIndex l).1.val.1.val))
          (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ) ≤ Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j) ≤ window)
          (hplainScale : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j ≤ Z^L),
        let src:=fun r=>withHeight (q r).first ((g r).datum.τ (χ r)) heightV
        let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
        let unionDs:=sharedProjectors Ds
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*Mrow+ξ/2-Mrow*lowReserve+εold+2*ε*d*(Fintype.card α:ℝ)+
          (P.q/(6*(incumbentKappa P)))*(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)+P.q*mesh+pad
        let exponentFull:=(Bmass*εmass-sideLower)+amp+p+exponent+error+εv+Bnorm*εshell+εlabels
        let factor : ℝ:=lowFullScalarFactor (P := P) Cg b Cs (p₀.control Sp) heightV height physical Z
          exponentFull (seed₀.absNorm:ℝ) N degree box.card
        let cost:=fun (r : rows)(D : Ideal O)=>
          (firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
            normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive)*
          (∑z∈zs r,weight r z*‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2)
        (∑r,∑D∈Ds r,cost r D) ≤ 
          factor*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell))

set_option maxHeartbeats 80000 in
set_option linter.defProp false in
def actual_geometry_selected_low_full_columns (P : Plane) {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0 < A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0 ≤ B) (ha : 0 < a) (ha' : a ≤ 1/4) (hb : 1 ≤ b)
    (hBmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hεold : 0 < εold)
    (hbeta : 51/100 ≤ HeckeZeroSupremum.beta)
    (hκbeta : 2*HeckeZeroSupremum.beta-1 ≤ P.incumbent)
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
    (window pad : ℝ)(hwindow : 0 ≤ window)(hpad : 0 < pad)(hL0 : 0 ≤ L) :
    Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,
      PLift (0 < Cu) ×
      (∀(η₀ : Character)(Q : Ideal O)(hQM : Q ≤ M),
        internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀ ≤ Ideal.span {(72:O)} →
        ΣCg : ℝ,PLift (0 < Cg ∧ ∀ᶠZ : ℝ in atTop,2 ≤ Z ∧
          lowFullLiteralSpec (P := P) (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta hκbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      degree Sp Cg Cu η₀ Q hQM Z)) :=
by
  exact
    let kernel := lowFullKernel (P := P) (α:=α) M H hH
      W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta hκbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel
    let degree:=kernel.1
    let Sp:=kernel.2.1
    let unionBase:=actual_second_low_weighted_shells.{0,0} (α:=α) N U εshell εunion hUcap heshell.le heunion
    let Cu:=Classical.choose unionBase
    let hu:=Classical.choose_spec unionBase
    let sourceCaps:=eventual_low_chain_source_caps (P := P) N window b pad L hwindow hb hpad hL0
    ⟨degree,Sp,Cu,⟨PLift.up hu.1,fun (η₀ : Character)(Q : Ideal O)(hQM : Q ≤ M)
        (hQ0 : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
        (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)})=>
      let hcbase:=kernel.2.2.down η₀ Q hQM hQ0 hQt hQ72
      let Cg:=Classical.choose hcbase
      let hc:=Classical.choose_spec hcbase
      ⟨Cg,PLift.up (And.intro hc.1 (show ∀ᶠZ : ℝ in atTop,2 ≤ Z ∧
        lowFullLiteralSpec (P := P) (α:=α) M H hH
        W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta hκbeta
        Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
        ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
        supply εv Bnorm εlabels hsupply hev hBnorm hel
        ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
        degree Sp Cg Cu η₀ Q hQM Z from by
        filter_upwards [hc.2,hu.2,sourceCaps] with Z hz hzu hzsource
        refine ⟨hz.1,?_⟩
        exact fun (hZ : 1 < Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
          (heightV height mesh aLow : ℝ)(i : ℕ)
          (hcard : Fintype.card α ≤ N)(hmass : ∀j,s.M j ≤ Cs)(hsupply' : supply ≤ s.lower)
          (hm : Matches M H hH s η₀ θ w σ freq W B Z)(hsη : s.η=ηseed)
          (hsupper : s.upper ≤ bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
          (hw : ∀j,0 ≤ w j)(hwL : ∀j,w j ≤ Cycle25.Energy.commonMesh Mcap Bmask L εold)
          (hwr : ∀j,w j/d ≤ Rwidth)(hmesh : 0 ≤ mesh)(hwm : ∀j,w j ≤ mesh)
          (hσlo : ∀j,lo ≤ σ j)(hσhi : ∀j,σ j ≤ hi)(hheight : 0 ≤ height)(hfreq : ∀j,|freq j| ≤ height)
          (haLow : 51/100 ≤ aLow)(haLow' : aLow ≤ ((1+P.q)/2))
          (hfreqbin : |heightV|+height+Z^τ/2 ≤ (3*i+2:ℕ)*Z^τ)
          (hhigh : (3+(3*i+2:ℕ)*Z^τ)^2 ≤ (Z^d)^η)
          (Mrow reserve ξ : ℝ)(hMmin : Mmin ≤ Mrow)
          (hω : 0 ≤ frequencyLoss Z 32 ξ+reserve)(hξ : 0 ≤ ξ)
          (hMcap' : Mrow+εwidth*Mrow+ξ/2 ≤ Mcap)
          (hzslot : (17/500)*Mrow ≤ ∑j,Real.logb Z (s.P j) ∧
            (∑j,Real.logb Z (s.P j)) ≤ (1/25)*Mrow)
          (haff : length Z s.X₁+length Z s.X₂+P.lambda*(∑j,Real.logb Z (s.P j)) ≤ 
            P.B*Mrow)
          {Label : Type}[Fintype Label]
          (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
          (firstIndex : Label→GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)=>
          let first:=fun l=>geometryFirstLabel s R seed₀ (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
          let cell:=widthCellUpper ((∑j,Real.logb Z (s.P j))/Mrow)
          let amp:=Mrow*Sil.Uneven.MainSource.amp P cell
          let childSrc:=fun l=>geometryLowFirstChild reflected s R seed₀ (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
          let Rchild:=fun l=>R*geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
          let seed:=fun l=>(firstIndex l).1.val.2.1.val
          let K:=fun l=>firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first l)
          let Tsec:=fun l=>firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
            (Fintype.card α) (first l)
          fun (hf : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2)
            (heq : ∀l,primeSupport (first l).1.1=primeSupport (first l).1.2)
            (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
              (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
                (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
              R s.ν s.W s.P≠0)
            (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
            (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l) ≤ Z^Bnorm)
            (Tfirst p exponent : ℝ)(hTfirst : 1 ≤ Tfirst)(hp : p ≤ Bnorm)
            (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
            (hinj : Function.Injective (fun l=>(first l,seed l)))
            (hfirstseed : ∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2)
            (hfirstnorm : ∀l,((first l).1.1.absNorm:ℝ) ≤ Z^Bnorm ∧ ((first l).1.2.absNorm:ℝ) ≤ Z^Bnorm)
            (hrad : ∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ) ≤ Z^p)
            (hgeom : ∀l,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l) ≤ exponent)
            (hfirstshell : ∀l,Tfirst ≤ ((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ) < 2*Tfirst)
            (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
            (hU : ∀r∈rows,r.2.2.1∈inactiveSubsets r.2.1.val.val.1 r.2.1.val.val.2)
            (box : Finset (Fin 4→ℤ))
            (hbox : ∀r∈rows,actualSecondDyad (childSrc r.1) (Rchild r.1) (seed r.1)
              (K r.1) (Tsec r.1) Z ξ r.2∈box)=>
          let datum : rows→SecondInputDatum α:=fun r : rows=>geometryLowSecondDatum reflected s R seed₀ Z Mrow amp ξ reserve bs t
            (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2
          fun (B₂ : (r : rows)→actualAllocations (childSrc r.val.1).pools
              (if second then (datum r).D else (datum r).C))
            (rwitness : (r : rows)→secondLiveRows (fun _:Unit=>(datum r).block))
            (hf₂ : ∀r,frozenCoefficient (B₂ r).val
              (if second then (datum r).D else (datum r).C) (datum r).R
              (childSrc r.val.1).ν (childSrc r.val.1).W (childSrc r.val.1).P≠0)=>
          let q:=fun r : rows=>geometryLowActualChain reflected s R seed₀ Z Mrow amp ξ reserve bs t
            (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
          let g:=fun r : rows=>geometryLowActualGeometry reflected s R seed₀ Z Mrow amp ξ reserve bs t
            (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 second (B₂ r)
            (rwitness r) (hf₁ r.val.1) (hf₂ r)
          let fields:=fun r : rows=>actual_geometry_low_paid_fields (P := P) reflected s R seed₀ Z Mrow amp ξ reserve bs t
            (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 (hU r.val r.property)
            second (B₂ r) (rwitness r) (hf₁ r.val.1) (hf₂ r)
          let hrow:=hz.2 hZ s θ w σ freq heightV height mesh aLow i hcard hmass hsupply' hm hsη hsupper hsb₁ hsb₂
            hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
            Mrow (frequencyLoss Z 32 ξ+reserve) ξ hMmin hω hξ hMcap' hzslot haff
            reflected second first hf heq R (fun l=>(firstIndex l).2)
            (fun l=>geometryColumnCharacter reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            (fun _=>t) hf₁ Rchild seed K Tsec reserve
            (fun l=>actual_first_live_squarefree
              (geometryFirstSource s R seed₀ (Z^Mrow) Z ξ
                (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
              (fun _=>logAnnulus) (firstIndex l).1.val (firstIndex l).1.property)
            (fun _=>hw₁) (fun _=>hw₂) hsource Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0 hinj hfirstseed
            hfirstnorm hrad hgeom hfirstshell rows hU box hbox q g
            (fun r=>(fields r).1) (fun r=>(fields r).2.1) (fun r=>(fields r).2.2.1)
            (fun r=>(fields r).2.2.2.1) (fun r=>(fields r).2.2.2.2.1)
            (fun r=>(fields r).2.2.2.2.2.1) (fun r=>(fields r).2.2.2.2.2.2) rfl
          fun (χ : rows→RayFourExpansion.RayCharacter) hP hPN divisorSeed hE₂ hdivisor (p₀ : Profiles a b) hp₁ hp₂
            (zs : rows→Finset O)(weight : rows→O→ℝ)
            (hnonneg : ∀r,∀z∈zs r,0 ≤ weight r z) hkeep hweight
            (Ψ : 𝓢(ℝ,ℂ)) hsourceOriginal hplain₁ hplain₂
            (sideLower : ℝ)
            (hside : ∀l,sideLower ≤ geometryHighSide reflected (Real.logb Z (volume s))
              (geometryExponents s R seed₀ (Z^Mrow) Z ξ (firstIndex l).1.val.1.val))
            (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ) ≤ Z^U)
            (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j) ≤ window)
            (hplainScale : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j ≤ Z^L)=>
          let src:=fun r=>withHeight (q r).first ((g r).datum.τ (χ r)) heightV
          let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
          let unionDs:=sharedProjectors Ds
          let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
          let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
          let error:=εwidth*Mrow+ξ/2-Mrow*lowReserve+εold+2*ε*d*(Fintype.card α:ℝ)+
            (P.q/(6*(incumbentKappa P)))*(frequencyLoss Z 32 ξ+reserve+εpad*Mrow)+P.q*mesh+pad
          let exponentFull:=(Bmass*εmass-sideLower)+amp+p+exponent+error+εv+Bnorm*εshell+εlabels
          let factor : ℝ:=lowFullScalarFactor (P := P) Cg b Cs (p₀.control Sp) heightV height physical Z
            exponentFull (seed₀.absNorm:ℝ) N degree box.card
          let cost:=fun (r : rows)(D : Ideal O)=>
            (firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
              normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive)*
            (∑z∈zs r,weight r z*‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2)
          let hcommonCaps:=fun (r : rows)(B : actualAllocations (q r).first.pools (q r).E₂)=>
            hzsource.2 s hcard hwindowSource hsb₁.le hsb₂.le hplainScale
              (q r) B ((g r).datum.τ (χ r)) heightV
          (show (∑r,∑D∈Ds r,cost r D) ≤ 
            factor*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)) from by
            have hphysical : 0 ≤ physical := by
              cases reflected <;> simp only [physical,geometryHighFactor,ite_true]
              · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (geometryDCompensator_pos bin).le
              · exact (inv_pos.mpr (geometryDCompensator_pos bin)).le
            have hCg : 0 < Cg := hc.1
            have hfirstMass (l : Label) : 0 ≤ firstMass l :=
              geometry_first_high_mass_nonneg reflected s R seed₀ Ψ Mrow Z ξ εmass
                (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
            have hmassBound (l : Label) : firstMass l ≤ physical*Z^(Bmass*εmass-sideLower) :=
              actual_geometry_low_uniform_mass (P := P) reflected N supply ap hsupply hap s R seed₀ Ψ
                Mrow Z ξ Bmass εmass sideLower hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hemass
                hcard hsupply' hs₀ hw₁ hw₂ hsourceOriginal hplain₁ hplain₂ bin (firstIndex l).1.val (hside l)
            have hfactor : 0 ≤ factor :=
              lowFullScalarFactor_nonneg (P := P) Cg b Cs (p₀.control Sp) heightV height physical Z
                exponentFull (seed₀.absNorm:ℝ) N degree box.card hCg.le
                (zero_le_one.trans hCs) hheight hphysical (zero_lt_one.trans hZ) (Nat.cast_nonneg _)
            have hcost (r : rows)(D : Ideal O) : 0 ≤ cost r D := by
              dsimp only [cost]
              apply mul_nonneg
              · exact mul_nonneg (mul_nonneg (div_nonneg
                  (geometry_first_high_mass_nonneg reflected s R seed₀ Ψ Mrow Z ξ εmass
                    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex r.val.1).1.val)
                  (CenteredMomentAmplificationChildInput.volume_pos _).le) (g r).datum.K_pos.le)
                  (normalizer_pos _ _ (g r).datum.hC _).le
              · exact Finset.sum_nonneg (fun z hz=>mul_nonneg (hnonneg r z hz) (sq_nonneg _))
            have hs (r : rows)(D : Ideal O)(hD : D∈Ds r) : Squarefree D := (Finset.mem_filter.mp hD).2
            have hsourcecap (r : rows):=
              actual_geometry_low_second_source_caps (P := P) reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 N hcard (Z^U) hpool
            have hcap (r : rows)(D : Ideal O)(hD : D∈Ds r) : (D.absNorm:ℝ) ≤ Z^(((N:ℝ)+2)*U) :=
              (second_datum_projector_cap (datum r) N Z U (hsourcecap r).1 hZ.le hUcap
                (hsourcecap r).2 D (Finset.mem_filter.mp hD).1).2
            have hshell (n : ℤ)(hn : n∈selectedShells unionDs) :
                (∑r,∑D∈shell unionDs n,cost r D) ≤ factor*(2*dyadicScale n)^(3*εshell) := by
              have hscale:=shared_projector_shell_scale Ds Z (((N:ℝ)+2)*U) hcap n hn
              have hcolumns:=hrow χ hP hPN divisorSeed hE₂ hdivisor (shell unionDs n) (dyadicScale n) pad
                hscale.1 (fun D hD=>let h:=shared_projector_shell_gates Ds n D hD; ⟨h.1,h.2.2⟩)
                p₀ hp₁ hp₂ (fun r B hB=>(hcommonCaps r B).1)
                (fun r B hB D hD al hal side=>⟨(hcommonCaps r B).2 D al side 0,(hcommonCaps r B).2 D al side 1⟩)
                zs weight hnonneg hkeep hweight firstMass physical (Bmass*εmass-sideLower)
                hphysical hfirstMass hmassBound
              convert hcolumns using 1
              · apply Finset.sum_congr rfl
                intro r hr
                dsimp only [cost]
                rw [Finset.mul_sum]
                dsimp only [src,childSrc,geometryLowFirstChild,first,geometryColumnIdeal,geometryFirstLabel]
                rfl
              · dsimp only [factor,lowFullScalarFactor,exponentFull,error]
                ring
            have hfull:=low_shared_shell_contraction (P := P) Ds hs cost hcost factor εshell hshell
            apply hfull.trans
            apply mul_le_mul_of_nonneg_left _ hfactor
            have hdatum:=hzu.2 datum (fun r=>(hsourcecap r).1) (fun r=>(hsourcecap r).2)
            simpa only [Ds,shared_squarefree_shells (P := P)] using hdatum)
        ))⟩⟩⟩

end
end OAI.SevenEighths.MainPhysical
