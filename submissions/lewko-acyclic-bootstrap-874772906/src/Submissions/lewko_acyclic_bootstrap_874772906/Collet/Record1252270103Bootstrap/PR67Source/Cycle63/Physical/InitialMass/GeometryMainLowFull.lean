import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainLowSelected
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildSelected
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.SecondLowSourceCaps
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle25.Energy.Endpoint
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
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
open Cycle63Moment
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal HeckeFamily.O) [NeZero M]
variable (H : Subgroup (HeckeFamily.O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

local instance geometryMainLowFullDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

private theorem shared_squarefree_shells {Label : Type*} [Fintype Label]
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

private theorem low_shared_shell_contraction {Label : Type*} [Fintype Label]
    (Ds : Label→Finset (Ideal O))(hs : ∀l D,D∈Ds l→Squarefree D)
    (cost : Label→ Ideal O→ℝ)(hc : ∀l D,0≤ cost l D)
    (factor εshell : ℝ)
    (hbound : ∀n∈selectedShells (sharedProjectors Ds),
      (∑l,∑D∈shell (sharedProjectors Ds) n,cost l D)≤
        factor*(2*dyadicScale n)^(3*εshell)) :
    (∑l,∑D∈Ds l,cost l D)≤factor*
      (∑n∈selectedShells (sharedProjectors Ds),(2*dyadicScale n)^(3*εshell)) := by
  apply (shared_projector_shell_sum_le Ds hs cost hc).trans
  calc
    _≤∑n∈selectedShells (sharedProjectors Ds),factor*(2*dyadicScale n)^(3*εshell) :=
      Finset.sum_le_sum hbound
    _=_ := (Finset.mul_sum _ _ _).symm

theorem actual_geometry_low_second_source_caps
    (reflected : Bool)(s : Input α)(R seed : Ideal O)
    (Z Mrow amp ξ reserve b t : ℝ)(N : ℕ)(hZ : 1<Z)(bin : ℤ×(Fin 5→ℤ))
    (j : GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
    (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
    (n : GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j)
    (Ncap : ℕ)(hN : Fintype.card α≤Ncap)(Y : ℝ)
    (hpool : ∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Y) :
    let datum:=geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve b t N hZ bin j hw₁ hw₂ n
    Fintype.card datum.slots≤Ncap ∧
      (∀i I,I∈datum.input.pools i→(I.absNorm:ℝ)≤Y) := by
  intro datum
  constructor
  · apply le_trans _ hN
    change Fintype.card (liveIndices j.2.val)≤Fintype.card α
    simpa only [Fintype.card_coe] using Finset.card_le_univ (liveIndices j.2.val)
  · exact actual_child_pool_cap s _ R j.2 _ t Y hpool

attribute [local irreducible] geometryLowActualChain geometryLowActualGeometry geometryLowSecondDatum
attribute [-instance] geometryMainLowFullDecidable in
private theorem eventual_low_chain_source_caps (N : ℕ) (window bs pad L : ℝ)
    (hwindow : 0≤window) (hbs : 1≤bs) (hpad : 0<pad) (hL : 0≤L) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι][DecidableEq ι](s : Input ι),
      Fintype.card ι≤N → (∀i,logWindow (s.lo i) (s.hi i)≤window) →
      s.b₁≤bs → s.b₂≤bs →
      (∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j≤Z^L) →
      ∀(q : Chain s)(B₂ : actualAllocations q.first.pools q.E₂)(χ₂ : Character)(t₂ : ℝ),
      let src:=commonData (withHeight q.first χ₂ t₂) q.E₂ q.R₂ B₂
      src.toSource.allowance Z≤pad ∧
        ∀(D : Ideal O)(alloc : Allocation D (Finset.univ : Finset _))
          (side : Bool)(j : Fin 2),finalPlain src side D alloc j≤Z^L := by
  filter_upwards [eventual_two_common_low_source_caps N window bs pad L hwindow hbs hpad hL] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ _ s hcard hw hb₁ hb₂ hplain q B₂ χ₂ t₂
  exact hz.2 s hcard hw hb₁ hb₂ hplain q.C₁ q.R₁ q.B₁ q.η₁ q.t₁ q.E₂ q.R₂ B₂ χ₂ t₂

variable [Cycle63.AffineLedger] in
set_option linter.unusedVariables false in
set_option linter.defProp false in
/-- The selected low frequency columns of the final daughters of the LOW children of a step are paid for every choice
of the parameters: the statement `LowSelectedStmt` of the row, closed over its parameters. -/
def LowSelectedPaidColumns (Adm : ℝ→ℝ→ℝ→Prop) (labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ)
    (Presented : (Bmask : ℝ) → Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop) : Prop :=
  ∀(M : Ideal HeckeFamily.O)[NeZero M](H : Subgroup (HeckeFamily.O⧸M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H){α : Type}[Fintype α][DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hLslot : Lslot≤Cycle25.Energy.commonMesh Mcap Bmask L εold)
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
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels),
    LowSelectedStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell N Cs
      supply εv Bnorm εlabels Adm labelExp (Presented Bmask)

variable [Cycle63.AffineLedger] in
/-- The first-level row 5: the complete selected low frequency columns are paid by the finite supported label budget of
the old region, for all units and without presentation of the children. -/
theorem actual_selected_low_paid_columns_closed [Cycle63.AffineLedger.DeletesIntoOldRegion] :
    LowSelectedPaidColumns (fun _ _ _ => True) lowGeometryExponent (fun _ _ _ _ _ _ => True) := by
  intro M _ H hH α _ _ W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hLslot hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs supply εv Bnorm εlabels hsupply hev hBnorm hel
  exact lowSelectedStmt_of_row5 (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hLslot hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel (fun _ _ _ _ _ => True)

variable [Cycle63.AffineLedger] in
set_option linter.defProp false in
private def lowFullKernel {Adm : ℝ→ℝ→ℝ→Prop} {labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ}
    {Presented : (Bmask : ℝ) → Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop}
    {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell : ℝ) (N : ℕ)
    (Cs supply εv Bnorm εlabels : ℝ)
    (hrow5 : LowSelectedStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin
      εshell N Cs supply εv Bnorm εlabels Adm labelExp (Presented Bmask))
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)(hQ0 : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)}) :
    Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCg : ℝ,PLift (0<Cg ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
      LowSelectedBody (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell N Cs
        supply εv Bnorm εlabels Adm labelExp (Presented Bmask) degree Sp η₀ Q hQM Cg Z) :=
  let hbase := hrow5 η₀ Q hQM hQ0 hQt hQ72
  let degree:=Classical.choose hbase
  let hd:=Classical.choose_spec hbase
  let Sp:=Classical.choose hd
  let hs:=Classical.choose_spec hd
  let Cg:=Classical.choose hs
  ⟨degree,Sp,Cg,PLift.up (Classical.choose_spec hs)⟩

attribute [local irreducible] lowFullKernel


def mainLowQuantitativeFactor
    (Cg b Cs control v height physical Z exponent seedNorm : ℝ)
    (N degree boxCard : ℕ) : ℝ :=
  Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*control^2*
    (1+|v|+height)^degree*(boxCard:ℝ)*physical*Z^exponent/seedNorm

theorem mainLowQuantitativeFactor_nonneg
    (Cg b Cs control v height physical Z exponent seedNorm : ℝ)
    (N degree boxCard : ℕ)
    (hCg : 0≤Cg)(hCs : 0≤Cs)(hheight : 0≤height)(hphysical : 0≤physical)
    (hZ : 0<Z)(hseed : 0≤ seedNorm) :
    0≤ mainLowQuantitativeFactor Cg b Cs control v height physical Z exponent seedNorm N degree boxCard := by
  have hd:=QuadraticInitialBound.diagonalControl_nonneg ballProfile
  unfold mainLowQuantitativeFactor
  positivity

variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 200000 in
set_option linter.unusedVariables false in
set_option linter.defProp false in
/-- The complete selected low frequency columns of a child source, with the shared second-projector shells and the
source caps of its children, for the per-label exponent `labelExp` of the first labels. -/
def lowFullLiteralSpec {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
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
    (Adm : ℝ→ℝ→ℝ→Prop)(labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (ap εmass Bmass : ℝ)(hap : 0<ap)(hemass : 0≤εmass)
    (U εunion : ℝ)(hUcap : 0≤U)(heunion : 0<εunion)
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L)
    (degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)(Z : ℝ) : Prop :=
  ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
        (heightV height mesh aLow : ℝ)(i : ℕ)
        (hcard : Fintype.card α≤N)(hmass : ∀j,s.M j≤Cs)(hsupply' : supply≤ s.lower)
        (hm : Matches M H hH s η₀ θ w σ freq W B Z)
        (hsupper : s.upper≤bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
        (hw : ∀j,0≤w j)(hwL : ∀j,w j≤Lslot)
        (hwr : ∀j,w j/d≤Rwidth)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
        (hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤hi)(hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)
        (haLow : 51/100≤aLow)(haLow' : aLow≤((1+Cycle63.AffineLedger.q)/2))
        (hfreqbin : |heightV|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ)
        (hhigh : (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η)
        (unit Mrow reserve ξ : ℝ)(hMmin : Mmin≤unit)(hAdm : Adm unit (frequencyLoss Z 32 ξ+reserve) ξ)
        (hω : 0≤frequencyLoss Z 32 ξ+reserve)(hξ : 0≤ξ)
        (hMcap' : unit+εwidth*unit+ξ/2≤Mcap)
        (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit)
        (hzslot : Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧
          (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit)
        (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
          Cycle63.AffineLedger.B*unit)
        {Label : Type}[Fintype Label]
        (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
        (firstIndex : Label→GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
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
        ∀(hf : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2)
          (heq : ∀l,primeSupport (first l).1.1=primeSupport (first l).1.2)
          (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
          (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤Z^Bnorm)
          (Tfirst p exponent : ℝ)(hTfirst : 1≤Tfirst)(hp : p≤Bnorm)
          (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
          (hinj : Function.Injective (fun l=>(first l,seed l)))
          (hfirstseed : ∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2)
          (hfirstproj : ∀l,seed₀∣firstProjectorRadical (first l).1.1 (first l).1.2 (first l).2.val)
          (hfirstnorm : ∀l,((first l).1.1.absNorm:ℝ)≤Z^Bnorm ∧ ((first l).1.2.absNorm:ℝ)≤Z^Bnorm)
          (hrad : ∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤Z^p)
          (hgeom : ∀l,labelExp reflected Z (Real.logb Z (volume s)) (first l)≤exponent)
          (hfirstshell : ∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst)
          (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
          (hU : ∀r∈rows,ActualSecondBlockIndex.IsInactive r.2)
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
          (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤Z^Bmask),
        let st:=fun r=>retainedState Z Bmask hZ ((g r).datum.τ (χ r)) (internalQ Q η₀)
          ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
        let low:=fun r=>ActualLow M H hH (st r) η₀ (inf_le_left.trans hQM) inf_le_right
          aLow e (3*(i+1:ℕ)*Z^τ)
        ∀(left₁ : Bool)(u₀ : O)(unit₁ : FirstSourceLabel→O)(Tz : ℝ),
        left₁=!reflected → u₀≠0 →
        ((∀l,IsUnit (unit₁ l)) ∧ Real.logb Z (normValue u₀)≤ε) →
        let mult:=fun r : rows=>firstRowMultiplier first left₁ u₀ unit₁ r.val
        (∀r,∀(W' : ℝ)(hW' : (st r).width≤W'),Presented η₀ Z (widenState (st r) W' hW') (mult r) Tz) →
        ∀(divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂)
          (hdivisor : ∀r,divisorSeed r∣(q r).E₂)(p₀ : Profiles a b)
          (hp₁ : s.W₁=(p₀.profile 0 : ℝ→ℂ))(hp₂ : s.W₂=(p₀.profile 1 : ℝ→ℂ))
          (zs : rows→Finset O)(weight : rows→O→ℝ)
          (hnonneg : ∀r,∀z∈zs r,0≤weight r z)
          (hkeep : ∀r,∀z∈zs r,(st r).radial.keep z ∧ low r z)
          (hweight : ∀r,∀z∈zs r,weight r z≤
            ((st r).radial.profile (‖eisEmbedding z‖^2/(st r).radial.scale)).re)
          (Ψ : 𝓢(ℝ,ℂ))
          (hsourceOriginal : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass)
          (hplain₁ : ∀x,s.W₁ x≠0→ap≤x)(hplain₂ : ∀x,s.W₂ x≠0→ap≤x)
          (sideLower : ℝ)
          (hside : ∀l,sideLower≤geometryHighSide reflected (Real.logb Z (volume s))
            (geometryExponents s R seed₀ (Z^Mrow) Z ξ (firstIndex l).1.val.1.val))
          (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Z^U)
          (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j)≤window)
          (hplainScale : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j≤Z^L),
        let src:=fun r=>withHeight (q r).first ((g r).datum.τ (χ r)) heightV
        let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
        let unionDs:=sharedProjectors Ds
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*unit+ξ/2-unit*(Cycle63.AffineLedger.lowReserve)+(unit-Mrow)+εold+2*ε*d*(Fintype.card α:ℝ)+
          Cycle63.AffineLedger.lowRate*(frequencyLoss Z 32 ξ+reserve+εpad*unit)+Cycle63.AffineLedger.q*mesh+pad
        let exponentFull:=(Bmass*εmass-sideLower)+amp+p+exponent+error+εv+Bnorm*εshell+εlabels
        let factor : ℝ:=mainLowQuantitativeFactor Cg b Cs (p₀.control Sp) heightV height physical Z
          exponentFull (seed₀.absNorm:ℝ) N degree box.card
        let cost:=fun (r : rows)(D : Ideal O)=>
          (firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
            normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive)*
          (∑z∈zs r,weight r z*‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2)
        (∑r,∑D∈Ds r,cost r D)≤
          factor*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell))

variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 80000 in
set_option linter.defProp false in
def actual_geometry_selected_low_full_columns {Adm : ℝ→ℝ→ℝ→Prop} {labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ}
    {Presented : (Bmask : ℝ) → Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop}
    {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L Lslot lo hi Mcap εold : ℝ)
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
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L) :
    ∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤M),
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
      Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,
        PLift (0<Cu) ×
        ΣCg : ℝ,PLift (0<Cg ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
          lowFullLiteralSpec (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm labelExp (Presented Bmask)
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      degree Sp Cg Cu η₀ Q hQM Z) :=
by
  exact
    let unionBase:=actual_second_low_weighted_shells.{0,0} (α:=α) N U εshell εunion hUcap heshell.le heunion
    let Cu:=Classical.choose unionBase
    let hu:=Classical.choose_spec unionBase
    let sourceCaps:=eventual_low_chain_source_caps N window b pad L hwindow hb hpad hL0
    fun (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)
        (hQ0 : internalQ Q η₀≠0)(hQt : internalQ Q η₀≠⊤)
        (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})=>
      let kernel := lowFullKernel (α:=α) M H hH
        W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell N Cs supply εv Bnorm εlabels hrow5
        η₀ Q hQM hQ0 hQt hQ72
      let degree:=kernel.1
      let Sp:=kernel.2.1
      let Cg:=kernel.2.2.1
      let hc:=kernel.2.2.2.down
      ⟨degree,Sp,Cu,PLift.up hu.1,Cg,PLift.up (And.intro hc.1 (show ∀ᶠZ : ℝ in atTop,2≤Z ∧
        lowFullLiteralSpec (α:=α) M H hH
        W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
        Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
        bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
        supply εv Bnorm εlabels hsupply hev hBnorm hel Adm labelExp (Presented Bmask)
        ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
        degree Sp Cg Cu η₀ Q hQM Z from by
        filter_upwards [hc.2,hu.2,sourceCaps] with Z hz hzu hzsource
        refine ⟨hz.1,?_⟩
        exact fun (hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
          (heightV height mesh aLow : ℝ)(i : ℕ)
          (hcard : Fintype.card α≤N)(hmass : ∀j,s.M j≤Cs)(hsupply' : supply≤ s.lower)
          (hm : Matches M H hH s η₀ θ w σ freq W B Z)
          (hsupper : s.upper≤bs)(hsb₁ : s.b₁=b)(hsb₂ : s.b₂=b)
          (hw : ∀j,0≤w j)(hwL : ∀j,w j≤Lslot)
          (hwr : ∀j,w j/d≤Rwidth)(hmesh : 0≤ mesh)(hwm : ∀j,w j≤ mesh)
          (hσlo : ∀j,lo≤σ j)(hσhi : ∀j,σ j≤hi)(hheight : 0≤height)(hfreq : ∀j,|freq j|≤height)
          (haLow : 51/100≤aLow)(haLow' : aLow≤((1+Cycle63.AffineLedger.q)/2))
          (hfreqbin : |heightV|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ)
          (hhigh : (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η)
          (unit Mrow reserve ξ : ℝ)(hMmin : Mmin≤unit)(hAdm : Adm unit (frequencyLoss Z 32 ξ+reserve) ξ)
          (hω : 0≤frequencyLoss Z 32 ξ+reserve)(hξ : 0≤ξ)
          (hMcap' : unit+εwidth*unit+ξ/2≤Mcap)
        (hfit : Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit)
          (hzslot : Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧
            (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit)
          (haff : length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
            Cycle63.AffineLedger.B*unit)
          {Label : Type}[Fintype Label]
          (reflected second : Bool)(R seed₀ : Ideal O)(bin : ℤ×(Fin 5→ℤ))(t : ℝ)
          (firstIndex : Label→GeometryLowFirstIndex reflected s R seed₀ (Z^Mrow) Z ξ
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)=>
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
          fun (hf : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2)
            (heq : ∀l,primeSupport (first l).1.1=primeSupport (first l).1.2)
            (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
              (geometryColumnIdeal reflected s R seed₀ (Z^Mrow) Z ξ
                (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
              R s.ν s.W s.P≠0)
            (hw₁ : s.W₁ 0=0)(hw₂ : s.W₂ 0=0)
            (hsource : ∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤Z^Bnorm)
            (Tfirst p exponent : ℝ)(hTfirst : 1≤Tfirst)(hp : p≤Bnorm)
            (hs₀ : Squarefree seed₀)(hs₀0 : seed₀≠0)
            (hinj : Function.Injective (fun l=>(first l,seed l)))
            (hfirstseed : ∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2)
            (hfirstproj : ∀l,seed₀∣firstProjectorRadical (first l).1.1 (first l).1.2 (first l).2.val)
            (hfirstnorm : ∀l,((first l).1.1.absNorm:ℝ)≤Z^Bnorm ∧ ((first l).1.2.absNorm:ℝ)≤Z^Bnorm)
            (hrad : ∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤Z^p)
            (hgeom : ∀l,labelExp reflected Z (Real.logb Z (volume s)) (first l)≤exponent)
            (hfirstshell : ∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst)
            (rows : Finset ((l : Label)×GeometryLowSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin (firstIndex l)))
            (hU : ∀r∈rows,ActualSecondBlockIndex.IsInactive r.2)
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
          let fields:=fun r : rows=>actual_geometry_low_paid_fields reflected s R seed₀ Z Mrow amp ξ reserve bs t
            (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 (hU r.val r.property)
            second (B₂ r) (rwitness r) (hf₁ r.val.1) (hf₂ r)
          let hrow:=hz.2 hZ s θ w σ freq heightV height mesh aLow i hcard hmass hsupply' hm hsupper hsb₁ hsb₂
            hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
            unit Mrow (frequencyLoss Z 32 ξ+reserve) ξ hMmin hAdm hω hξ hMcap' hfit hzslot haff
            reflected second first hf heq R (fun l=>(firstIndex l).2)
            (fun l=>geometryColumnCharacter reflected s R seed₀ (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            (fun _=>t) hf₁ Rchild seed K Tsec reserve
            (fun l=>actual_first_live_squarefree
              (geometryFirstSource s R seed₀ (Z^Mrow) Z ξ
                (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)
              (fun _=>logAnnulus) (firstIndex l).1.val (firstIndex l).1.property)
            (fun _=>hw₁) (fun _=>hw₂) hsource Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0 hinj hfirstseed
            hfirstproj hfirstnorm hrad hgeom hfirstshell rows hU box hbox q g
            (fun r=>(fields r).1) (fun r=>(fields r).2.1) (fun r=>(fields r).2.2.1)
            (fun r=>(fields r).2.2.2.1) (fun r=>(fields r).2.2.2.2.1)
            (fun r=>(fields r).2.2.2.2.2.1) (fun r=>(fields r).2.2.2.2.2.2.1) (fun r=>(fields r).2.2.2.2.2.2.2) rfl
          fun (χ : rows→RayFourExpansion.RayCharacter) hP hPN leftR uR unitR Tz hleft hu₀ hdict hpres divisorSeed hE₂
            hdivisor (p₀ : Profiles a b) hp₁ hp₂
            (zs : rows→Finset O)(weight : rows→O→ℝ)
            (hnonneg : ∀r,∀z∈zs r,0≤weight r z) hkeep hweight
            (Ψ : 𝓢(ℝ,ℂ)) hsourceOriginal hplain₁ hplain₂
            (sideLower : ℝ)
            (hside : ∀l,sideLower≤geometryHighSide reflected (Real.logb Z (volume s))
              (geometryExponents s R seed₀ (Z^Mrow) Z ξ (firstIndex l).1.val.1.val))
            (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤Z^U)
            (hwindowSource : ∀j,logWindow (s.lo j) (s.hi j)≤window)
            (hplainScale : ∀side j,Cycle63.Physical.sourcePlainScales s.toData.toSource side j≤Z^L)=>
          let src:=fun r=>withHeight (q r).first ((g r).datum.τ (χ r)) heightV
          let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
          let unionDs:=sharedProjectors Ds
          let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
            (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
          let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
          let error:=εwidth*unit+ξ/2-unit*(Cycle63.AffineLedger.lowReserve)+(unit-Mrow)+εold+2*ε*d*(Fintype.card α:ℝ)+
            Cycle63.AffineLedger.lowRate*(frequencyLoss Z 32 ξ+reserve+εpad*unit)+Cycle63.AffineLedger.q*mesh+pad
          let exponentFull:=(Bmass*εmass-sideLower)+amp+p+exponent+error+εv+Bnorm*εshell+εlabels
          let factor : ℝ:=mainLowQuantitativeFactor Cg b Cs (p₀.control Sp) heightV height physical Z
            exponentFull (seed₀.absNorm:ℝ) N degree box.card
          let cost:=fun (r : rows)(D : Ideal O)=>
            (firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
              normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive)*
            (∑z∈zs r,weight r z*‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2)
          let hcommonCaps:=fun (r : rows)(B : actualAllocations (q r).first.pools (q r).E₂)=>
            hzsource.2 s hcard hwindowSource hsb₁.le hsb₂.le hplainScale
              (q r) B ((g r).datum.τ (χ r)) heightV
          (show (∑r,∑D∈Ds r,cost r D)≤
            factor*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)) from by
            have hphysical : 0≤physical := by
              cases reflected <;> simp only [physical,geometryHighFactor,ite_true]
              · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (geometryDCompensator_pos bin).le
              · exact (inv_pos.mpr (geometryDCompensator_pos bin)).le
            have hCg : 0<Cg := hc.1
            have hfirstMass (l : Label) : 0≤firstMass l :=
              geometry_first_high_mass_nonneg reflected s R seed₀ Ψ Mrow Z ξ εmass
                (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
            have hmassBound (l : Label) : firstMass l≤physical*Z^(Bmass*εmass-sideLower) :=
              actual_geometry_low_uniform_mass reflected N supply ap hsupply hap s R seed₀ Ψ
                Mrow Z ξ Bmass εmass sideLower hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hemass
                hcard hsupply' hs₀ hw₁ hw₂ hsourceOriginal hplain₁ hplain₂ bin (firstIndex l).1.val (hside l)
            have hfactor : 0≤factor :=
              mainLowQuantitativeFactor_nonneg Cg b Cs (p₀.control Sp) heightV height physical Z
                exponentFull (seed₀.absNorm:ℝ) N degree box.card hCg.le
                (zero_le_one.trans hCs) hheight hphysical (zero_lt_one.trans hZ) (Nat.cast_nonneg _)
            have hcost (r : rows)(D : Ideal O) : 0≤ cost r D := by
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
              actual_geometry_low_second_source_caps reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin (firstIndex r.val.1) hw₁ hw₂ r.val.2 N hcard (Z^U) hpool
            have hcap (r : rows)(D : Ideal O)(hD : D∈Ds r) : (D.absNorm:ℝ)≤Z^(((N:ℝ)+2)*U) :=
              (second_datum_projector_cap (datum r) N Z U (hsourcecap r).1 hZ.le hUcap
                (hsourcecap r).2 D (Finset.mem_filter.mp hD).1).2
            have hshell (n : ℤ)(hn : n∈selectedShells unionDs) :
                (∑r,∑D∈shell unionDs n,cost r D)≤factor*(2*dyadicScale n)^(3*εshell) := by
              have hscale:=shared_projector_shell_scale Ds Z (((N:ℝ)+2)*U) hcap n hn
              have hcolumns:=hrow χ hP hPN divisorSeed hE₂ hdivisor (shell unionDs n) (dyadicScale n) pad
                hscale.1 (fun D hD=>let h:=shared_projector_shell_gates Ds n D hD; ⟨h.1,h.2.2⟩)
                p₀ hp₁ hp₂ (fun r B hB=>(hcommonCaps r B).1)
                (fun r B hB D hD al hal side=>⟨(hcommonCaps r B).2 D al side 0,(hcommonCaps r B).2 D al side 1⟩)
                leftR uR unitR Tz hleft hu₀ hdict hpres zs weight hnonneg hkeep hweight firstMass physical
                (Bmass*εmass-sideLower) hphysical hfirstMass hmassBound
              convert hcolumns using 1
              · apply Finset.sum_congr rfl
                intro r hr
                dsimp only [cost]
                rw [Finset.mul_sum]
                dsimp only [src,childSrc,geometryLowFirstChild,first,geometryColumnIdeal,geometryFirstLabel]
                rfl
              · dsimp only [factor,mainLowQuantitativeFactor,exponentFull,error]
                ring
            have hfull:=low_shared_shell_contraction Ds hs cost hcost factor εshell hshell
            apply hfull.trans
            apply mul_le_mul_of_nonneg_left _ hfactor
            have hdatum:=hzu.2 datum (fun r=>(hsourcecap r).1) (fun r=>(hsourcecap r).2)
            simpa only [Ds,shared_squarefree_shells] using hdatum)
        ))⟩

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
