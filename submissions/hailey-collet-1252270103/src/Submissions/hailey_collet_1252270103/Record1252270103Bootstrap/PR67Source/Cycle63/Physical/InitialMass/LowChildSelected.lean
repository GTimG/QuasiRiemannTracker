import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildColumns
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.GeometryMainLowSelected
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.LowChildRowMultiplier
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The selected low frequency columns of the final daughters of the LOW children of a step, paid by the finite
supported label budget: the common statement of the old row and of the row with the second step. Released under
Apache 2.0. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy CenteredMomentSourceLiveColumn
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceMass CenteredMomentRankinRadical CenteredMomentFirstDiscardedEnergy
open CenteredMomentLogDyadic
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

local instance lowChildSelectedDecidable {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The statement of the selected low frequency columns after the choice of the constants `degree`, `Sp`, the character
`η₀`, the ideal `Q` and the constant `Cg`, and the lower bound `Z`: the whole telescope of the data and the
conclusion. See `LowSelectedStmt`. -/
def LowSelectedBody [Led : Cycle63.AffineLedger] {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin εshell : ℝ) (N : ℕ) (Cs supply εv Bnorm εlabels : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop) 
    (degree : ℕ) (Sp : Finset (ℕ×ℕ)) (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) (Cg Z : ℝ) : Prop :=
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Fintype.card α≤N → (∀j,s.M j≤Cs) →
      supply≤ s.lower → Matches M H hH s η₀ θ w σ freq W B Z → s.upper≤bs → s.b₁=b → s.b₂=b →
      (∀j,0≤w j) → (∀j,w j≤Lslot) →
      (∀j,w j/d≤Rwidth) → 0≤ mesh → (∀j,w j≤ mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) → 51/100≤aLow → aLow≤((1+Cycle63.AffineLedger.q)/2) →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(unit Mrow omega ξ : ℝ),Mmin≤unit → Adm unit omega ξ → 0≤omega → 0≤ξ → unit+εwidth*unit+ξ/2≤Mcap →
      Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤unit+(εwidth/2)*unit →
      (Cycle63.AffineLedger.slotFloor*unit≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop*unit) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.B*unit →
    ∀{Label : Type}[Fintype Label],∀(reflected second : Bool)
      (first : Label→FirstSourceLabel)
      (_hf : ∀l,Supported (first l).1.1 ∧ Supported (first l).1.2)
      (_heq : ∀l,primeSupport (first l).1.1=primeSupport (first l).1.2)
      (Rfirst : Ideal O)
      (alloc : (l : Label)→actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χfirst : Label→ Character)(tfirst : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let childSrc := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χfirst l) (tfirst l)
    ∀(R seed : Label→ Ideal O)(K Tsec : Label→ℝ)(reserve : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(childSrc l).W₁ 0=0) → (∀l,(childSrc l).W₂ 0=0) →
    (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (childSrc l)≤Z^Bnorm) →
    ∀(Tfirst p exponent : ℝ),1≤Tfirst → p≤Bnorm →
    ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    Function.Injective (fun l=>(first l,seed l)) →
    (∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2) →
    (∀l,seed₀∣firstProjectorRadical (first l).1.1 (first l).1.2 (first l).2.val) →
    (∀l,((first l).1.1.absNorm:ℝ)≤Z^Bnorm ∧ ((first l).1.2.absNorm:ℝ)≤Z^Bnorm) →
    (∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤Z^p) →
    (∀l,labelExp reflected Z (Real.logb Z (volume s)) (first l)≤exponent) →
    (∀l,Tfirst≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*Tfirst) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (childSrc l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀r∈rows,ActualSecondBlockIndex.IsInactive r.2)
      (box : Finset (Fin 4→ℤ)),
    (∀r∈rows,actualSecondDyad (childSrc r.1) (R r.1) (seed r.1)
      (K r.1) (Tsec r.1) Z ξ r.2∈box) →
    let label := fun r : rows=>actualSecondSupportedLabel (childSrc r.val.1)
      (R r.val.1) (seed r.val.1) (K r.val.1) (Tsec r.val.1) Z ξ r.val.2 (hU r.val r.property)
    let cell := Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/unit))
    let amp := unit*Cycle63.AffineLedger.amp cell
    ∀q : rows→ Chain s,
    ∀g : (r : rows)→LiveMainGeometry s (q r) Z Mrow amp omega ξ bs (Fintype.card α),
    (∀r,(q r).C₁=(if reflected then (first r.val.1).1.2 else (first r.val.1).1.1)) →
    (∀r,(g r).D₁=(if reflected then (first r.val.1).1.1 else (first r.val.1).1.2)) →
    (∀r,(g r).datum.C=(label r).1.1) → (∀r,(g r).datum.D=(label r).1.2) →
    (∀r,HEq (g r).datum.inactive (label r).2.val) →
    (∀r,(q r).E₂=(if second then (label r).1.2 else (label r).1.1)) →
    (∀r,(g r).datum.K=firstMainRadius reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve (first r.val.1)) →
    (∀r,(g r).datum.radius=frequencyRadius (firstMainFourierScale reflected (Z^Mrow) (volume s) Z ξ (3*amp) reserve bs
      (Fintype.card α) (first r.val.1)) Z ξ) →
    omega=frequencyLoss Z 32 ξ+reserve →
    ∀(χ : rows→RayFourExpansion.RayCharacter)(hP : ∀r,(q r).R₂*(q r).E₂≠0)
      (hPN : ∀r,(((q r).R₂*(q r).E₂).absNorm:ℝ)≤Z^Bmask),
    let st := fun r=>retainedState Z Bmask hZ ((g r).datum.τ (χ r)) (internalQ Q η₀)
      ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
    let src := fun r=>withHeight (q r).first ((g r).datum.τ (χ r)) v
    ∀(divisorSeed : rows→ Ideal O)(hE₂ : ∀r,Supported (q r).E₂),(∀r,divisorSeed r∣(q r).E₂) →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ),1≤T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      (commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.allowance Z≤pad) →
    (∀r,∀B₂ : actualAllocations (src r).pools (q r).E₂,
      commonScalar (src r) (q r).E₂ (q r).R₂ B₂≠0 →
      ∀D∈Ds,∀al∈(commonData (src r) (q r).E₂ (q r).R₂ B₂).toSource.active D,∀side : Bool,
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 0≤Z^L ∧
      finalPlain (commonData (src r) (q r).E₂ (q r).R₂ B₂) side D al 1≤Z^L) →
    ∀(left₁ : Bool)(u₀ : O)(unit₁ : FirstSourceLabel→O)(Tz : ℝ),
    left₁=!reflected → u₀≠0 →
    ((∀l,IsUnit (unit₁ l)) ∧ Real.logb Z (normValue u₀)≤ε) →
    let mult := fun r : rows=>firstRowMultiplier first left₁ u₀ unit₁ r.val
    (∀r,∀(W' : ℝ)(hW' : (st r).width≤W'),Presented η₀ Z (widenState (st r) W' hW') (mult r) Tz) →
    let low := fun r=>ActualLow M H hH (st r) η₀ (inf_le_left.trans hQM) inf_le_right
      aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : rows→Finset O)(weight : rows→O→ℝ),(∀r,∀z∈zs r,0≤weight r z) →
      (∀r,∀z∈zs r,(st r).radial.keep z ∧ low r z) →
      (∀r,∀z∈zs r,weight r z≤((st r).radial.profile (‖eisEmbedding z‖^2/(st r).radial.scale)).re) →
    ∀(mass : Label→ℝ)(physical loss : ℝ),0≤physical → (∀l,0≤ mass l) →
      (∀l,mass l≤physical*Z^loss) →
    let c := fun r=>mass r.val.1/volume (childSrc r.val.1)*
      (g r).datum.K*normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
    let error := εwidth*unit+ξ/2-unit*(Cycle63.AffineLedger.lowReserve)+(unit-Mrow)+εold+2*ε*d*(Fintype.card α:ℝ)+
      Cycle63.AffineLedger.lowRate*(omega+εpad*unit)+Cycle63.AffineLedger.q*mesh+pad
    (∑r,c r*(∑D∈Ds,∑z∈zs r,weight r z*
      ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2))≤
      Cg*(2*b^2*Cs^(4*N))*QuadraticInitialBound.diagonalControl ballProfile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*(2*T)^(3*εshell)*(box.card:ℝ)*physical*
        Z^(loss+amp+p+exponent+error+εv+Bnorm*εshell+εlabels)/(seed₀.absNorm:ℝ)

/-- The statement of the selected low frequency columns at a character `η₀` and an ideal `Q` below `M` whose internal
modulus is nonzero, not the unit ideal and below `(72)`: there are constants `degree`, `Sp` and `Cg` such that, for all
large `Z`, the body holds. See `LowSelectedStmt`. -/
def LowSelectedAt [Led : Cycle63.AffineLedger] {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin εshell : ℝ) (N : ℕ) (Cs supply εv Bnorm εlabels : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M) : Prop :=
    internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
    LowSelectedBody (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell N Cs
      supply εv Bnorm εlabels Adm labelExp Presented degree Sp η₀ Q hQM Cg Z

/-- The selected low frequency columns of the final daughters of the LOW children of a step are paid by the finite
supported label budget. The bound is the old bound of `actual_selected_low_paid_columns` with the exponent of the
labels `labelExp reflected Z (log volume s) (first l)` in place of `lowGeometryExponent`, and the units `unit` with
`Adm unit omega ξ`; the children are presented (`Presented`) by the multipliers `mult r = firstRowMultiplier first left₁
u₀ unit₁ r` of the rows, for the orientation `left₁`, the fixed row `u₀` and the units `unit₁`, when the second step is
run. The factors `unit₁` are units and the fixed row has log norm at most `ε` (`hdict`), and the radius of the datum of
a row is the frequency radius of its first label (`hRadius`), so that the energy scale of the child is determined by the
first label. The constants `degree`, `Sp` and `Cg` depend on the character `η₀` and on the ideal `Q`, which come
first. The orientation of the multipliers is the physical one, `left₁ = !reflected` (`hleft`: the first-level
payment of the coordinates of the rows holds only for it), the fixed row is nonzero (`hu₀`: the multipliers of the rows
are then nonzero), and the projector `seed₀` divides the first projector radical
of every label (`hfirstproj`: the factor `1/N(seed₀)` of the bound is then also available for the returned parts of the
rows). The error is the old one, with the rate `lowRate` of the ledger. The lengths `w j` of the slots are at most the
slot bound `Lslot`, which the second step may take smaller than the common mesh of the old moment. -/
def LowSelectedStmt [Led : Cycle63.AffineLedger] {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d : ℝ)
    (bs εwidth εpad Mmin εshell : ℝ) (N : ℕ) (Cs supply εv Bnorm εlabels : ℝ)
    (Adm : ℝ → ℝ → ℝ → Prop) (labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop)  : Prop :=
    ∀η₀ : Character, ∀Q : Ideal O, ∀hQM : Q≤M,
    LowSelectedAt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell N Cs
      supply εv Bnorm εlabels Adm labelExp Presented η₀ Q hQM

variable [Cycle63.AffineLedger] in
/-- The old bound of the selected low columns (`actual_selected_low_paid_columns`) is the bound of `LowSelectedStmt`
for all units and the exponent `lowGeometryExponent` of the labels, for every slot bound `Lslot` below the common mesh
of the old moment. -/
theorem lowSelectedStmt_of_row5 [Cycle63.AffineLedger.DeletesIntoOldRegion] {α : Type} [Fintype α] [DecidableEq α]
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
    (hBnorm : 0≤Bnorm)(hel : 0<εlabels)
    (Presented : Character → (Z : ℝ) → NaturalState Z Bmask 2 → O → ℝ → Prop) :
    LowSelectedStmt (α:=α) M H hH W B a b Bmask L Lslot lo hi Mcap εold Rwidth τ ε e η d bs εwidth εpad Mmin εshell N Cs
      supply εv Bnorm εlabels (fun _ _ _ => True) lowGeometryExponent Presented := by
  obtain ⟨degree,Sp,h⟩ := actual_selected_low_paid_columns (α:=α) M H hH W A B a b Bmask L lo hi Mcap εold
    hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs supply εv Bnorm εlabels hsupply hev hBnorm hel
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := h η₀ Q hQM hQ0 hQt hQ72
  refine ⟨degree,Sp,Cg,hCg,?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro hZone s θ w σ freq v height mesh aLow i hcard hmass hsupply' hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow omega ξ
    hMmin _ hω hξ hMcap' hfit hzslot haff Label _ reflected second first hf heq Rfirst alloc χfirst tfirst halloc
    childSrc R seed K Tsec reserve hseed hw₁ hw₂ hsource Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0
    hinj hfirstseed _ hfirstnorm hrad hgeom hfirstshell rows hU box hbox label cell amp q g
    hC₁ hD₁ hC₂ hD₂ hU₂ hEeq hKeq _ hωeq χ hP hPN st src divisorSeed hE₂ hdivisor Ds T pad hT hDs
    p₀ hp₁ hp₂ hallow hcaps left₁ u₀ unit₁ Tz _ _ _ mult _ low zs weight hnonneg hkeep hweight mass physical loss
    hphysical hmass0 hmasscap c error
  have hh := hZ.2 hZone s θ w σ freq v height mesh aLow i hcard hmass hsupply' hm hsupper hsb₁ hsb₂
    hw (fun j => (hwL j).trans hLslot) hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh unit Mrow
    omega ξ
    hMmin hω hξ hMcap' hfit hzslot haff reflected second first hf heq Rfirst alloc χfirst tfirst halloc
    R seed K Tsec reserve hseed hw₁ hw₂ hsource Tfirst p exponent hTfirst hp seed₀ hs₀ hs₀0
    hinj hfirstseed hfirstnorm hrad hgeom hfirstshell rows hU box hbox q g
    hC₁ hD₁ hC₂ hD₂ hU₂ hEeq hKeq hωeq χ hP hPN divisorSeed hE₂ hdivisor Ds T pad hT hDs
    p₀ hp₁ hp₂ hallow hcaps zs weight hnonneg hkeep hweight mass physical loss hphysical hmass0 hmasscap
  exact hh

end
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
