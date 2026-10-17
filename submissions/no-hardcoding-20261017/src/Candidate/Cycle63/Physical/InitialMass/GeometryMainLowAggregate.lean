import Candidate.Cycle63.Physical.InitialMass.GeometryMainNormalized
import Candidate.Cycle63.Physical.InitialMass.SecondProjectorShell
import Candidate.Cycle63.Physical.InitialMass.SecondLabelDisintegration
import Candidate.Cycle63.Physical.InitialMass.GeometryCostSelection
import Candidate.Cycle63.Arithmetic.Constants

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open HeckeFamily CanonicalQuadraticSieve RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonLinearNormalization
open CenteredMomentAmplificationChildInput CenteredMomentCommonHeightEnvelope
open CenteredMomentExceptionalAmplitudePair CenteredMomentSecondCanonicalScalar
open CenteredMomentSourceLiveColumn CenteredMomentSecondInputCapacitySource
open CenteredMomentCommonPairedSource
open CenteredMomentSecondEnergySplit CenteredMomentSectorLocalization
open Cycle63FinalNatural CenteredMomentEnergyState
open CenteredMomentSecondLiveBlock CenteredMomentSecondCanonical CenteredMomentSourceRow
open CenteredMomentSecondRetainedAggregate CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondBlockAggregate CenteredMomentSourceMass CenteredMomentRankinRadical
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
open Cycle63Moment CenteredMomentLogDyadic CenteredMomentCommonPairedSource
open CenteredMomentWholeDivisorShell
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
local instance geometryMainLowAggregateSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The genuine uniform low-column theorem accepts the selected first
mass divided by its child volume. All second scalar factors stay inside
the complete frequency sum, before any row-independent allocation choice. -/
theorem actual_selected_low_physical_family_columns
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0<margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell)
    (Nweight : ℕ) (slotlo plainlo : ℝ) (hslot : 0<slotlo) (hplain : 0<plainlo) :
    ∃degree : ℕ, ∃Sp : Finset (ℕ×ℕ), ∀η₀ : Character, ∀Q : Ideal O,
    ∀hQM : Q≤M, internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃Cg : ℝ, 0<Cg ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(s : Input α)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
      (v height mesh aLow : ℝ)(i : ℕ),
      Matches M H hH s η₀ θ w σ freq W B Z → s.η=ηseed → s.upper≤bs → s.b₁=b → s.b₂=b →
      (∀j,0≤w j) → (∀j,w j≤Cycle25.Energy.commonMesh Mcap Bmask L εold) →
      (∀j,w j/d≤Rwidth) → 0≤mesh → (∀j,w j≤mesh) → (∀j,lo≤σ j) → (∀j,σ j≤hi) →
      0≤height → (∀j,|freq j|≤height) → 51/100≤aLow → aLow≤((1+Cycle63.Arithmetic.q0)/2) →
      |v|+height+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^η →
    ∀(Mrow omega ξ : ℝ),Mmin≤Mrow → 0≤omega → 0≤ξ → Mrow+εwidth*Mrow+ξ/2≤Mcap →
      (Cycle63.Optimization.slotFloor*Mrow≤∑j,Real.logb Z (s.P j) ∧ (∑j,Real.logb Z (s.P j))≤Cycle63.Optimization.slotTop*Mrow) →
      length Z s.X₁+length Z s.X₂+Cycle63.Arithmetic.lambda*(∑j,Real.logb Z (s.P j))≤Cycle63.Arithmetic.B*Mrow →
    ∀(reflected : Bool)(R seed : Ideal O)(bin : ℤ×(Fin 5→ℤ))(t _Mprice _Aprice : ℝ)
      (_sourceWeight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ),
    ∀{Label : Type*}[Fintype Label][DecidableEq Label],
    ∀firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin,
    ∀q : Label→Chain s,
    (∀l,(q l).C₁=geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val) →
    (∀l,(q l).R₁=R) → (∀l,HEq (q l).B₁ (firstIndex l).2) →
    (∀l,(q l).η₁=geometryColumnCharacter reflected s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val) →
    (∀l,(q l).t₁=t) →
    let cell := Cycle63.Arithmetic.cellUpper (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
    let amp := Mrow*Cycle63.Arithmetic.amp cell
    ∀g : (l : Label)→LiveMainGeometry s (q l) Z Mrow amp omega ξ bs (Fintype.card α),
    (∀l,(g l).reflected=reflected) →
    (∀l,(g l).C₀=(geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val.1).C) →
    (∀l,(g l).D₀=(geometryFirstSource s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val.1).D) →
    ∀(χ : Label→RayFourExpansion.RayCharacter)(hP : ∀l,(q l).R₂*(q l).E₂≠0)
      (hPN : ∀l,(((q l).R₂*(q l).E₂).absNorm:ℝ)≤Z^Bmask),
    let st := fun l=>retainedState Z Bmask hZ ((g l).datum.τ (χ l)) (internalQ Q η₀)
      ((q l).R₂*(q l).E₂) (hP l) (hPN l) (g l).datum.radius (g l).datum.C (g l).datum.D (g l).datum.inactive
    let src := fun l=>withHeight (q l).first ((g l).datum.τ (χ l)) v
    let nominal := fun l=>secondNominal Mrow Z amp omega (q l).C₁ (g l).D₁
      (g l).datum.C (g l).datum.D (g l).datum.inactive
    let δwidth := εwidth*Mrow+ξ/2
    let padding := omega+εpad*Mrow
    ∀(divisorSeed : Label→Ideal O)(hE₂ : ∀l,Supported (q l).E₂),(∀l,divisorSeed l∣(q l).E₂) →
    ∀(Ds : Finset (Ideal O))(T pad : ℝ),1≤T →
      (∀D∈Ds,Squarefree D ∧ T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
    ∀p₀ : Profiles a b,s.W₁=(p₀.profile 0 : ℝ→ℂ) → s.W₂=(p₀.profile 1 : ℝ→ℂ) →
    (∀l,∀B₂ : actualAllocations (src l).pools (q l).E₂,
      commonScalar (src l) (q l).E₂ (q l).R₂ B₂≠0 →
      (commonData (src l) (q l).E₂ (q l).R₂ B₂).toSource.allowance Z≤pad) →
    (∀l,∀B₂ : actualAllocations (src l).pools (q l).E₂,
      commonScalar (src l) (q l).E₂ (q l).R₂ B₂≠0 →
      ∀D∈Ds,∀alloc∈(commonData (src l) (q l).E₂ (q l).R₂ B₂).toSource.active D,∀second : Bool,
      finalPlain (commonData (src l) (q l).E₂ (q l).R₂ B₂) second D alloc 0≤Z^L ∧
      finalPlain (commonData (src l) (q l).E₂ (q l).R₂ B₂) second D alloc 1≤Z^L) →
    let low := fun l=>ActualLow M H hH (st l) η₀ (inf_le_left.trans hQM) inf_le_right
      aLow e (3*(i+1:ℕ)*Z^τ)
    ∀(zs : Label→Finset O)(weight : Label→O→ℝ),(∀l,∀z∈zs l,0≤weight l z) →
      (∀l,∀z∈zs l,(st l).radial.keep z ∧ low l z) →
      (∀l,∀z∈zs l,weight l z≤((st l).radial.profile (‖eisEmbedding z‖^2/(st l).radial.scale)).re) →
    ∀coefficient : Label→ℝ,(∀l,0≤coefficient l) →
    let c := fun l=>coefficient l*
      ((g l).datum.K/lowerFactor Nweight slotlo plainlo)*
      normalizer (g l).datum.C (g l).datum.D (g l).datum.inactive
    (∑l,c l*(∑D∈Ds,∑z∈zs l,weight l z*
      ‖normalizedColumn (src l) (q l).E₂ (hE₂ l) (q l).R₂ (divisorSeed l) D z‖^2))≤
      Cg*∑l,c l*((src l).toData.profileFactor*(∏j,(src l).M j)^2*
        QuadraticInitialBound.diagonalControl (st l).radial.profile*(p₀.control Sp)^2*
        (1+|v|+height)^degree*((q l).E₂.absNorm:ℝ)^(εshell-1)*(2*T)^(3*εshell)*
        Z^(nominal l+δwidth+amp-Mrow*(Cycle63.Arithmetic.lowReserve)+εold+2*ε*d*(Fintype.card α:ℝ)+
          (2*Cycle63.Arithmetic.q0/9)*padding+Cycle63.Arithmetic.q0*mesh)*Z^pad) := by
  obtain ⟨degree,Sp,hcolumn⟩ := actual_live_main_low_profile_column (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell
  refine ⟨degree,Sp,?_⟩
  intro η₀ Q hQM hQ0 hQt hQ72
  obtain ⟨Cg,hCg,hbound⟩ := hcolumn η₀ Q hQM hQ0 hQt hQ72
  refine ⟨Cg,hCg,?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro hZ s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
    hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow omega ξ hMmin hω hξ hMcap' hzslot haff
    reflected R seed bin t Mprice Aprice sourceWeight Label _ _ firstIndex q hCq hRq hBq hηq htq
    cell amp g hgref hgC hgD χ hP hPN st src nominal δwidth padding divisorSeed hE₂ hseed
    Ds T pad hT hDs p₀ hp₁ hp₂ hallow hcaps low zs weight hnonneg hkeep hweight coefficient hcoefficient c
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _
  have hh := hz.2 hZ s θ w σ freq v height mesh aLow i hm hsη hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh
    Mrow omega ξ hMmin hω hξ hMcap' hzslot haff (q l) (g l) (χ l) (hP l) (hPN l)
    (divisorSeed l) (hE₂ l) (hseed l) Ds T pad hT hDs p₀ hp₁ hp₂ (hallow l) (hcaps l)
    (zs l) (weight l) (hnonneg l) (hkeep l) (hweight l)
  have hc : 0≤c l := by
    dsimp only [c]
    exact mul_nonneg (mul_nonneg
      (hcoefficient l)
      (div_nonneg (g l).datum.K_pos.le (lowerFactor_pos Nweight slotlo plainlo hslot hplain).le))
      (normalizer_pos (g l).datum.C (g l).datum.D (g l).datum.hC (g l).datum.inactive).le
  apply (mul_le_mul_of_nonneg_left hh hc).trans_eq
  ring

universe u v
attribute [local irreducible] geometryLowActualChain geometryLowActualGeometry geometryLowSecondDatum
set_option linter.defProp false in
/-- Literal original main constructors for the selected physical low
energy. The final nonnegative coefficient is chosen by the first cost
selection, without requiring an energy bound as an input. -/
def actual_geometry_selected_low_physical_columns {α : Type u} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (A B a b Bmask L lo hi Mcap εold : ℝ)
    (hA : 0<A) (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (hB : 0≤B) (ha : 0<a) (ha' : a≤1/4) (hb : 1≤b)
    (hBmask : 0≤Bmask) (hMcap : 0<Mcap) (hεold : 0<εold)
    (hbeta : 51/100≤HeckeZeroSupremum.beta)
    (Rwidth dmax τ ε e κ η margin d : ℝ)
    (hRw : 0≤Rwidth) (hdmax : 0≤dmax) (hτ : 0<τ) (hε : 0<ε)
    (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hη : 0≤η)
    (hbudget : 8*e*Rwidth+κ≤ε) (hmargin : 0<margin)
    (hd : 0<d) (hdsupply : Mcap+Bmask+margin≤d) (hdm : d≤dmax)
    (ηseed : Character) (bs εwidth εpad Mmin : ℝ)
    (hbs : 1≤bs) (hew : 0<εwidth) (hep : 0<εpad) (hmin : 0<Mmin)
    (εshell : ℝ) (heshell : 0<εshell)
    (Nweight : ℕ) (slotlo plainlo : ℝ) (hslot : 0<slotlo) (hplain : 0<plainlo) :=
  let hbase := actual_selected_low_physical_family_columns.{u,v} (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell Nweight slotlo plainlo hslot hplain
  let degree := Classical.choose hbase
  let hdegree := Classical.choose_spec hbase
  let Sp := Classical.choose hdegree
  let hcolumn := Classical.choose_spec hdegree
  (degree,Sp,fun η₀ Q hQM hQ0 hQt hQ72=>
    let hc := hcolumn η₀ Q hQM hQ0 hQt hQ72
    let Cg := Classical.choose hc
    let hg := Classical.choose_spec hc
    (Cg,PLift.up (And.intro hg.1 (Filter.Eventually.mono hg.2 (fun Z hz=>
      And.intro hz.1
      (fun (hZ : 1<Z) (s : Input α) (θ : α→RayQuotient.Characters M H)
        (w σ freq : α→ℝ) (heightV height mesh aLow : ℝ) (i : ℕ)
        hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
        hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh (Mrow reserve ξ : ℝ) hMmin hω hξ hMcap'
        hzslot haff (reflected : Bool) (R seed : Ideal O) (bin : ℤ×(Fin 5→ℤ))
        (t Mprice Aprice : ℝ)
        (sourceWeight : Cycle63JointSource.SourceCoordinate s R seed (Z^Mrow) Z ξ→ℂ)
        {Label : Type v} [Fintype Label] [DecidableEq Label]
        (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin)=>
        let cell := Cycle63.Arithmetic.cellUpper
          (Cycle63.Moment.originalCell ((∑j,Real.logb Z (s.P j))/Mrow))
        let amp := Mrow*Cycle63.Arithmetic.amp cell
        fun (hw₁ : s.W₁ 0=0) (hw₂ : s.W₂ 0=0)
        (n : (l : Label)→GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l))=>
        let datum := fun l=>geometryLowSecondDatum reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l)
        let firstChild := fun l=>geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin t (firstIndex l)
        fun (second : Label→Bool)
          (B₂ : (l : Label)→actualAllocations (firstChild l).pools
            (if second l then (datum l).D else (datum l).C))
          (r : (l : Label)→secondLiveRows (fun _:Unit=>(datum l).block))
          (hf₁ : ∀l,frozenCoefficient (firstIndex l).2.val
            (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
              (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val)
            R s.ν s.W s.P≠0)
          (hf₂ : ∀l,frozenCoefficient (B₂ l).val
            (if second l then (datum l).D else (datum l).C) (datum l).R
            (firstChild l).ν (firstChild l).W (firstChild l).P≠0)=>
        let q : Label→Chain s := fun l=>geometryLowActualChain reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l)
        let g : (l : Label)→LiveMainGeometry s (q l) Z Mrow amp
          (frequencyLoss Z 32 ξ+reserve) ξ bs (Fintype.card α) := fun l=>geometryLowActualGeometry reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l) (r l) (hf₁ l) (hf₂ l)
        let hfields := fun l=>actual_geometry_low_admission_fields reflected s R seed Z Mrow amp ξ reserve bs t
          (Fintype.card α) hZ bin (firstIndex l) hw₁ hw₂ (n l) (second l) (B₂ l) (r l) (hf₁ l) (hf₂ l)
        hz.2 hZ s θ w σ freq heightV height mesh aLow i hm hsη hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm
          hσlo hσhi hheight hfreq haLow haLow' hfreqbin hhigh Mrow (frequencyLoss Z 32 ξ+reserve) ξ
          hMmin hω hξ hMcap' hzslot haff reflected R seed bin t Mprice Aprice sourceWeight firstIndex q
          (fun l=>(hfields l).1) (fun l=>(hfields l).2.1) (fun l=>(hfields l).2.2.1)
          (fun l=>(hfields l).2.2.2.1) (fun l=>(hfields l).2.2.2.2.1) g
          (fun l=>(hfields l).2.2.2.2.2.2.1)
          (fun l=>(hfields l).2.2.2.2.2.2.2.1)
          (fun l=>(hfields l).2.2.2.2.2.2.2.2.1)))))))

/-- The occupied first labels and projectors, with no extension of an
allocation to a zero or unsupported ideal. -/
def selectedLowFirstLabels {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) : Finset FirstSourceLabel :=
  Finset.univ.image first

def selectedLowFirstProjectors {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→Ideal O)
    (l : FirstSourceLabel) : Finset (Ideal O) :=
  (Finset.univ.filter (fun j=>first j=l)).image seed

abbrev SelectedLowFirstPair {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→Ideal O) :=
  (l : selectedLowFirstLabels first) × selectedLowFirstProjectors first seed l.val

def selectedLowFirstPair {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→Ideal O) (j : Label) :
    SelectedLowFirstPair first seed :=
  ⟨⟨first j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩⟩,
    ⟨seed j,Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩⟩⟩

theorem selected_low_first_pair_bijective {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j))) :
    Function.Bijective (selectedLowFirstPair first seed) := by
  constructor
  · intro j k h
    apply hinj
    exact Prod.ext (congrArg (fun x=>(x.1.val)) h) (congrArg (fun x=>x.2.val) h)
  · intro x
    obtain ⟨j,hj,hseed⟩ := Finset.mem_image.mp x.2.property
    have hfirst : first j=x.1.val := (Finset.mem_filter.mp hj).2
    refine ⟨j,?_⟩
    apply Sigma.ext
    · exact Subtype.ext hfirst
    · apply (Subtype.heq_iff_coe_eq (fun D=>by
        dsimp only [selectedLowFirstPair]
        rw [hfirst])).mpr
      exact hseed

def selectedLowFirstPairEquiv {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j))) :
    Label ≃ SelectedLowFirstPair first seed :=
  Equiv.ofBijective _ (selected_low_first_pair_bijective first seed hinj)

/-- Reindex the entire selected child cost, after the second-label sum has
been formed. The inverse pair index keeps the actual first allocation. -/
theorem selected_low_first_cost_reindex {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (children : Label→Finset FirstSourceLabel) (cost : Label→FirstSourceLabel→ℝ) :
    (∑j,∑v∈children j,cost j v)=
      ∑l : selectedLowFirstLabels first,
        ∑D : selectedLowFirstProjectors first seed l.val,
          ∑v∈children ((selectedLowFirstPairEquiv first seed hinj).symm ⟨l,D⟩),
            cost ((selectedLowFirstPairEquiv first seed hinj).symm ⟨l,D⟩) v := by
  calc
    _=∑p : SelectedLowFirstPair first seed,
        ∑v∈children ((selectedLowFirstPairEquiv first seed hinj).symm p),
          cost ((selectedLowFirstPairEquiv first seed hinj).symm p) v :=
      Fintype.sum_equiv (selectedLowFirstPairEquiv first seed hinj) _ _ (fun j=>by simp)
    _=_ := Fintype.sum_sigma _

theorem selected_low_pair_inverse_fields {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (p : SelectedLowFirstPair first seed) :
    first ((selectedLowFirstPairEquiv first seed hinj).symm p)=p.1.val ∧
      seed ((selectedLowFirstPairEquiv first seed hinj).symm p)=p.2.val := by
  have h := (selectedLowFirstPairEquiv first seed hinj).apply_symm_apply p
  exact ⟨congrArg (fun x=>x.1.val) h,congrArg (fun x=>x.2.val) h⟩

def selectedLowSupportedChildren {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (children : Label→Finset FirstSourceLabel)
    (l : FirstSourceLabel) (D : Ideal O) : Finset FirstSourceLabel :=
  if h : l∈selectedLowFirstLabels first ∧ D∈selectedLowFirstProjectors first seed l then
    children ((selectedLowFirstPairEquiv first seed hinj).symm ⟨⟨l,h.1⟩,⟨D,h.2⟩⟩)
  else ∅

@[simp] theorem selected_low_supported_children_at {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (children : Label→Finset FirstSourceLabel) (p : SelectedLowFirstPair first seed) :
    selectedLowSupportedChildren first seed hinj children p.1.val p.2.val=
      children ((selectedLowFirstPairEquiv first seed hinj).symm p) := by
  unfold selectedLowSupportedChildren
  rw [dite_eq_left (show p.1.val∈selectedLowFirstLabels first ∧
    p.2.val∈selectedLowFirstProjectors first seed p.1.val from ⟨p.1.property,p.2.property⟩)]

/-- The supported payment domain is exactly the image of selected first
pairs, with the dependent second children retained in every occupied fiber. -/
theorem selected_low_supported_sum {Label : Type*} [Fintype Label]
    (first : Label→FirstSourceLabel) (seed : Label→Ideal O)
    (hinj : Function.Injective (fun j=>(first j,seed j)))
    (children : Label→Finset FirstSourceLabel)
    (cost : FirstSourceLabel→FirstSourceLabel→ℝ) :
    (∑j,∑v∈children j,cost (first j) v)=
      ∑l∈selectedLowFirstLabels first,∑D∈selectedLowFirstProjectors first seed l,
        ∑v∈selectedLowSupportedChildren first seed hinj children l D,cost l v := by
  rw [selected_low_first_cost_reindex first seed hinj children (fun j v=>cost (first j) v)]
  calc
    _=∑l : selectedLowFirstLabels first,∑D : selectedLowFirstProjectors first seed l.val,
        ∑v∈selectedLowSupportedChildren first seed hinj children l.val D.val,cost l.val v := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro D _
      rw [selected_low_supported_children_at first seed hinj children ⟨l,D⟩,
        (selected_low_pair_inverse_fields first seed hinj ⟨l,D⟩).1]
    _=_ := by
      rw [Finset.sum_coe_sort (selectedLowFirstLabels first)
        (fun l=>∑D : selectedLowFirstProjectors first seed l,
          ∑v∈selectedLowSupportedChildren first seed hinj children l D,cost l v)]
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_coe_sort (selectedLowFirstProjectors first seed l)
        (fun D=>∑v∈selectedLowSupportedChildren first seed hinj children l D,cost l v)

/-- Pay the selected first-pair fibers once. Supported second labels are
summed with their reciprocal norm; the first labels and projector ideals
are reindexed injectively, without an additional first-family count. -/
theorem actual_selected_low_supported_budget (B ε : ℝ) (hB : 0≤B) (hε : 0<ε) :
    ∃K₀ : ℝ,0<K₀ ∧ ∀{Label : Type*}[Fintype Label]
    (reflected second : Bool)(Z T A p exponent error : ℝ),
    2≤Z → 1≤T → p≤B → ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    ∀(first : Label→FirstSourceLabel)(seed : Label→Ideal O),
    Function.Injective (fun j=>(first j,seed j)) →
    (∀j,Supported (first j).1.1 ∧ Supported (first j).1.2) →
    (∀j,primeSupport (first j).1.1=primeSupport (first j).1.2) →
    (∀j,seed₀∣(first j).1.1 ∧ seed₀∣(first j).1.2) →
    (∀j,((first j).1.1.absNorm:ℝ)≤Z^B ∧ ((first j).1.2.absNorm:ℝ)≤Z^B) →
    (∀j,((commonRadical (first j).1.1 (first j).1.2).absNorm:ℝ)≤Z^p) →
    (∀j,lowGeometryExponent reflected Z A (first j)≤exponent) →
    (∀j,Squarefree (seed j)) →
    (∀j,T≤((seed j).absNorm:ℝ) ∧ ((seed j).absNorm:ℝ)<2*T) →
    ∀children : Label→Finset FirstSourceLabel,
    (∀j,∀v∈children j,Supported v.1.1 ∧ Supported v.1.2) →
    (∀j,∀v∈children j,primeSupport v.1.1=primeSupport v.1.2) →
    (∀j,∀v∈children j,seed j∣v.1.1 ∧ seed j∣v.1.2) →
    (∀j,∀v∈children j,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
    (∑j,∑v∈children j,Z^(lowGeometryExponent reflected Z A (first j)+error)/
      ((if second then v.1.2 else v.1.1).absNorm:ℝ))≤
      K₀*Z^(p+exponent+error+ε)/(seed₀.absNorm:ℝ) := by
  obtain ⟨K₀,hK₀,hbudget⟩ := actual_low_full_label_budget B ε hB hε
  refine ⟨K₀,hK₀,?_⟩
  intro Label _ reflected second Z T A p exponent error hZ hT hp seed₀ hs hs0 first seed hinj
    hsup heq hseed hnorm hrad hgeom hsq hdyad children hsup₂ heq₂ hseed₂ hnorm₂
  rw [selected_low_supported_sum first seed hinj children
    (fun l v=>Z^(lowGeometryExponent reflected Z A l+error)/
      ((if second then v.1.2 else v.1.1).absNorm:ℝ))]
  apply hbudget reflected second Z T A p exponent error hZ hT hp seed₀ hs hs0
    (selectedLowFirstLabels first)
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hsup j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact heq j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hseed j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hnorm j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hrad j
  · intro l hl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hl
    exact hgeom j
  · intro l _ D hD
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
    exact hsq j
  · intro l _ D hD
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
    exact hdyad j
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren,dite_eq_left ⟨hl,hD⟩] at hv
    exact hsup₂ _ v hv
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren,dite_eq_left ⟨hl,hD⟩] at hv
    exact heq₂ _ v hv
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren,dite_eq_left ⟨hl,hD⟩] at hv
    have hf := (selected_low_pair_inverse_fields first seed hinj ⟨⟨l,hl⟩,⟨D,hD⟩⟩).2
    simpa only [hf] using hseed₂ _ v hv
  · intro l hl D hD v hv
    rw [selectedLowSupportedChildren,dite_eq_left ⟨hl,hD⟩] at hv
    exact hnorm₂ _ v hv

/-- Literal selected first columns supply the occupied support equivalence
used by the finite supported low payment. -/
def actual_geometry_selected_first_pair_equiv {Label : Type*} [Fintype Label]
    (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (column : Label→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK bin (column j),
      (column j).2.1.val))) :=
  selectedLowFirstPairEquiv
    (fun j=>geometryFirstLabel s R seed K Z ξ hK bin (column j))
    (fun j=>(column j).2.1.val) hinj

omit [DecidableEq α] in
/-- The occupied-pair inverse requires an allocation only at its original
selected ideal, so the first coefficient remains genuinely nonzero. -/
theorem actual_geometry_selected_pair_allocation {Label : Type*} [Fintype Label]
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (K Z ξ : ℝ) (hK : 0<K)
    (bin : ℤ×(Fin 5→ℤ))
    (column : Label→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (hinj : Function.Injective (fun j=>(geometryFirstLabel s R seed K Z ξ hK bin (column j),
      (column j).2.1.val)))
    (alloc : (j : Label)→actualAllocations s.pools
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin (column j)))
    (hne : ∀j,frozenCoefficient (alloc j).val
      (geometryColumnIdeal reflected s R seed K Z ξ hK bin (column j)) R s.ν s.W s.P≠0) :
    ∀p : SelectedLowFirstPair
      (fun j=>geometryFirstLabel s R seed K Z ξ hK bin (column j))
      (fun j=>(column j).2.1.val),
      let j := (actual_geometry_selected_first_pair_equiv s R seed K Z ξ hK bin column hinj).symm p
      frozenCoefficient (alloc j).val
        (geometryColumnIdeal reflected s R seed K Z ξ hK bin (column j)) R s.ν s.W s.P≠0 := by
  intro p j
  exact hne j

/-- Actual selected second blocks pay their child volume and canonical
scalar before the supported reciprocal-norm sum. The common four-dyad
box is paid once, independently of the number of first labels. -/
theorem eventual_actual_selected_low_second_payment
    (N : ℕ) (lo εv : ℝ) (hlo : 0<lo) (hev : 0<εv) :
    ∀ᶠZ : ℝ in atTop,1<Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤N → lo≤s.lower →
    ∀{Label : Type}[Fintype Label]
    (reflected second : Bool) (first : Label→FirstSourceLabel),
    (∀l,Supported (first l).1.1 ∧ Supported (first l).1.2) →
    (∀l,primeSupport (first l).1.1=primeSupport (first l).1.2) →
    ∀(Rfirst : Ideal O)
      (alloc : (l : Label)→actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χ : Label→Character) (t : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let src := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χ l) (t l)
    ∀(R seed : Label→Ideal O)(K Tsec : Label→ℝ)(ξ M a reserve error εcommon Bnorm : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(src l).W₁ 0=0) → (∀l,(src l).W₂ 0=0) →
    0≤εcommon → (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (src l)≤Z^Bnorm) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (src l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀q∈rows,q.2.2.1∈inactiveSubsets q.2.1.val.val.1 q.2.1.val.val.2)
      (box : Finset (Fin 4→ℤ)),
    (∀q∈rows,actualSecondDyad (src q.1) (R q.1) (seed q.1)
      (K q.1) (Tsec q.1) Z ξ q.2∈box) →
    let pay := fun (l : Label)(v : FirstSourceLabel)=>
      Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve (first l)/volume (src l))*
        (normalizer v.1.1 v.1.2 v.2.val*((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
        Z^(secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
          (if reflected then (first l).1.2 else (first l).1.1)
          (if reflected then (first l).1.1 else (first l).1.2) v.1.1 v.1.2 v.2.val+a+error)
    (∑q : rows,pay q.val.1
      (actualSecondSupportedLabel (src q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)))≤
      (box.card:ℝ)*(∑l,∑v∈actualSecondLabels (src l) (R l) (seed l),
        Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)+
          error+εv+Bnorm*εcommon)/((if second then v.1.2 else v.1.1).absNorm:ℝ)) := by
  filter_upwards [eventual_actual_child_low_mass_payment N lo εv hlo hev] with Z hz
  refine ⟨hz.1,?_⟩
  intro ι _ s hn hs Label _ reflected second first hfirst heq Rfirst alloc χ t halloc
    src R seed K Tsec ξ M a reserve error εcommon Bnorm hseed hw₁ hw₂ hecommon hsource
    rows hU box hbox pay
  have hZ : 0<Z := zero_lt_one.trans hz.1
  have hgate (l : Label) (v : FirstSourceLabel)
      (hv : v∈actualSecondLabels (src l) (R l) (seed l)) :=
    actual_second_labels_gates (src l) (R l) (seed l) (hseed l) (hw₁ l) (hw₂ l) v hv
  have hpay (l : Label) (v : FirstSourceLabel)
      (hv : v∈actualSecondLabels (src l) (R l) (seed l)) :
      0≤pay l v := by
    dsimp only [pay]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hZ.le _) (div_nonneg
        (first_main_radius_pos reflected (Z^M) (volume s) Z ξ (3*a) reserve hZ (first l)).le
        (volume_pos (src l)).le))
      (mul_nonneg (normalizer_pos _ _ (hgate l v hv).1 _).le
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))) (Real.rpow_nonneg hZ.le _)
  have hdis := actual_second_joint_positive_disintegration
    (fun l=>liveIndices (alloc l).val) src R seed K Tsec Z ξ rows hU box hbox
    (fun l v _=>pay l v) (fun l v hv _ _=>hpay l v hv)
  apply hdis.trans
  have hpoint : ∀l,∀v∈actualSecondLabels (src l) (R l) (seed l),pay l v≤
      Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)+
        error+εv+Bnorm*εcommon)/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
    intro l v hv
    have hg := hgate l v hv
    have hnorm : ((if second then v.1.2 else v.1.1).absNorm:ℝ)≤Z^Bnorm := by
      cases second
      · exact hg.2.2.2.2.2.1.trans (hsource l)
      · exact hg.2.2.2.2.2.2.trans (hsource l)
    exact hz.2 s hn hs reflected second (first l) (hfirst l).1 (hfirst l).2 (heq l)
      Rfirst (alloc l) (χ l) (t l) (halloc l) v.1.1 v.1.2 hg.1 hg.2.1 v.2.val
      M a ξ reserve error εcommon Bnorm hecommon hnorm
  calc
    _≤∑_n∈box,∑l,∑v∈actualSecondLabels (src l) (R l) (seed l),
        Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)+
          error+εv+Bnorm*εcommon)/((if second then v.1.2 else v.1.1).absNorm:ℝ) := by
      apply Finset.sum_le_sum
      intro n _
      apply Finset.sum_le_sum
      intro l _
      exact Finset.sum_le_sum (hpoint l)
    _=_ := by simp

/-- The selected original second scalar sum is fully paid on its finite
supported first-label/projector fibers. -/
theorem eventual_actual_selected_low_second_paid
    (N : ℕ) (lo εv B ε : ℝ) (hlo : 0<lo) (hev : 0<εv) (hB : 0≤B) (hε : 0<ε) :
    ∃K₀ : ℝ,0<K₀ ∧
    ∀ᶠZ : ℝ in atTop,2≤Z ∧ ∀{ι : Type}[Fintype ι]
    (s : Input ι),Fintype.card ι≤N → lo≤s.lower →
    ∀{Label : Type}[Fintype Label]
    (reflected second : Bool) (first : Label→FirstSourceLabel),
    (∀l,Supported (first l).1.1 ∧ Supported (first l).1.2) →
    (∀l,primeSupport (first l).1.1=primeSupport (first l).1.2) →
    ∀(Rfirst : Ideal O)
      (alloc : (l : Label)→actualAllocations s.pools
        (if reflected then (first l).1.2 else (first l).1.1))
      (χ : Label→Character) (t : Label→ℝ),
    (∀l,frozenCoefficient (alloc l).val
      (if reflected then (first l).1.2 else (first l).1.1) Rfirst s.ν s.W s.P≠0) →
    let src := fun l=>child s (if reflected then (first l).1.2 else (first l).1.1)
      Rfirst (alloc l) (χ l) (t l)
    ∀(R seed : Label→Ideal O)(K Tsec : Label→ℝ)(ξ M a reserve error εcommon : ℝ),
    (∀l,Squarefree (seed l)) → (∀l,(src l).W₁ 0=0) → (∀l,(src l).W₂ 0=0) →
    0≤εcommon → (∀l,CenteredMomentOriginalCommonHarmonic.sourceRadius (src l)≤Z^B) →
    ∀(T p exponent : ℝ),1≤T → p≤B →
    ∀seed₀ : Ideal O,Squarefree seed₀ → seed₀≠0 →
    Function.Injective (fun l=>(first l,seed l)) →
    (∀l,seed₀∣(first l).1.1 ∧ seed₀∣(first l).1.2) →
    (∀l,((first l).1.1.absNorm:ℝ)≤Z^B ∧ ((first l).1.2.absNorm:ℝ)≤Z^B) →
    (∀l,((commonRadical (first l).1.1 (first l).1.2).absNorm:ℝ)≤Z^p) →
    (∀l,lowGeometryExponent reflected Z (Real.logb Z (volume s)) (first l)≤exponent) →
    (∀l,T≤((seed l).absNorm:ℝ) ∧ ((seed l).absNorm:ℝ)<2*T) →
    ∀(rows : Finset ((l : Label)×ActualSecondBlockIndex (src l) (R l) (seed l)
      (K l) (Tsec l) Z ξ))
      (hU : ∀q∈rows,q.2.2.1∈inactiveSubsets q.2.1.val.val.1 q.2.1.val.val.2)
      (box : Finset (Fin 4→ℤ)),
    (∀q∈rows,actualSecondDyad (src q.1) (R q.1) (seed q.1)
      (K q.1) (Tsec q.1) Z ξ q.2∈box) →
    let pay := fun (l : Label)(v : FirstSourceLabel)=>
      Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve (first l)/volume (src l))*
        (normalizer v.1.1 v.1.2 v.2.val*((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
        Z^(secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
          (if reflected then (first l).1.2 else (first l).1.1)
          (if reflected then (first l).1.1 else (first l).1.2) v.1.1 v.1.2 v.2.val+a+error)
    (∑q : rows,pay q.val.1
      (actualSecondSupportedLabel (src q.val.1) (R q.val.1) (seed q.val.1)
        (K q.val.1) (Tsec q.val.1) Z ξ q.val.2 (hU q.val q.property)))≤
      (box.card:ℝ)*(K₀*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed₀.absNorm:ℝ)) := by
  let hbase := actual_selected_low_supported_budget.{0} B ε hB hε
  let K₀ := Classical.choose hbase
  let hlabels := Classical.choose_spec hbase
  refine ⟨K₀,hlabels.1,?_⟩
  filter_upwards [eventual_actual_selected_low_second_payment N lo εv hlo hev,
    eventually_ge_atTop (2:ℝ)] with Z hz hZ2
  refine ⟨hZ2,?_⟩
  intro ι _ s hn hs Label _ reflected second first hfirst heq Rfirst alloc χ t halloc
    src R seed K Tsec ξ M a reserve error εcommon hseed hw₁ hw₂ hecommon hsource
    T p exponent hT hp seed₀ hs₀ hs₀0 hinj hfirstseed hfirstnorm hrad hgeom hdyad
    rows hU box hbox pay
  have hpaid := hz.2 s hn hs reflected second first hfirst heq Rfirst alloc χ t halloc
    R seed K Tsec ξ M a reserve error εcommon B hseed hw₁ hw₂ hecommon hsource
    rows hU box hbox
  have hgate (l : Label) (v : FirstSourceLabel)
      (hv : v∈actualSecondLabels (src l) (R l) (seed l)) :=
    actual_second_labels_gates (src l) (R l) (seed l) (hseed l) (hw₁ l) (hw₂ l) v hv
  have hbound := hlabels.2 (Label:=Label) reflected second Z T (Real.logb Z (volume s)) p exponent
    (error+εv+B*εcommon) hZ2 hT hp seed₀ hs₀ hs₀0 first seed hinj hfirst heq
    hfirstseed hfirstnorm hrad hgeom hseed hdyad
    (fun l=>actualSecondLabels (src l) (R l) (seed l))
    (fun l v hv=>⟨(hgate l v hv).1,(hgate l v hv).2.1⟩)
    (fun l v hv=>(hgate l v hv).2.2.1)
    (fun l v hv=>⟨(hgate l v hv).2.2.2.1,(hgate l v hv).2.2.2.2.1⟩)
    (fun l v hv=>⟨(hgate l v hv).2.2.2.2.2.1.trans (hsource l),
      (hgate l v hv).2.2.2.2.2.2.trans (hsource l)⟩)
  have hexp : p+exponent+(error+εv+B*εcommon)+ε=
      p+exponent+error+εv+B*εcommon+ε := by ring
  rw [hexp] at hbound
  apply hpaid.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg box.card)
  simpa only [src,K₀,add_assoc] using hbound

/-- The actual second-projector union pays the low theorem's shell-scale
factor once, uniformly before all moving block labels and allocations. -/
theorem actual_second_low_weighted_shells (N : ℕ)(U εshell ε : ℝ)
    (hU : 0≤U)(heshell : 0≤εshell)(he : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀{Label : Type*}[Fintype Label](d : Label→SecondInputDatum α),
    (∀l,Fintype.card (d l).slots≤N) →
    (∀l i I,I∈(d l).input.pools i→(I.absNorm:ℝ)≤Z^U) →
    (∑n∈selectedShells (sharedProjectors (fun l=>(d l).block.divisors)),
      (2*dyadicScale n)^(3*εshell))≤
        C*Z^(ε+3*(((N:ℝ)+2)*U)*εshell) := by
  obtain ⟨C₀,hC₀,hbound⟩ := actual_second_projector_shell_subpower (α:=α) N U ε hU he
  refine ⟨C₀*(2:ℝ)^(3*εshell),mul_pos hC₀ (Real.rpow_pos_of_pos (by norm_num) _),?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro Label _ d hN hpool
  let L := ((N:ℝ)+2)*U
  let shells := selectedShells (sharedProjectors (fun l=>(d l).block.divisors))
  have hZ : 0<Z := zero_lt_one.trans hz.1
  have hpower : 0≤3*εshell := mul_nonneg (by norm_num) heshell
  have hscale (n : ℤ)(hn : n∈shells) : dyadicScale n≤Z^L :=
    (shared_projector_shell_scale (fun l=>(d l).block.divisors) Z L
      (fun l D hD=>(second_datum_projector_cap (d l) N Z U (hN l) hz.1.le hU
        (hpool l) D hD).2) n hn).2
  have hp (n : ℤ)(hn : n∈shells) :
      (2*dyadicScale n)^(3*εshell)≤(2:ℝ)^(3*εshell)*Z^(3*L*εshell) := by
    calc
      _≤(2*Z^L)^(3*εshell) := Real.rpow_le_rpow (mul_nonneg (by norm_num) (dyadicScale_pos n).le)
        (mul_le_mul_of_nonneg_left (hscale n hn) (by norm_num)) hpower
      _=_ := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hZ.le _),
          ←Real.rpow_mul hZ.le]
        congr 1
        ring
  calc
    _≤∑_n∈shells,(2:ℝ)^(3*εshell)*Z^(3*L*εshell) := Finset.sum_le_sum hp
    _=(shells.card:ℝ)*((2:ℝ)^(3*εshell)*Z^(3*L*εshell)) := by simp
    _≤(C₀*Z^ε)*((2:ℝ)^(3*εshell)*Z^(3*L*εshell)) :=
      mul_le_mul_of_nonneg_right (hz.2 d hN hpool) (by positivity)
    _=_ := by dsimp only [L]; rw [Real.rpow_add hZ]; ring

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_selected_low_physical_family_columns
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_selected_low_physical_columns

#print axioms OAI.SevenEighths.Cycle63InitialMass.selected_low_first_pair_bijective
#print axioms OAI.SevenEighths.Cycle63InitialMass.selected_low_first_cost_reindex
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_selected_pair_allocation

#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_selected_low_second_payment

#print axioms OAI.SevenEighths.Cycle63InitialMass.selected_low_supported_sum

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_selected_low_supported_budget

#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_selected_low_second_paid

#print axioms OAI.SevenEighths.Cycle63InitialMass.selected_low_pair_inverse_fields
#print axioms OAI.SevenEighths.Cycle63InitialMass.selected_low_supported_children_at

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_second_low_weighted_shells
