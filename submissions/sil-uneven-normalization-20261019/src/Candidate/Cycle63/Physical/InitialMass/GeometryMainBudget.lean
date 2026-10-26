import Candidate.Cycle63.Physical.InitialMass.SecondChildLowPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryLowColumn
import Candidate.Cycle63.Physical.InitialMass.GeometryZeroPartition

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryLowPayment. -/
section

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical
open CenteredMomentFirstAmplificationChoice CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open Cycle63Moment Cycle63FinalCapacity CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput CenteredMomentSourceLiveColumn
local notation "O" => HeckeFamily.O

/-- Actual child scalar costs are summed over the full first/second label
and projector shell, with no squarefree restriction on either ideal label. -/
theorem eventual_actual_geometry_low_label_payment (N : ℕ) (lo εv B ε : ℝ)
    (hlo : 0<lo) (hev : 0<εv) (hB : 0≤B) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤N → lo≤s.lower →
      ∀(reflected second : Bool)(T p exponent error εcommon M a ξ reserve : ℝ),
      0≤εcommon → 1≤T → p≤B → ∀seed : Ideal O,Squarefree seed → seed≠0 →
      ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤Z^p) →
      (∀l∈labels,lowGeometryExponent reflected Z (Real.logb Z (volume s)) l≤exponent) →
      ∀(Ds : FirstSourceLabel→Finset (Ideal O))
        (children : FirstSourceLabel→Ideal O→Finset FirstSourceLabel),
      (∀l∈labels,∀D∈Ds l,Squarefree D) →
      (∀l∈labels,∀D∈Ds l,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,Supported v.1.1 ∧ Supported v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,primeSupport v.1.1=primeSupport v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,D∣v.1.1 ∧ D∣v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      ∀Rfirst : Ideal O,
      ∀alloc : (l : FirstSourceLabel)→(D : Ideal O)→(v : FirstSourceLabel)→
        actualAllocations s.pools (if reflected then l.1.2 else l.1.1),
      ∀(χ : FirstSourceLabel→Ideal O→FirstSourceLabel→Character)
        (t : FirstSourceLabel→Ideal O→FirstSourceLabel→ℝ),
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,
        frozenCoefficient (alloc l D v).val (if reflected then l.1.2 else l.1.1)
          Rfirst s.ν s.W s.P≠0) →
      (∑l∈labels,∑D∈Ds l,∑v∈children l D,
        Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l/
          volume (child s (if reflected then l.1.2 else l.1.1) Rfirst
            (alloc l D v) (χ l D v) (t l D v)))*
          (normalizer v.1.1 v.1.2 v.2.val*((if second then v.1.2 else v.1.1).absNorm:ℝ)^(εcommon-1))*
          Z^(Cycle63FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
            (if reflected then l.1.2 else l.1.1) (if reflected then l.1.1 else l.1.2)
            v.1.1 v.1.2 v.2.val+a+error))≤
        K*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ) := by
  obtain ⟨K,hK,hlabels⟩ := actual_low_full_label_budget B ε hB hε
  refine ⟨K,hK,?_⟩
  filter_upwards [eventual_actual_child_low_mass_payment N lo εv hlo hev,
    eventually_ge_atTop (2:ℝ)] with Z hz hZ2
  refine ⟨hZ2,?_⟩
  intro ι _ s hcard hlow reflected second T p exponent error εcommon M a ξ reserve
    hecommon hT hp seed hs hs0 labels hsup heq hseed hnorm hrad hgeom
    Ds children hDs hdyad hsup₂ heq₂ hseed₂ hnorm₂ Rfirst alloc χ t halloc
  have hbudget := hlabels reflected second Z T (Real.logb Z (volume s)) p exponent
    (error+εv+B*εcommon) hZ2 hT hp seed hs hs0 labels hsup heq hseed hnorm hrad hgeom
    Ds children hDs hdyad hsup₂ heq₂ hseed₂ hnorm₂
  have hexp : p+exponent+(error+εv+B*εcommon)+ε=p+exponent+error+εv+B*εcommon+ε := by ring
  rw [hexp] at hbudget
  apply le_trans _ hbudget
  apply Finset.sum_le_sum
  intro l hl
  apply Finset.sum_le_sum
  intro D hD
  apply Finset.sum_le_sum
  intro v hv
  have hh := hz.2 s hcard hlow reflected second l (hsup l hl).1 (hsup l hl).2
    (heq l hl) Rfirst (alloc l D v) (χ l D v) (t l D v) (halloc l hl D hD v hv)
    v.1.1 v.1.2 (hsup₂ l hl D hD v hv).1 (hsup₂ l hl D hD v hv).2 v.2.val
    M a ξ reserve error εcommon B hecommon (by
      cases second
      · exact (hnorm₂ l hl D hD v hv).1
      · exact (hnorm₂ l hl D hD v hv).2)
  simpa only [add_assoc] using hh

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_geometry_low_label_payment
end

/- Original module: Candidate.Cycle63.Physical.InitialMass.GeometryMainBudget. -/
section

set_option autoImplicit false
set_option maxHeartbeats 250000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
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
open CenteredMomentRankinRadical CenteredMomentSecondCanonicalScalar
open HeckeDetectorZeros LocalMoment
open Cycle63FinalLow
open Cycle63Moment.LowBranch Cycle63FinalNatural Cycle63FinalCapacity
open CenteredMomentDivisorExtraction
open CenteredMomentEnergyAllocatedProfiles CenteredMomentAllocatedChildCapacity Cycle63FinalProfiles
local notation "O" => HeckeFamily.O
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]
local instance geometryMainBudgetSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _
attribute [local irreducible] geometryLowActualChain geometryLowActualGeometry geometryLowSecondDatum


variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- Complete low columns on literal first and second source coordinates.
The selected second common allocation is fixed before the retained row sum. -/
def actual_geometry_main_low_columns
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
    (εshell : ℝ) (heshell : 0<εshell) :=
  let hbase := actual_geometry_low_family_columns.{u,v} (α:=α) M H hH
    W A B a b Bmask L lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
    Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
    ηseed bs εwidth εpad Mmin hbs hew hep hmin εshell heshell
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


/-- The genuine detector supplies the low gate on every nonzero radial term
in a selected low bin. -/
theorem actual_geometry_main_low_fiber_admission {κ : Type*}
    (rows : Finset κ) {Z Bmask bΦ : ℝ} (st : rows→NaturalState Z Bmask bΦ)
    (η₀ : Character) (hQM : ∀u,(st u).fixedModulus≤M)
    (hQη : ∀u,(st u).fixedModulus≤η₀.modulus)
    (z : rows→O) (hz : ∀u,(st u).radial.keep (z u))
    (e T : ℝ) (he : 0<e) (hT : 2<T)
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (p : BufferIndex e) (hp : bufferValue e p<21/25) :
    ∀u∈rows.attach.filter (fun u=>
      geometryZeroSelector M H hH rows st η₀ hQM hQη z hz e T he hT hβlo hβhi u=p ∧
      (st u).radial.profile (‖eisEmbedding (z u)‖^2/(st u).radial.scale)≠0),
      (st u).radial.keep (z u) ∧
        ActualLow M H hH (st u) η₀ (hQM u) (hQη u)
          (21/25) e (3*(p.1.val+1:ℕ)*T) (z u) := by
  intro u hu
  obtain ⟨_,hu⟩ := Finset.mem_filter.mp hu
  have h := geometry_zero_selector_spec M H hH rows st η₀ hQM hQη z hz e T he hT hβlo hβhi u
  rw [hu.1] at h
  obtain ⟨_,_,_,_,_,_,_,_,hlow,_⟩ := h
  exact ⟨hz u,hlow hp hu.2⟩

/-- Removing radial zero terms preserves every weighted source coordinate;
no estimate or label cardinality is used. -/
theorem actual_geometry_main_low_fiber_zero_terms {κ : Type*}
    (rows : Finset κ) {Z Bmask bΦ : ℝ} (st : rows→NaturalState Z Bmask bΦ)
    (z : rows→O) (e : ℝ) (select : rows→BufferIndex e) (p : BufferIndex e)
    (weight cost : rows→ℝ) (hw : ∀u,0≤weight u)
    (hmajorant : ∀u,weight u≤
      ((st u).radial.profile (‖eisEmbedding (z u)‖^2/(st u).radial.scale)).re) :
    (∑u∈rows.attach.filter (fun u=>select u=p),weight u*cost u)=
      ∑u∈rows.attach.filter (fun u=>select u=p ∧
        (st u).radial.profile (‖eisEmbedding (z u)‖^2/(st u).radial.scale)≠0),
        weight u*cost u := by
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hs : select u=p
  · by_cases hzero : (st u).radial.profile (‖eisEmbedding (z u)‖^2/(st u).radial.scale)=0
    · have hm := hmajorant u
      rw [hzero] at hm
      have hwzero : weight u=0 := le_antisymm (by simpa using hm) (hw u)
      simp [hs,hzero,hwzero]
    · simp [hs,hzero]
  · simp [hs]

/-- Scalar payment only asks for allocations on the actual finite supported labels. -/
theorem eventual_actual_geometry_low_supported_payment (N : ℕ) (lo εv B ε : ℝ)
    (hlo : 0<lo) (hev : 0<εv) (hB : 0≤B) (hε : 0<ε) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
      ∀{ι : Type}[Fintype ι](s : Input ι),Fintype.card ι≤N → lo≤s.lower →
      ∀(reflected second : Bool)(T p exponent error εcommon M a ξ reserve : ℝ),
      0≤εcommon → 1≤T → p≤B → ∀seed : Ideal O,Squarefree seed → seed≠0 →
      ∀labels : Finset FirstSourceLabel,
      (∀l∈labels,Supported l.1.1 ∧ Supported l.1.2) →
      (∀l∈labels,primeSupport l.1.1=primeSupport l.1.2) →
      (∀l∈labels,seed∣l.1.1 ∧ seed∣l.1.2) →
      (∀l∈labels,(l.1.1.absNorm:ℝ)≤Z^B ∧ (l.1.2.absNorm:ℝ)≤Z^B) →
      (∀l∈labels,((commonRadical l.1.1 l.1.2).absNorm:ℝ)≤Z^p) →
      (∀l∈labels,lowGeometryExponent reflected Z (Real.logb Z (volume s)) l≤exponent) →
      ∀(Ds : FirstSourceLabel→Finset (Ideal O))
        (children : FirstSourceLabel→Ideal O→Finset FirstSourceLabel),
      (∀l∈labels,∀D∈Ds l,Squarefree D) →
      (∀l∈labels,∀D∈Ds l,T≤(D.absNorm:ℝ) ∧ (D.absNorm:ℝ)<2*T) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,Supported v.1.1 ∧ Supported v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,primeSupport v.1.1=primeSupport v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,D∣v.1.1 ∧ D∣v.1.2) →
      (∀l∈labels,∀D∈Ds l,∀v∈children l D,(v.1.1.absNorm:ℝ)≤Z^B ∧ (v.1.2.absNorm:ℝ)≤Z^B) →
      ∀Rfirst : Ideal O,
      ∀alloc : (l : labels)→(D : Ds l.val)→(v : children l.val D.val)→
        actualAllocations s.pools (if reflected then l.val.1.2 else l.val.1.1),
      ∀(χ : (l : labels)→(D : Ds l.val)→children l.val D.val→Character)
        (t : (l : labels)→(D : Ds l.val)→children l.val D.val→ℝ),
      (∀(l : labels)(D : Ds l.val)(v : children l.val D.val),
        frozenCoefficient (alloc l D v).val (if reflected then l.val.1.2 else l.val.1.1)
          Rfirst s.ν s.W s.P≠0) →
      (∑l : labels,∑D : Ds l.val,∑v : children l.val D.val,
        Z^(-a)*(firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve l.val/
          volume (child s (if reflected then l.val.1.2 else l.val.1.1) Rfirst
            (alloc l D v) (χ l D v) (t l D v)))*
          (normalizer v.val.1.1 v.val.1.2 v.val.2.val*
            ((if second then v.val.1.2 else v.val.1.1).absNorm:ℝ)^(εcommon-1))*
          Z^(Cycle63FinalCapacity.secondNominal M Z a (frequencyLoss Z 32 ξ+reserve)
            (if reflected then l.val.1.2 else l.val.1.1) (if reflected then l.val.1.1 else l.val.1.2)
            v.val.1.1 v.val.1.2 v.val.2.val+a+error))≤
        K*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ) := by
  obtain ⟨K,hK,hlabels⟩ := actual_low_full_label_budget B ε hB hε
  refine ⟨K,hK,?_⟩
  filter_upwards [eventual_actual_child_low_mass_payment N lo εv hlo hev,
    eventually_ge_atTop (2:ℝ)] with Z hz hZ2
  refine ⟨hZ2,?_⟩
  intro ι _ s hcard hlow reflected second T p exponent error εcommon M a ξ reserve
    hecommon hT hp seed hs hs0 labels hsup heq hseed hnorm hrad hgeom
    Ds children hDs hdyad hsup₂ heq₂ hseed₂ hnorm₂ Rfirst alloc χ t halloc
  have hbudget := hlabels reflected second Z T (Real.logb Z (volume s)) p exponent
    (error+εv+B*εcommon) hZ2 hT hp seed hs hs0 labels hsup heq hseed hnorm hrad hgeom
    Ds children hDs hdyad hsup₂ heq₂ hseed₂ hnorm₂
  have hexp : p+exponent+(error+εv+B*εcommon)+ε=p+exponent+error+εv+B*εcommon+ε := by ring
  rw [hexp] at hbudget
  have hbudget' :
      (∑l : labels,∑D : Ds l.val,∑v : children l.val D.val,
        Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) l.val+
          error+εv+B*εcommon)/((if second then v.val.1.2 else v.val.1.1).absNorm:ℝ))≤
        K*Z^(p+exponent+error+εv+B*εcommon+ε)/(seed.absNorm:ℝ) := by
    let F := fun (l v : FirstSourceLabel)=>
      Z^(lowGeometryExponent reflected Z (Real.logb Z (volume s)) l+
        error+εv+B*εcommon)/((if second then v.1.2 else v.1.1).absNorm:ℝ)
    have hsum : (∑l : labels,∑D : Ds l.val,∑v : children l.val D.val,F l.val v.val)=
        ∑l∈labels,∑D∈Ds l,∑v∈children l D,F l v := by
      rw [Finset.sum_coe_sort labels (fun l=>∑D : Ds l,∑v : children l D.val,F l v.val)]
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.sum_coe_sort (Ds l) (fun D=>∑v : children l D,F l v.val)]
      apply Finset.sum_congr rfl
      intro D hD
      exact Finset.sum_coe_sort (children l D) (fun v=>F l v)
    change (∑l : labels,∑D : Ds l.val,∑v : children l.val D.val,F l.val v.val)≤_
    rw [hsum]
    simpa only [F,add_assoc] using hbudget
  apply le_trans _ hbudget'
  apply Finset.sum_le_sum
  intro l _
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro v _
  have hh := hz.2 s hcard hlow reflected second l.val (hsup l.val l.property).1
    (hsup l.val l.property).2 (heq l.val l.property) Rfirst (alloc l D v) (χ l D v) (t l D v)
    (halloc l D v) v.val.1.1 v.val.1.2
    (hsup₂ l.val l.property D.val D.property v.val v.property).1
    (hsup₂ l.val l.property D.val D.property v.val v.property).2 v.val.2.val
    M a ξ reserve error εcommon B hecommon (by
      cases second
      · exact (hnorm₂ l.val l.property D.val D.property v.val v.property).1
      · exact (hnorm₂ l.val l.property D.val D.property v.val v.property).2)
  simpa only [add_assoc] using hh

end
end OAI.SevenEighths.Cycle63InitialMass
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_main_low_columns

#print axioms OAI.SevenEighths.Cycle63InitialMass.eventual_actual_geometry_low_supported_payment

#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_main_low_fiber_admission
#print axioms OAI.SevenEighths.Cycle63InitialMass.actual_geometry_main_low_fiber_zero_terms
end
