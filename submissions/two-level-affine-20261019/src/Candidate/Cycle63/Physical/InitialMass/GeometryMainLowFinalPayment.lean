/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryMainLowPhysicalPayment
import Candidate.Cycle25.Energy.Endpoint

set_option autoImplicit false
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 10000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve
open CenteredMomentCommonAllocationSum CenteredMomentAmplificationChildInput
open CenteredMomentCommonRadialData CenteredMomentSourceLiveColumn
open CenteredMomentWholeDivisorShell CenteredMomentSectorLocalization
open CenteredMomentSourceRow LocalMoment CenteredMomentFirstDiscardedEnergy
variable {α Label : Type*} [Fintype α] [DecidableEq α] [Fintype Label]
local instance mainLowFinalSumDecidable : DecidableEq (α⊕Fin 2) := Classical.decEq _

set_option maxHeartbeats 10000 in
private theorem filtered_first_shell_sum {ι J : Type*} [Fintype J]
    {src : ι→FirstBlockSource}(column : J→FirstColumnIndex src)
    (hs : ∀l,Squarefree (column l).2.1.val)
    (Block : J→Type*)[∀l,Fintype (Block l)]
    (rows : Finset ((l : J)×Block l))(f : ((l : J)×Block l)→ℝ) :
    (∑q∈rows,f q)=∑n∈selectedShells (selectedFirstProjectors column),
      ∑q∈(Finset.univ.filter (fun q : (l : SelectedFirstShell column n)×Block l.val=>
        (⟨q.1.val,q.2⟩ : (l : J)×Block l)∈rows)),f ⟨q.1.val,q.2⟩ := by
  have heq : rows=Finset.univ.filter (fun q=>q∈rows) := by ext; simp
  calc
    _=∑l,∑q : Block l,if (⟨l,q⟩ : (l : J)×Block l)∈rows then f ⟨l,q⟩ else 0 := by
      nth_rw 1 [heq]
      rw [Finset.sum_filter,Fintype.sum_sigma]
    _=∑n∈selectedShells (selectedFirstProjectors column),
      ∑l : SelectedFirstShell column n,∑q : Block l.val,
        if (⟨l.val,q⟩ : (l : J)×Block l)∈rows then f ⟨l.val,q⟩ else 0 :=
      selected_first_shell_sum column hs _
    _=_ := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_filter,Fintype.sum_sigma]

private theorem filtered_first_shell_subtype_sum {ι J : Type*} [Fintype J]
    {src : ι→FirstBlockSource}(column : J→FirstColumnIndex src)
    (hs : ∀l,Squarefree (column l).2.1.val)
    (Block : J→Type*)[∀l,Fintype (Block l)]
    (rows : Finset ((l : J)×Block l))(cost : rows→ℝ) :
    (∑q : rows,cost q)=∑n∈selectedShells (selectedFirstProjectors column),
      ∑q : (Finset.univ.filter (fun q : (l : SelectedFirstShell column n)×Block l.val=>
        (⟨q.1.val,q.2⟩ : (l : J)×Block l)∈rows)),
        cost ⟨⟨q.val.1.val,q.val.2⟩,(Finset.mem_filter.mp q.property).2⟩ := by
  let f : ((l : J)×Block l)→ℝ := fun q=>if h : q∈rows then cost ⟨q,h⟩ else 0
  have hg := filtered_first_shell_sum column hs Block rows f
  have hl : (∑q∈rows,f q)=∑q : rows,cost q := by
    rw [←Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [f,dite_eq_left q.property]
  rw [hl] at hg
  rw [hg]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [←Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [f,dite_eq_left (Finset.mem_filter.mp q.property).2]

variable (reflected : Bool) (s : Input α) (R seed : Ideal O)
variable (Z Mrow amp ξ reserve b t : ℝ) (N : ℕ) (hZ : 1<Z)
variable (key : ℤ×(Fin 5→ℤ)) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
variable (firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ
  (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key)

/-- A named type boundary keeps the actual second-source family intact. -/
def MainLowFinalSecondIndex (l : Label) : Type :=
  GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key (firstIndex l)

local instance mainLowFinalBlockFintype (l : Label) :
    Fintype (MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l) :=
  inferInstanceAs (Fintype (GeometryLowSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    (firstIndex l)))

/-- Pull the actual complete second index back to one shell of the common
FIRST projector union. The second allocation and all four dyads are kept. -/
def mainLowShellIndex (n : ℤ)
    (q : (l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n)×
      MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l.val) :
    (l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l := ⟨q.1.val,q.2⟩

/-- ORIGINAL full-nonzero membership is tested before ordinary restriction
and is pulled back exactly, rather than replaced by restricted nonzeroness. -/
def mainLowShellRows
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l)) (n : ℤ) :
    Finset ((l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n)×
      MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l.val) :=
  Finset.univ.filter (fun q=>mainLowShellIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    firstIndex n q∈rows)

def mainLowShellRowOriginal
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l)) (n : ℤ)
    (q : mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n) : rows :=
  ⟨mainLowShellIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex n q.val,
    (Finset.mem_filter.mp q.property).2⟩

attribute [local irreducible] geometryMainNonzeroBlocks geometryLowSecondDatum

set_option maxHeartbeats 320000 in
theorem main_low_shell_original_gate
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l))
    (hOriginal : ∀q∈rows,
      (⟨firstIndex q.1,q.2⟩ : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t
        N hZ key)∈geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂)
    (n : ℤ) :
    ∀q∈mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n,
      (⟨firstIndex q.1.val,q.2⟩ : GeometryMainSecondIndex reflected s R seed Z Mrow amp ξ reserve b t
        N hZ key)∈geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve b t N hZ key hz₁ hz₂ := by
  intro q hq
  exact hOriginal _ (Finset.mem_filter.mp hq).2

attribute [local irreducible] MainLowFinalSecondIndex

omit [DecidableEq α] in
/-- The same complete filter identity for the original cost's subtype. -/
theorem main_low_shell_complete_subtype_sum
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t
      N hZ key firstIndex l))
    (hs : ∀l,Squarefree (firstIndex l).1.val.2.1.val)(cost : rows→ℝ) :
    (∑q : rows,cost q)=∑n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val)),
      ∑q : mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n,
        cost (mainLowShellRowOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key
          firstIndex rows n q) := by
  exact filtered_first_shell_subtype_sum (fun l=>(firstIndex l).1.val) hs
    (fun l=>MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex l)
    rows cost

variable [Cycle63.AffineLedger] in
/-- The literal complete fixed-ray physical cost follows the same first
shell disintegration, with every residual divisor and signed source row. -/
theorem main_low_shell_fixed_ray_cost
    (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed Z Mrow amp ξ reserve b t
      N hZ key firstIndex l))
    (hs : ∀l,Squarefree (firstIndex l).1.val.2.1.val)
    (Ncost : ℕ)(lo ap : ℝ)(second : Bool)(d : rows→SecondInputDatum α)
    (coefficient : rows→ℝ)(t₀ u : ℝ)(χ ψ : RayFourExpansion.RayCharacter){e : ℝ}
    (select : (r : rows)→mainLowSourceRows second (d r) (fun _=>True)→BufferIndex e) :
    mainLowFixedRayPhysicalCost Ncost lo ap second d coefficient t₀ u χ ψ select=
      ∑n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val)),
        mainLowFixedRayPhysicalCost Ncost lo ap second
          (fun q : mainLowShellRows reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n=>
            d (mainLowShellRowOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n q))
          (fun q=>coefficient (mainLowShellRowOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n q))
          t₀ u χ ψ
          (fun q=>select (mainLowShellRowOriginal reflected s R seed Z Mrow amp ξ reserve b t N hZ key firstIndex rows n q)) := by
  unfold mainLowFixedRayPhysicalCost
  exact main_low_shell_complete_subtype_sum reflected s R seed Z Mrow amp ξ reserve b t N hZ key
    firstIndex rows hs _

include hz₁ hz₂ in
/-- Actual original caps bound the radical bin endpoint on every occupied
common first shell. The selected allocation and its injection are retained. -/
theorem actual_main_low_final_shell_first_gates
    (Bmass Bnorm : ℝ)(hZ2 : 2≤Z)(hs : Squarefree seed)
    (hsource : CenteredMomentOriginalCommonHarmonic.sourceRadius s≤Z^Bmass)
    (hBnorm : Bmass+1≤Bnorm)
    (hinj : Function.Injective (fun l=>(geometryFirstLabel s R seed (Z^Mrow) Z ξ
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val,
      (firstIndex l).1.val.2.1.val)))
    (hf : ∀l,frozenCoefficient (firstIndex l).2.val
      (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l).1.val)
      R s.ν s.W s.P≠0)
    (n : ℤ)(hn : n∈selectedShells (selectedFirstProjectors (fun l=>(firstIndex l).1.val))) :
    Function.Injective (fun l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n=>
      (geometryFirstLabel s R seed (Z^Mrow) Z ξ
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l.val).1.val,
        (firstIndex l.val).1.val.2.1.val)) ∧
    (∀l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n,
      frozenCoefficient (firstIndex l.val).2.val
        (geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key (firstIndex l.val).1.val)
        R s.ν s.W s.P≠0) ∧
    (∀l : SelectedFirstShell (fun l=>(firstIndex l).1.val) n,
      dyadicScale n≤((firstIndex l.val).1.val.2.1.val.absNorm:ℝ) ∧
        ((firstIndex l.val).1.val.2.1.val.absNorm:ℝ)<2*dyadicScale n) ∧
    ((key.2 2:ℝ)+1)*Real.logb Z 2≤Bnorm := by
  have hg:=actual_main_low_first_shell_restriction reflected s R seed (Z^Mrow) Z ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) key firstIndex hinj hf n
  have hp:=actual_main_low_first_shell_scalar_gates reflected s R seed (Z^Mrow) Z ξ Bmass
    (Real.logb Z (volume s)) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    hZ2 hs hz₁ hz₂ hsource key firstIndex n hn
  exact ⟨hg.1,hg.2.1,hg.2.2,hp.1.trans hBnorm⟩

attribute [local semireducible] MainLowFinalSecondIndex

section SavedKernel
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

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ)(hH : RayOrthogonality.globalUnits M≤H)
open Set HeckePrimeAnnular Cycle63Moment CenteredMomentSlotRatios
/-- A structural common-projector count, uniform over the original slot type. -/
def MainLowFirstShellCountAt (N : ℕ) (U εfirst Cfirst Z : ℝ) : Prop :=
  ∀{ι Label : Type}[Fintype ι][DecidableEq ι][Fintype Label]
    (s : Input ι),Fintype.card ι≤N →
    (∀i I,I∈s.pools i→(I.absNorm:ℝ)≤Z^U) →
    ∀(R seed : Ideal O)(K ξ : ℝ)(hK : 0<K)(bin : ℤ×(Fin 5→ℤ))
      (column : Label→FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)),
    ((selectedShells (selectedFirstProjectors column)).card:ℝ)≤Cfirst*Z^εfirst

variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 100000 in
set_option linter.unusedVariables false in
set_option linter.defProp false in
def MainLowFinalPhysicalSpec {α : Type} [Fintype α] [DecidableEq α]
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
    (εfirst Cfirst : ℝ)(degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
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
          (rows : Finset ((l : Label)×MainLowFinalSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin firstIndex l))
          (hOriginal : ∀r∈rows,
            (⟨firstIndex r.1,r.2⟩ : GeometryMainSecondIndex reflected s R seed₀ Z Mrow amp ξ reserve bs t
              (Fintype.card α) hZ bin)∈geometryMainNonzeroBlocks reflected s R seed₀ Z Mrow amp ξ reserve bs t
                (Fintype.card α) hZ bin hw₁ hw₂)
          (hU : ∀r∈rows,ActualSecondBlockIndex.IsInactive r.2)
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
        let ray:=if second then ψ⁻¹ else χ
        let st:=fun r : rows=>retainedState Z Bmask hZ ((g r).datum.τ ray) (internalQ Q η₀)
          ((q r).R₂*(q r).E₂) (hP r) (hPN r) (g r).datum.radius (g r).datum.C (g r).datum.D (g r).datum.inactive
        ∀(left₁ : Bool)(u₀ : O)(unit₁ : FirstSourceLabel→O)(Tz : ℝ),
        left₁=!reflected → u₀≠0 →
        ((∀l,IsUnit (unit₁ l)) ∧ Real.logb Z (normValue u₀)≤ε) →
        let mult:=fun r : rows=>firstRowMultiplier first left₁ u₀ unit₁ r.val
        (∀r,∀(W' : ℝ)(hW' : (st r).width≤W'),Presented η₀ Z (widenState (st r) W' hW') (mult r) Tz) →
        let ordinaryRows:=fun r : rows=>mainLowSourceRows second
          (ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m) (fun _=>True)
        let canonical:=fun r : rows=>mainLowCanonicalSelector M H hH (datum r) (χ₀ r) χ ψ
          (internalQ Q η₀) hQ72 m hm₀ hml hm₂ Z Bmask hZ second
          (by exact hP r) (by exact hPN r) η₀ (inf_le_left.trans hQM) inf_le_right e (Z^τ) he hT hbeta hβhi
        let src:=fun r=>withHeight (q r).first ((g r).datum.τ ray) heightV
        let Ds:=fun r : rows=>(datum r).block.divisors.filter Squarefree
        let unionDs:=sharedProjectors Ds
        let firstMass:=fun l=>geometryFirstHighMass reflected s R seed₀ Ψ Mrow Z ξ εmass
          (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin (firstIndex l).1.val
        let physical:=geometryHighFactor reflected (geometrySupportConstant N supply ap ap) bin
        let error:=εwidth*unit+ξ/2-unit*(Cycle63.AffineLedger.lowReserve)+(unit-Mrow)+εold+2*ε*d*(Fintype.card α:ℝ)+
          Cycle63.AffineLedger.lowRate*(frequencyLoss Z 32 ξ+reserve+εpad*unit)+Cycle63.AffineLedger.q*mesh+pad
        let exponentFull:=Bmass*εmass+amp+error+εv+Bnorm*εshell+εlabels
        let factor : ℝ:=mainLowQuantitativeFactor Cg b Cs (p₀.control Sp) heightV height physical Z
          exponentFull (seed₀.absNorm:ℝ) N degree box.card
        let coefficient:=fun (r : rows)(_D : Ideal O)=>
          firstMass r.val.1/volume (childSrc r.val.1)*(g r).datum.K*
            normalizer (g r).datum.C (g r).datum.D (g r).datum.inactive
        let value:=fun (r : rows)(D : Ideal O)(z : O)=>
          ‖normalizedColumn (src r) (q r).E₂ (hE₂ r) (q r).R₂ (divisorSeed r) D z‖^2
        ∀(t₀ u : ℝ),heightV=t+2*Real.pi*(u-(if second then -t₀ else t₀)) →
        (∀r,divisorSeed r=(datum r).seed) →
        mainLowFixedRayPhysicalCost N supply ap second
          (fun r=>ordinarySecondDatum (datum r) (χ₀ r) (internalQ Q η₀) m)
          (fun r=>firstMass r.val.1/volume (childSrc r.val.1)) t₀ u χ ψ canonical≤
          (Cfirst*Z^εfirst)*((1/lowerFactor N supply ap)*(Fintype.card (BufferIndex e):ℝ)*
            ((64*factor)*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell))))

attribute [local irreducible] mainLowFixedRayPhysicalCost mainLowCanonicalSelector

variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 60000 in
theorem main_low_final_physical_spec_of_bins {α : Type} [Fintype α] [DecidableEq α]
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
    (εfirst Cfirst : ℝ)(degree : ℕ)(Sp : Finset (ℕ×ℕ))(Cg Cu : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (Z : ℝ)(hZ2 : 2≤Z)(hCg : 0<Cg)(hCu : 0<Cu)(hBstrong : Bmass+1≤Bnorm)
    (hcount : MainLowFirstShellCountAt N U εfirst Cfirst Z)
    (hspec : MainLowPhysicalBinSpec (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm Presented
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      degree Sp Cg Cu η₀ Q hQM hQ72 Z) :
    MainLowFinalPhysicalSpec (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm Presented
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst degree Sp Cg Cu η₀ Q hQM hQ72 Z := by
  unfold MainLowFinalPhysicalSpec
  intro hZ s θ w σ freq heightV height mesh hcard hmass hsupply' hm hsupper hsb₁ hsb₂
    hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
    unit Mrow reserve ξ hMmin hAdm hω hξ hMcap' hfit hzslot haff Label _ reflected second R seed₀ bin t firstIndex
    first cell amp childSrc Rchild seed K Tsec p c exponent sideLower hf₁ hw₁ hw₂ hsource
    hs₀ hs₀0 hinj hfirstproj
    rows hOriginal hU box hbox datum B₂ rwitness hf₂ q g χ₀ χ ψ m hm₀ hml hm₂ hP hPN
    divisorSeed hE₂ hdivisor p₀ hp₁ hp₂ Ψ hsourceOriginal hplain₁ hplain₂ hpool
    hwindowSource hplainScale ray st leftR uR unitR Tz hleft hu₀ hdict _ hpres ordinaryRows canonical src Ds unionDs
    firstMass physical error
    exponentFull factor coefficient value t₀ u hshift hseed
  let column:=fun l=>(firstIndex l).1.val
  have hshellCount := hcount (ι:=α) (Label:=Label) s hcard hpool R seed₀ (Z^Mrow) ξ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) bin column
  have hsq : ∀l,Squarefree (column l).2.1.val :=
    fun l=>actual_first_live_squarefree _ _ _ (firstIndex l).1.property
  let E:=(1/lowerFactor N supply ap)*(Fintype.card (BufferIndex e):ℝ)*
    ((64*factor)*(Cu*Z^(εunion+3*(((N:ℝ)+2)*U)*εshell)))
  have hphysical : 0≤physical := (geometry_high_factor_pos reflected
    (geometrySupportConstant N supply ap ap) bin
    (geometrySupportConstant_pos N supply ap ap hsupply hap hap)).le
  have hfactor : 0≤factor := mainLowQuantitativeFactor_nonneg Cg b Cs (p₀.control Sp)
    heightV height physical Z exponentFull (seed₀.absNorm:ℝ) N degree box.card
    hCg.le (le_trans zero_le_one hCs) hheight hphysical (zero_lt_one.trans hZ) (Nat.cast_nonneg _)
  have hE : 0≤E := by
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (div_nonneg zero_le_one
      (lowerFactor_pos N supply ap hsupply hap).le) (Nat.cast_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) hfactor)
        (mul_nonneg hCu.le (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)))
  rw [main_low_shell_fixed_ray_cost reflected s R seed₀ Z Mrow amp ξ reserve bs t
    (Fintype.card α) hZ bin firstIndex rows hsq N]
  calc
    _≤∑_n∈selectedShells (selectedFirstProjectors column),E := by
      refine Finset.sum_le_sum fun n hn => ?_
      let rs:=mainLowShellRows reflected s R seed₀ Z Mrow amp ξ reserve bs t (Fintype.card α) hZ bin firstIndex rows n
      let old:=mainLowShellRowOriginal reflected s R seed₀ Z Mrow amp ξ reserve bs t (Fintype.card α) hZ bin firstIndex rows n
      let fi:=fun l : SelectedFirstShell column n=>firstIndex l.val
      have hg:=actual_main_low_final_shell_first_gates reflected s R seed₀ Z Mrow ξ hZ bin hw₁ hw₂
        firstIndex Bmass Bnorm hZ2 hs₀ hsourceOriginal hBstrong hinj hf₁ n hn
      have hTfirst:=(actual_geometry_selected_first_shell_scale s N R seed₀ (Z^Mrow) Z ξ U
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hcard hZ.le hUcap hpool bin column n hn).1
      have hk:=hspec
      unfold MainLowPhysicalBinSpec at hk
      have hkfirst:=hk hZ s θ w σ freq heightV height mesh hcard hmass
        hsupply' hm hsupper hsb₁ hsb₂ hw hwL hwr hmesh hwm hσlo hσhi hheight hfreq hT hfreqbin hβhi
        unit Mrow reserve ξ hMmin hAdm hω hξ hMcap' hfit hzslot haff reflected second R seed₀ bin t fi
        hg.2.1 hw₁ hw₂ (fun l=>hsource l.val) (dyadicScale n) hTfirst hg.2.2.2 hs₀ hs₀0 hg.1
        (fun l=>hfirstproj l.val) hg.2.2.1

      have hkrows:=hkfirst rs
      have hko:=hkrows (main_low_shell_original_gate reflected s R seed₀ Z Mrow amp ξ reserve bs t (Fintype.card α)
          hZ bin hw₁ hw₂ firstIndex rows hOriginal n)
      have hku:=hko (fun r hr=>hU (old ⟨r,hr⟩).val (old ⟨r,hr⟩).property)
      have hkbox:=hku box
        (fun r hr=>hbox (old ⟨r,hr⟩).val (old ⟨r,hr⟩).property)

      have hkb:=hkbox (fun r=>B₂ (old r))
      have hkw:=hkb (fun r=>rwitness (old r))
      have hkf:=hkw (fun r=>hf₂ (old r))
      have hkchar:=hkf (fun r=>χ₀ (old r)) χ ψ m hm₀ hml hm₂
      have hkp:=hkchar (fun r=>hP (old r)) (fun r=>hPN (old r))
      have hkd:=hkp (fun r=>divisorSeed (old r)) (fun r=>hE₂ (old r)) (fun r=>hdivisor (old r))
      have hkp0:=hkd p₀ hp₁ hp₂ Ψ
      have hks:=hkp0 hsourceOriginal hplain₁ hplain₂ hpool hwindowSource hplainScale
        leftR uR unitR Tz hleft hu₀ hdict (fun r W' hW'=>hpres (old r) W' hW')
      obtain ⟨select,heq,_hpos,hcost⟩:=hks
      have hsel := funext heq
      have hb:=hcost t₀ u hshift (fun r=>hseed (old r))
      subst select
      exact hb
    _=((selectedShells (selectedFirstProjectors column)).card:ℝ)*E:=by simp
    _≤(Cfirst*Z^εfirst)*E:=mul_le_mul_of_nonneg_right hshellCount hE

attribute [local irreducible] MainLowFinalPhysicalSpec MainLowPhysicalBinSpec
variable [Cycle63.AffineLedger] in
set_option maxHeartbeats 100000 in
def actual_main_low_final_physical_bins {Adm : ℝ→ℝ→ℝ→Prop} {labelExp : Bool → ℝ → ℝ → FirstSourceLabel → ℝ}
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
    (window pad : ℝ)(hwindow : 0≤window)(hpad : 0<pad)(hL0 : 0≤L) (hτgap : 2*τ<d*η) (hBstrong : Bmass+1≤Bnorm) (εfirst : ℝ)(hefirst : 0<εfirst) :
    ∀(η₀ : Character)(Q : Ideal O)(hQM : Q≤M),
      internalQ Q η₀≠0 → internalQ Q η₀≠⊤ → ∀hQ72 : internalQ Q η₀≤Ideal.span {(72:O)},
      Σdegree : ℕ,ΣSp : Finset (ℕ×ℕ),ΣCu : ℝ,ΣCfirst : ℝ,
        PLift (0<Cu ∧ 0<Cfirst) ×
        ΣCg : ℝ,PLift (0<Cg ∧ ∀ᶠZ : ℝ in atTop,2≤Z ∧
          MainLowFinalPhysicalSpec (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm (Presented Bmask)
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst degree Sp Cg Cu η₀ Q hQM hQ72 Z) := by
  intro η₀ Q hQM hQ0 hQt hQ72
  let counts:=eventual_actual_geometry_selected_first_shell_subpower N U εfirst hUcap hefirst
  let Cfirst:=Classical.choose counts
  have hCfirst:= (Classical.choose_spec counts).1
  have hcount:= (Classical.choose_spec counts).2
  let k:=actual_main_low_physical_bins (α:=α) M H hH hgate
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel hrow5
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0 hτgap (by linarith)
      η₀ Q hQM hQ0 hQt hQ72
  refine ⟨k.1,k.2.1,k.2.2.1,Cfirst,PLift.up ⟨k.2.2.2.1.down,hCfirst⟩,?_⟩
  let hc:=k.2.2.2.2
  refine ⟨hc.1,PLift.up ⟨hc.2.down.1,?_⟩⟩
  filter_upwards [hc.2.down.2,hcount] with Z hz hf
  refine ⟨hz.1,?_⟩
  have hcountZ : MainLowFirstShellCountAt N U εfirst Cfirst Z := hf.2
  exact main_low_final_physical_spec_of_bins (α:=α) M H hH
      W A B a b Bmask L Lslot lo hi Mcap εold hA hWs hW hB ha ha' hb hBmask hMcap hεold hbeta
      Rwidth dmax τ ε e κ η margin d hRw hdmax hτ hε he he' hκ hη hbudget hmargin hd hdsupply hdm
      bs εwidth εpad Mmin hbs hew hep hmin εshell heshell N Cs hCs
      supply εv Bnorm εlabels hsupply hev hBnorm hel Adm (Presented Bmask)
      ap εmass Bmass hap hemass U εunion hUcap heunion window pad hwindow hpad hL0
      εfirst Cfirst k.1 k.2.1 hc.1 k.2.2.1 η₀ Q hQM hQ72 Z hz.1 hc.2.down.1 k.2.2.2.1.down hBstrong hcountZ hz.2

end SavedKernel

end
end OAI.SevenEighths.Cycle63InitialMass
