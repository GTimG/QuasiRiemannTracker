/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainLowPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryMainSelectedPartition
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainNormalized
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainHighBound
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainContraction
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainRatioPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineRetainedPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineFinalSchedule
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineMainScalarPayment
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineBudgetTransport
import Candidate.Cycle63.Physical.InitialMass.GeometryAffineRetainedBudget
import Candidate.Cycle63.Arithmetic.Constants
set_option autoImplicit false
set_option maxHeartbeats 80000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff HeckeNotation
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle63Moment
open Cycle63Moment.LowBranch
open LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss
open Cycle63FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle63InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyState CenteredMomentEnergyBands
local instance affineMainPaymentSumDecidable {α : Type} : DecidableEq (α⊕Fin 2) := Classical.decEq _
attribute [local irreducible] Finset.univ mainLowPhysicalCompleteCost

variable [Cycle63.AffineLedger] in
/-- Half the LOW reserve is below `1/100`. -/
theorem geometry_affine_main_reserve_half : -(1/100:ℝ)≤-((Cycle63.AffineLedger.lowReserve/2):ℝ) := by
  have hlow := Cycle63.AffineLedger.lowReserve_le
  linarith

/-- One common degree pays the two inner Mellin heights of both branches.
The original source-height factor stays inside the branch constants. -/
theorem affine_main_two_height_join (CL CH t u : ℝ) (dl dh : ℕ)
    (hCL : 0≤CL) (hCH : 0≤CH) :
    (CL*(1+‖t‖)^dl)*(1+‖u‖)^dl+(CH*(1+‖t‖)^dh)*(1+‖u‖)^dh≤
      ((CL+CH)*(1+‖t‖)^(max dl dh))*(1+‖u‖)^(max dl dh) := by
  have ht : 1≤1+‖t‖ := by linarith [norm_nonneg t]
  have hu : 1≤1+‖u‖ := by linarith [norm_nonneg u]
  have hm (C : ℝ) (k : ℕ) (hC : 0≤C) (hk : k≤ max dl dh) :
      (C*(1+‖t‖)^k)*(1+‖u‖)^k≤
        (C*(1+‖t‖)^(max dl dh))*(1+‖u‖)^(max dl dh) := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hk) hC)
      (pow_le_pow_right₀ hu hk) (pow_nonneg (zero_le_one.trans hu) _)
      (mul_nonneg hC (pow_nonneg (zero_le_one.trans ht) _))
  convert add_le_add (hm CL dl hCL (le_max_left _ _))
    (hm CH dh hCH (le_max_right _ _)) using 1; ring

variable {α : Type} [Fintype α] [DecidableEq α]

variable [Cycle63.AffineLedger] in
/-- The exact component receipt required by physical selection, at a parent with puncture `R`, seed `seed` and radial scale
`Z^Mrow`. Both costs use one selector on the original-nonzero selected family. The first mass and child volume remain inside
the coefficient. -/
def GeometryAffineMainSelectedBranches
    (ε ξ Z amp reserve baseHeight CL CH : ℝ) (dl dh : ℕ) (hZ : 1<Z)
    (reflected : Bool) (s : Input α) (R seed : Ideal O) (Mrow : ℝ) (key : ℤ×(Fin 5→ℤ)) (Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter) (Q : Ideal O) (m : O) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) : Prop :=
  ∀(second : Bool)(t₀ u : ℝ),
    let hKfirst:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) Mrow
    let rows:=firstLiveColumns (geometryFirstSource s R seed (Z^Mrow) Z ξ hKfirst key) (fun _=>logAnnulus)
    let ideal:=fun j : rows=>geometryColumnIdeal reflected s R seed (Z^Mrow) Z ξ hKfirst key j.val
    let mass:=fun j : rows=>geometryFirstHighMass reflected s R seed Ψ Mrow Z ξ ε hKfirst key j.val
    ∀{Label : Type}[Fintype Label](column : Label → rows),
      Function.Injective (fun j=>(geometryFirstLabel s R seed (Z^Mrow) Z ξ hKfirst key (column j).val,
        (column j).val.2.1.val)) →
    ∀alloc : (j : Label)→actualAllocations s.pools (ideal (column j)),
      (∀j,frozenCoefficient (alloc j).val (ideal (column j)) R s.ν s.W s.P≠0) →
    let firstIndex : Label→GeometryLowFirstIndex reflected s R seed (Z^Mrow) Z ξ hKfirst key:=
      fun j=>⟨column j,alloc j⟩
    let selected:=mainLowSelectedNonzeroRows reflected s R seed Z Mrow amp ξ reserve (9/4) baseHeight
      (Fintype.card α) hZ key hz₁ hz₂ firstIndex
    let datum:=fun r : selected=>geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve (9/4)
      baseHeight (Fintype.card α) hZ key hz₁ hz₂ χ Q m ⟨firstIndex r.val.1,r.val.2⟩
    let coefficient:=fun r : selected=>mass (column r.val.1)/volume
      (geometryLowFirstChild reflected s R seed (Z^Mrow) Z ξ hKfirst key baseHeight (firstIndex r.val.1))
    ∃e : ℝ,∃select : (r : selected)→(χ ψ : RayCharacter)→
      mainLowSourceRows second (datum r) (fun _=>True)→BufferIndex e,
      mainLowPhysicalCompleteCost (Fintype.card α) 1 (1/4) second datum coefficient t₀ u select≤
        (CL*(1+‖t₀‖)^dl)*(1+‖u‖)^dl ∧
      (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(datum l).block)=>
        ((1+Cycle63.AffineLedger.q)/2)≤bufferValue e (mainPhysicalFamilySelector second datum select r)),
        (coefficient r.val.1*((datum r.val.1).K/lowerFactor (Fintype.card α) 1 (1/4))*
          normalizer (datum r.val.1).C (datum r.val.1).D (datum r.val.1).inactive)*
        highNormalizedRowCost second datum r
          ((datum r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
          ((datum r.val.1).block.divisors.filter Squarefree))≤
        (CH*(1+‖t₀‖)^dh)*(1+‖u‖)^dh

variable [Cycle63.AffineLedger] in
/-- Exact low/high component costs discharge the genuine supported first
selection, then the physical selection theorem returns the full normalized
contract. This bridge adds no coefficient majorant or label multiplicity. -/
theorem actual_affine_main_normalized_of_selected_low_high
    (Cs ε ξ K Z CL CH : ℝ) (dl dh : ℕ) (hZ : 1<Z)
    (hK : 0≤K) (hCL : 0≤CL) (hCH : 0≤CH)
    (hselection : GeometryAffinePhysicalSelectionSpec (ι:=α) Cs ε ξ K Z)
    (reflected : Bool) (s : Input α) (p : Profiles (1/4) (9/4))
    (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card α) Cs Z)
    (R seed : Ideal O) (Mrow : ℝ) (hseed : Squarefree seed) (hMrow : 0≤Mrow)
    (amp reserve baseHeight : ℝ) (key : ℤ×(Fin 5→ℤ)) (Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter) (Q : Ideal O) (m : O) (W : 𝓢(ℝ,ℂ))
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hbranches : GeometryAffineMainSelectedBranches ε ξ Z amp reserve baseHeight CL CH dl dh hZ
      reflected s R seed Mrow key Ψ χ Q m hz₁ hz₂) :
    let selected:=geometryMainNonzeroBlocks reflected s R seed Z Mrow amp ξ reserve (9/4) baseHeight
      (Fintype.card α) hZ key hz₁ hz₂
    let datum:=fun j : selected=>geometryMainOrdinaryDatum reflected s R seed Z Mrow amp ξ reserve
      (9/4) baseHeight (Fintype.card α) hZ key hz₁ hz₂ χ Q m j.val
    let weight:=fun j : selected=>geometryMainSecondWeight reflected s R seed Z Mrow amp ξ reserve
      (9/4) baseHeight (Fintype.card α) hZ key Mrow (Real.logb Z (volume s))
      (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z ξ q)) j.val
    SecondNormalizedBound W (max dl dh) (max dl dh) datum weight (fun _=>K*Z^ε*(CL+CH)) (fun _=>1) := by
  apply actual_affine_main_normalized_of_selected Cs ε ξ K Z (CL+CH) (max dl dh) hZ hK
    (add_nonneg hCL hCH) hselection reflected s p caps R seed Mrow hseed hMrow amp reserve
    baseHeight key Ψ χ Q m W hz₁ hz₂
  intro second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf
  obtain ⟨e,select,hlow,hhigh⟩:=hbranches second t₀ u column hinj alloc hf
  have hb:=actual_main_selected_low_high_cost reflected s R seed Z Mrow amp ξ reserve (9/4) baseHeight
    (Fintype.card α) hZ key hz₁ hz₂ (fun j=>⟨column j,alloc j⟩)
    (fun j=>mass (column j)) χ Q m 1 (1/4) second t₀ u e select
    ((CL*(1+‖t₀‖)^dl)*(1+‖u‖)^dl) ((CH*(1+‖t₀‖)^dh)*(1+‖u‖)^dh) hlow hhigh
  exact hb.trans (affine_main_two_height_join CL CH t₀ u dl dh hCL hCH)

/-- Put source-height and profile controls under one union before adding
the physical branches. Only scalar controls are enlarged. -/
theorem affine_main_branch_control_mono (p : Profiles (1/4) (9/4))
    (S S' : Finset (ℕ×ℕ)) (K side x Z target : ℝ) (d D : ℕ)
    (hS : S⊆S') (hK : 0≤K) (hside : 0≤ side) (hx : 1≤x) (hZ : 1<Z) (hd : d≤D) :
    K*(p.control S)^2*side*Z^target*x^d≤
      K*(p.control S')^2*side*Z^target*x^D := by
  have hc:=pow_le_pow_left₀ (p.control_nonneg S) (profile_control_mono p hS) 2
  have hp:=pow_le_pow_right₀ hx hd
  have hz:=Real.rpow_nonneg (zero_lt_one.trans hZ).le target
  gcongr

variable [Cycle63.AffineLedger] in
/-- Enlarging only the scalar branch constants preserves the same selector,
selected carriers, and actual physical costs. -/
theorem affine_main_selected_branches_mono
    (ε ξ Z amp reserve baseHeight CL CH CL' CH' : ℝ)(dl dh : ℕ)(hZ : 1<Z)
    (reflected : Bool)(s : Input α)(R seed : Ideal O)(Mrow : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter)(Q : Ideal O)(m : O)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hCL : CL≤CL')(hCH : CH≤CH')
    (hbranches : GeometryAffineMainSelectedBranches ε ξ Z amp reserve baseHeight CL CH dl dh hZ
      reflected s R seed Mrow key Ψ χ Q m hz₁ hz₂) :
    GeometryAffineMainSelectedBranches ε ξ Z amp reserve baseHeight CL' CH' dl dh hZ
      reflected s R seed Mrow key Ψ χ Q m hz₁ hz₂ := by
  intro second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf firstIndex selected datum coefficient
  obtain ⟨e,select,hlow,hhigh⟩:=hbranches second t₀ u column hinj alloc hf
  refine ⟨e,select,hlow.trans ?_,hhigh.trans ?_⟩ <;> gcongr

/-- A union of profile controls and one source-height degree pays both
physical branches. The inner Mellin degrees and selector are preserved. -/
theorem affine_main_selected_branches_common_control
    (ε ξ Z amp reserve baseHeight KL KH side low high height : ℝ)(dl dh D : ℕ)(hZ : 1<Z)
    (reflected : Bool)(s : Input α)(R seed : Ideal O)(Mrow : ℝ)(p : Profiles (1/4) (9/4))
    (SL SH S : Finset (ℕ×ℕ))(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))
    (χ : RayCharacter)(Q : Ideal O)(m : O)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hKL : 0≤KL)(hKH : 0≤KH)(hside : 0≤ side)(hheight : 0≤height)
    (hSL : SL⊆S)(hSH : SH⊆S)(hdl : dl≤D)(hdh : dh≤D)
    (hbranches : GeometryAffineMainSelectedBranches ε ξ Z amp reserve baseHeight
      (KL*(p.control SL)^2*side*Z^low*(1+|baseHeight|+height)^dl)
      (KH*(p.control SH)^2*side*Z^high*(1+|baseHeight|+height)^dh) dl dh hZ
      reflected s R seed Mrow key Ψ χ Q m hz₁ hz₂) :
    let control:=(p.control S)^2*side*(1+|baseHeight|+height)^D
    GeometryAffineMainSelectedBranches ε ξ Z amp reserve baseHeight
      ((KL*control)*Z^low) ((KH*control)*Z^high) dl dh hZ
      reflected s R seed Mrow key Ψ χ Q m hz₁ hz₂ := by
  intro control
  have hb : 1≤1+|baseHeight|+height := by linarith [abs_nonneg baseHeight]
  apply affine_main_selected_branches_mono ε ξ Z amp reserve baseHeight _ _ _ _ dl dh hZ
    reflected s R seed Mrow key Ψ χ Q m hz₁ hz₂ _ _ hbranches
  · convert affine_main_branch_control_mono p SL S KL side (1+|baseHeight|+height) Z low dl D
      hSL hKL hside hb hZ hdl using 1;dsimp only [control];ring
  · convert affine_main_branch_control_mono p SH S KH side (1+|baseHeight|+height) Z high dh D
      hSH hKH hside hb hZ hdh using 1;dsimp only [control];ring

omit [DecidableEq α] in
/-- Actual affine slot scales identify the raw complete-low amplifier with
its original slot-mass cell. No slot count or Fourier scale is substituted. -/
theorem affine_main_amplifier_of_actual_scales
    (s : Input α)(Z : ℝ)(hZ : 1<Z)(w : α→ℝ)(hP : ∀i,s.P i=Z^(w i)) :
    (1:ℝ)*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑i,Real.logb Z (s.P i))/(1:ℝ))))=
    Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑i,w i))) := by
  have hsum : (∑i,Real.logb Z (s.P i))=∑i,w i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hP i]
    exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
  simp only [hsum,div_one,one_mul]

section CanonicalHigh
variable (M : Ideal O) [NeZero M]
local instance affineMainPaymentFiniteQuotient : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

/-- The remaining actual high component, on the exact canonical selector
and shared low schedule. This is an explicit high receipt, not a completed
main bound. All physical carriers use the actual source cardinality. -/
def GeometryAffineMainCanonicalHighReceipt
    (g : GeometryAffineLowSchedule) (η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (hβlo : 51/100≤HeckeZeroSupremum.beta) (hβhi : HeckeZeroSupremum.beta≤7/8)
    (Z : ℝ) (hZ : 1<Z) (hT : 2<Z^g.τ)
    (reflected : Bool) (s : Input α) (p : Profiles (1/4) (9/4))
    (amp baseHeight height : ℝ) (key : ℤ×(Fin 5→ℤ)) (Ψ : 𝓢(ℝ,ℂ)) (χ₀ : RayCharacter)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (KH : ℝ) (SH : Finset (ℕ×ℕ)) (dh : ℕ) (highSaving : ℝ) : Prop :=
  ∀(second : Bool)(t₀ u : ℝ),
    let hKfirst:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (1:ℝ)
    let rows:=firstLiveColumns (geometryFirstSource s 1 1 (Z^(1:ℝ)) Z (g.μ/64) hKfirst key) (fun _=>logAnnulus)
    let ideal:=fun j : rows=>geometryColumnIdeal reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64) hKfirst key j.val
    let mass:=fun j : rows=>geometryFirstHighMass reflected s 1 1 Ψ 1 Z (g.μ/64) g.δ hKfirst key j.val
    ∀{Label : Type}[Fintype Label](column : Label → rows),
      Function.Injective (fun j=>(geometryFirstLabel s 1 1 (Z^(1:ℝ)) Z (g.μ/64) hKfirst key (column j).val,
        (column j).val.2.1.val)) →
    ∀alloc : (j : Label)→actualAllocations s.pools (ideal (column j)),
      (∀j,frozenCoefficient (alloc j).val (ideal (column j)) 1 s.ν s.W s.P≠0) →
    let firstIndex : Label→GeometryLowFirstIndex reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64) hKfirst key:=
      fun j=>⟨column j,alloc j⟩
    let selected:=mainLowSelectedNonzeroRows reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
      baseHeight (Fintype.card α) hZ key hz₁ hz₂ firstIndex
    let raw:=fun r : selected=>mainLowSelectedDatum reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
      baseHeight (Fintype.card α) hZ key hz₁ hz₂ firstIndex r
    let datum:=fun r : selected=>ordinarySecondDatum (raw r) χ₀ (internalQ Q η₀) fixedBadMask
    let coefficient:=fun r : selected=>mass (column r.val.1)/volume
      (geometryLowFirstChild reflected s 1 1 (Z^(1:ℝ)) Z (g.μ/64) hKfirst key baseHeight (firstIndex r.val.1))
    ∀(hP : ∀r,(raw r).R*(if second then (raw r).D else (raw r).C)≠0)
      (hPN : ∀r,((((raw r).R*(if second then (raw r).D else (raw r).C)).absNorm:ℝ))≤Z^(28:ℝ)),
    let canonical:=fun (r : selected)(χ ψ : RayCharacter)=>mainLowCanonicalSelector M H hH
      (raw r) χ₀ χ ψ (internalQ Q η₀) hQ72 fixedBadMask fixedBadMask_ne_zero
      (dvd_mul_right _ _) (dvd_mul_left _ _) Z 28 hZ second (hP r) (hPN r) η₀
      (inf_le_left.trans hQM) inf_le_right g.e (Z^g.τ) g.e_pos hT hβlo hβhi
    (∑r∈Finset.univ.filter (fun r : secondLiveRows (fun l=>(datum l).block)=>
      ((1+Cycle63.AffineLedger.q)/2)≤bufferValue g.e (mainPhysicalFamilySelector second datum canonical r)),
      (coefficient r.val.1*((datum r.val.1).K/lowerFactor (Fintype.card α) 1 (1/4))*
        normalizer (datum r.val.1).C (datum r.val.1).D (datum r.val.1).inactive)*
      highNormalizedRowCost second datum r
        ((datum r.val.1).input.t+2*Real.pi*(u-(if second then -t₀ else t₀)))
        ((datum r.val.1).block.divisors.filter Squarefree))≤
      KH*(p.control SH)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*
        Z^(amp+highSaving)*(1+|baseHeight|+height)^dh*(1+‖t₀‖)^dh*(1+‖u‖)^dh

/-- Specialize the frozen actual low receipt and join it to the explicit
actual high receipt. Fixed inducing-mask nonzero and divisor gates are
proved internally, and both branches keep one literal selector. -/
theorem actual_affine_main_selected_branches
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤HeckeZeroSupremum.beta)(g : GeometryAffineLowSchedule)(Mcap Lslot : ℝ)
    (ηseed : Character)(SL : Finset (ℕ×ℕ))(dl : ℕ)(KL : ℝ)
    (η₀ : Character)(Q : Ideal O)(hQM : Q≤M)(hQ72 : internalQ Q η₀≤Ideal.span {(72:O)})
    (Z : ℝ)(hlow : GeometryAffineMainLowSpec (α:=α) M H hH W hW hWs hβlo g Mcap Lslot ηseed SL dl KL η₀ Q hQM hQ72 Z)
    (hZ : 1<Z)(θ : α→RayQuotient.Characters M H)(w σ freq : α→ℝ)
    (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
    (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
    (p : Profiles (1/4) (9/4))(tplain X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂)
    (height mesh : ℝ)(hw : ∀i,0≤w i)(hmesh : 0≤ mesh)
    (hmeshcap : mesh≤Lslot)(hwm : ∀i,w i≤ mesh)
    (hheight : 0≤height)(hfreq : ∀i,|freq i|≤height)(hT : 2<Z^g.τ)
    (hβhi : HeckeZeroSupremum.beta≤7/8)
    (hwin : Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i))
    (reflected : Bool)(baseHeight : ℝ)(key : ℤ×(Fin 5→ℤ))(Ψ : 𝓢(ℝ,ℂ))(χ₀ : RayCharacter)
    (KH : ℝ)(SH : Finset (ℕ×ℕ))(dh : ℕ)(highSaving : ℝ) :
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) tplain X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=affine_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=affine_profile_zero p 1
    let amp:=(1:ℝ)*Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell ((∑j,Real.logb Z (s.P j))/(1:ℝ))))
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    GeometryAffineMainCanonicalHighReceipt M H hH g η₀ Q hQM hQ72 hβlo hβhi Z hZ hT
      reflected s p amp baseHeight height key Ψ χ₀ hz₁ hz₂ KH SH dh highSaving →
    GeometryAffineMainSelectedBranches g.δ (g.μ/64) Z amp (g.μ/8) baseHeight
      (KL*(p.control SL)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*
        Z^(geometryAffineLowTarget g (Fintype.card α) amp omega mesh)*(1+|baseHeight|+height)^dl)
      (KH*(p.control SH)^2*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card α) 1 (1/4) (1/4)) key*
        Z^(amp+highSaving)*(1+|baseHeight|+height)^dh)
      dl dh hZ reflected s 1 1 1 key Ψ χ₀ (internalQ Q η₀) fixedBadMask hz₁ hz₂ := by
  intro s hz₁ hz₂ amp omega hhigh second t₀ u hKfirst rows ideal mass Label _ column hinj alloc hf firstIndex selected datum coefficient
  have hb:=hlow hZ θ w σ freq hσ bΦ state hη p tplain X₁ X₂ hX₁ hX₂ height mesh
    hw hmesh hmeshcap hwm hheight hfreq hT hβhi hwin
    reflected second key baseHeight firstIndex hf hinj (fun _=>χ₀) fixedBadMask
    fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) Ψ t₀ u
  obtain ⟨hP,hPN,hpaid⟩:=hb
  have hh:=hhigh second t₀ u column hinj alloc hf hP hPN
  refine ⟨g.e,_,?_,hh⟩
  simpa only [Real.norm_eq_abs, datum, coefficient, firstIndex, mass,
    geometryMainOrdinaryDatum, mainLowSelectedDatum] using hpaid

variable [Cycle63.AffineLedger] in
/-- The common loss unit closes both branch exponents after exactly three
external dictionary fees. Cardinality enlargement occurs only in this ledger. -/
theorem affine_main_final_branch_exponents
    (g : GeometryAffineLowSchedule) (εaffine : ℝ) (hε : 0<εaffine)
    (hμ : g.μ=geometryLossUnit 1 εaffine) (n N : ℕ) (hn : n≤N)
    (B L amp omega mesh : ℝ) (hB : 0≤B) (hL : 0≤L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)
    (hω : omega≤33*g.μ/128) (hmesh : mesh≤g.μ/8) :
    geometryAffineLowTarget g n amp omega mesh+3*g.δ-amp≤-((Cycle63.AffineLedger.lowReserve/2):ℝ) ∧
    (amp+(-(Cycle63.AffineLedger.lowReserve:ℝ)+4*g.μ-3*g.δ))+3*g.δ-amp≤
      -((Cycle63.AffineLedger.lowReserve/2):ℝ) := by
  have hm : 0<geometryLossUnit 1 εaffine :=
    geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hl := geometry_affine_subset_low_target_ledger g B L n N hn amp omega mesh hB hL hδ hω hmesh
  have hb := geometry_paid_loss 1 εaffine 1 (Cycle63.AffineLedger.lowReserve) (2*g.μ)
    (by norm_num) le_rfl le_rfl (by rw [hμ];linarith)
  have hh := geometry_paid_loss 1 εaffine 1 (Cycle63.AffineLedger.lowReserve) (4*g.μ)
    (by norm_num) le_rfl geometry_high_reserve_ge_low (by rw [hμ];linarith)
  constructor <;> linarith only [hl,hb,hh]

/-- Genuine affine source caps and physical selection are obtained together
before the live subset, source, first allocation, or Mellin heights. The
cap is converted to the actual subset count without changing Fourier data. -/
theorem actual_affine_main_source_selection
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (δ ξ : ℝ)(hδ : 0<δ)(hξ : 0≤ξ) :
    ∃Cs : ℝ,1≤Cs ∧ ∃Ksel : ℝ,0<Ksel ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀T : Finset α,GeometryAffinePhysicalSelectionSpec (ι:=T) Cs δ ξ Ksel Z ∧
    ∀(η₀ : Character)(θ : T→RayQuotient.Characters M H)(w σ freq : T→ℝ)
      (hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))(bΦ : ℝ)(state : NaturalState Z 0 bΦ)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
      let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
        (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
      GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z := by
  have hcaps:=eventual_actual_affine_exceptional_source_gates (α:=α) M H hH W hW hWs
  obtain ⟨Cs,hCs,hcaps⟩:=hcaps
  obtain ⟨Ksel,hKsel,hselection⟩:=uniform_actual_affine_physical_selection (α:=α) Cs δ ξ hCs hδ hξ
  refine ⟨Cs,hCs,Ksel,hKsel,?_⟩
  filter_upwards [hcaps,hselection] with Z hz hs
  refine ⟨hz.1,?_⟩
  intro T
  refine ⟨hs T,?_⟩
  intro η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwin s
  exact geometry_affine_source_gates_actual_card s p (Fintype.card α) Cs Z
    (hz.2 T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂ hw hwin)

/-- All outside payment receipts are constructed for the actual affine
source before its subset, profiles, allocation, and heights. Only exact
selected component costs remain as a branch premise. This conditional
endpoint does not claim that the pending high theorem is complete. -/
theorem actual_affine_main_uniform_component_payment
    (A dl dh : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : Continuous W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (ηseed : Character)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (g : GeometryAffineLowSchedule)(hμ : g.μ=geometryLossUnit 1 εaffine)
    (N : ℕ)(hN : Fintype.card α≤N)(B L : ℝ)(hB : 0≤B)(hL : 0≤L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)(hmeshμ : mesh≤g.μ/8)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)})
    (KL KH : ℝ)(hKL : 0≤KL)(hKH : 0≤KH) :
    ∃Cs : ℝ,1≤Cs ∧ ∃Ksel : ℝ,0<Ksel ∧ ∃Cm : ℝ,0≤Cm ∧
    ∃SE : Finset (ℕ×ℕ),∃dE : ℕ,∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(T : Finset α)(η₀ : Character)(θ : T→RayQuotient.Characters M H)
      (w σ freq : T→ℝ)(hσ : ∀i,σ i∈Set.Icc (33/50:ℝ) (33/50))
      (bΦ : ℝ)(state : NaturalState Z 0 bΦ)(hη : state.character=ηseed)
      (p : Profiles (1/4) (9/4))(t X₁ X₂ : ℝ)(hX₁ : 0<X₁)(hX₂ : 0<X₂),
      (∀i,0≤w i) → (∀i,w i≤ mesh) →
      Cycle63.AffineLedger.PlainWindow (length Z X₁) (length Z X₂) (∑i,w i) →
    ∀(S : Finset (ℕ×ℕ))(D : ℕ),SE⊆S → dE≤D →
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),0≤height →
    ∀χ₀ : RayCharacter,
    let s:=affineInput M H hH η₀ θ W hW 1 2 (33/50) (33/50)
      (by norm_num) hWs w σ freq hσ state p (by norm_num) (Cycle63.AffineLedger.comparisonLength (length Z X₁) (length Z X₂) (∑i,w i)) t X₁ X₂ hX₁ hX₂
    let hz₁ : s.W₁ 0=0:=affine_profile_zero p 0
    let hz₂ : s.W₂ 0=0:=affine_profile_zero p 1
    let beta:=Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑i,w i))
    let amp:=Cycle63.AffineLedger.amp beta
    let P:=CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^amp)
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    let low:=geometryAffineLowTarget g (Fintype.card T) amp omega mesh
    let high:=amp+(-(Cycle63.AffineLedger.lowReserve:ℝ)+4*g.μ-3*g.δ)
    let control:=(p.control S)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
    GeometryAffineMainSelectedBranches g.δ (g.μ/64) Z amp (g.μ/8) firstHeight
      ((KL*control)*Z^low) ((KH*control)*Z^high) dl dh hZ
      reflected s 1 1 1 key Ψ χ₀ Qfix fixedBadMask hz₁ hz₂ →
    (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
      ‖geometryMainRetainedSum reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
        firstHeight hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (g.μ/64) q))‖≤
      Cm*control*Z^(-((Cycle63.AffineLedger.lowReserve/2):ℝ)) := by
  have hsource:=actual_affine_main_source_selection (α:=α) M H hH
    W hW hWs g.δ (g.μ/64) g.δ_pos (div_nonneg g.μ_pos.le (by norm_num))
  obtain ⟨Cs,hCs,Ksel,hKsel,hsource⟩:=hsource
  obtain ⟨Ce,hCe,SE,dE,Co,hCo,hcontract⟩:=actual_affine_main_retained_contraction (α:=α)
    M H hH A (max dl dh) (max dl dh) hc hs Sbad hbad W hW hWs ηseed εaffine mesh hε hmesh
    Qfix hQ hQt hQ72 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _)
  obtain ⟨Cb,hCb,hratio⟩:=uniform_actual_affine_main_ratio_payment (α:=α) M H hH
    W hW hWs εaffine g.δ hε g.δ_pos
  obtain ⟨Cbudget,hCbudget,hbudget⟩:=actual_affine_geometry_retained_budget (α:=α) M H hH
    Sbad hbad W hW hWs g.δ mesh g.μ g.δ_pos g.μ_pos g.μ_cap hmesh
  let Cm:=Ce+Co*(56*geometryAmplifierCoefficientCap*Cb*Ksel*(KL+KH))
  refine ⟨Cs,hCs,Ksel,hKsel,Cm,by have := geometryAmplifierCoefficientCap_pos;dsimp only [Cm];positivity,SE,dE,?_⟩
  filter_upwards [hsource,hcontract,hratio,hbudget,eventual_geometry_small_frequency g.μ g.μ_pos]
    with Z hz hcZ hrZ hpZ hfZ
  rw [←hμ] at hcZ hrZ
  refine ⟨hz.1,?_⟩
  intro hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂ hw hwm hwin S D hSE hdE Ψ reflected key firstHeight height hheight χ₀
    s hz₁ hz₂ beta amp P omega low high control hbranches
  have caps:=(hz.2 T).2 η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwin
  have hside : 0<geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key :=
    geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)
  have hcontrol : 0≤ control := by dsimp only [control];positivity
  have hn:=actual_affine_main_normalized_of_selected_low_high Cs g.δ (g.μ/64) Ksel Z
    ((KL*control)*Z^low) ((KH*control)*Z^high) dl dh hZ hKsel.le (by positivity) (by positivity)
    (hz.2 T).1 reflected s p caps 1 1 1 squarefree_one zero_le_one amp (g.μ/8) firstHeight key Ψ χ₀ Qfix
    fixedBadMask ballProfile hz₁ hz₂ hbranches
  let selected:=geometryMainNonzeroBlocks reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
    firstHeight (Fintype.card T) hZ key hz₁ hz₂
  let datum:=fun j : selected=>geometryLowSecondDatum reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8)
    (9/4) firstHeight (Fintype.card T) hZ key j.val.1 hz₁ hz₂ j.val.2
  let E:=Ksel*Z^g.δ*((KL*control)*Z^low+(KH*control)*Z^high)
  have hE : 0≤E := by dsimp only [E];positivity
  let ratio:=∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A
  have hnorm : SecondNormalizedBound ballProfile (max dl dh) (max dl dh)
      (fun j=>ordinarySecondDatum (datum j) χ₀ Qfix fixedBadMask)
      (fun j=>geometryMainSecondWeight reflected s 1 1 Z 1 amp (g.μ/64) (g.μ/8) (9/4)
        firstHeight (Fintype.card T) hZ key 1 (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s 1 1 Ψ (Z^(1:ℝ)) Z (g.μ/64) q)) j.val)
      (fun _=>E) (fun _=>1) := by
    simpa only [geometryMainOrdinaryDatum] using hn
  have hp:=hcZ.2 hZ T η₀ θ w σ freq hσ bΦ state hη p t X₁ X₂ hX₁ hX₂
    hw hwm hwin Ψ reflected key firstHeight
    (fun _=>χ₀) (fun _=>E) (fun _=>1) (fun _ _=>hE) (fun _ _=>by norm_num)
    (by simpa only [datum,selected,s,amp,beta] using hnorm)
  have hratioZ:=hrZ.2 hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwin
  have hratioPaid : ratio≤Cb*E*Z^g.δ := by
    simpa only [ratio,datum,selected,s,amp,beta] using
      (hratioZ.2.2 reflected key firstHeight).2.1 E hE A
  have hprime:=(hpZ.2 hZ T η₀ θ w σ freq hσ bΦ state p t X₁ X₂ hX₁ hX₂
    hw hwm hwin).2.1
  have hcount : Fintype.card T≤N :=
    (Fintype.card_le_of_injective (fun i : T=>i.val) Subtype.val_injective).trans hN
  have htargets:=affine_main_final_branch_exponents g εaffine hε hμ (Fintype.card T) N hcount
    B L amp omega mesh hB hL hδ hfZ.2.2 hmeshμ
  have hex : Ce*geometryAffineExceptionalShell reflected Z key*(p.control SE)^2*
      (1+‖firstHeight‖)^dE*Z^(-(1/100:ℝ))≤Ce*control*Z^(-((Cycle63.AffineLedger.lowReserve/2):ℝ)) := by
    rw [geometry_affine_exceptional_shell_eq (Fintype.card T) Z hZ]
    have hprofile:=pow_le_pow_left₀ (p.control_nonneg SE) (profile_control_mono p hSE) 2
    have hbase : (1+‖firstHeight‖)^dE≤(1+|firstHeight|+height)^D := by
      rw [Real.norm_eq_abs]
      exact (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith [abs_nonneg firstHeight]) hdE)
    have hpow:=Real.rpow_le_rpow_of_exponent_le hZ.le
      geometry_affine_main_reserve_half
    have hh : Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control SE)^2*
        (1+‖firstHeight‖)^dE≤Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control S)^2*
        (1+|firstHeight|+height)^D :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprofile (mul_nonneg hCe.le hside.le))
        hbase (pow_nonneg (by positivity) _) (by positivity)
    have hm:=mul_le_mul hh hpow (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by positivity)
    convert hm using 1;dsimp only [control];ring
  have hcell:=Cycle63.AffineLedger.originalCell_mem ⟨hwin.slots_ge,hwin.slots_le⟩
  have hb:=Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1
  have hcoef:=geometry_affine_main_amplifier_bound beta hb
  exact geometry_affine_main_contracted_payment Z (P.card:ℝ) amp g.δ low high (-((Cycle63.AffineLedger.lowReserve/2)))
    ((amplifierCap 2 0 1+6*amp)/(amp/2)) geometryAmplifierCoefficientCap Cb Ksel KL KH Ce Co control
    _ _ ratio hZ hprime hcoef.1 hcoef.2 hCb.le hKsel.le hKL hKH hCo.le hcontrol
    (by simpa only [P,s,amp,beta,ratio,datum,selected,mul_assoc] using hp) hex hratioPaid htargets.1 htargets.2

variable [Cycle63.AffineLedger] in
/-- The retained main estimate at a parent with the HIGH part of the second transform left as a given: the paid LOW part, and a
term that is linear in the bound `CH` of the HIGH rows. `CH` is any non-negative real chosen after `Z` and the parent; the
saving carries the radial deficit `1 - Mrow`. -/
theorem actual_affine_main_parent_component_payment_linear
    (A dl dh : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<Cycle63.AffineLedger.amplifierFloor/2)
    (g : GeometryAffineLowSchedule)(hμ : g.μ=geometryLossUnit 1 εaffine)
    (N : ℕ)(hN : Fintype.card α≤N)(B L : ℝ)(hB : 0≤B)(hL : 0≤L)
    (hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 B L N)(hmeshμ : mesh≤g.μ/8)
    (Qfix : Ideal O)(hQ : Qfix≠0)(hQt : Qfix≠⊤)(hQ72 : Qfix≤Ideal.span {(72:O)})
    (KL : ℝ)(hKL : 0≤KL)(Cs : ℝ)(hCs : 1≤Cs) :
    ∃Ksel : ℝ,0<Ksel ∧ ∃Cm : ℝ,0≤Cm ∧ ∃Chigh : ℝ,0≤Chigh ∧
    ∃SE : Finset (ℕ×ℕ),∃dE : ℕ,∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(hZ : 1<Z)(T : Finset α)(s : Input T)(p : Profiles (1/4) (9/4))
      (caps : GeometryAffineExceptionalSourceGates s p (Fintype.card T) Cs Z)
      (η₀ : Character)(θ : T→RayQuotient.Characters M H)(w σ freq : T→ℝ),
      CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W 2 Z →
    ∀(R seed : Ideal O)(Mrow : ℝ),R≠0 → Squarefree seed → (R.absNorm:ℝ)≤Z^(20:ℝ) → 0≤ Mrow →
      Mrow≤1 → Mrow+Real.logb Z (s.η.modulus.absNorm:ℝ)≤1+g.μ/16 →
      (∀j,w j ≤ mesh) →
      (Cycle63.AffineLedger.slotFloor≤∑j,Real.logb Z (s.P j) ∧
        (∑j,Real.logb Z (s.P j))≤Cycle63.AffineLedger.slotTop) →
      length Z s.X₁+length Z s.X₂+Cycle63.AffineLedger.lam*(∑j,Real.logb Z (s.P j))≤
        Cycle63.AffineLedger.B →
    ∀beta : ℝ,beta=Cycle63.AffineLedger.cellUpper
        (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))) →
    ∀(S : Finset (ℕ×ℕ))(D : ℕ),SE⊆S → dE≤D →
    ∀(Ψ : 𝓢(ℝ,ℂ))(reflected : Bool)(key : ℤ×(Fin 5→ℤ))(firstHeight height : ℝ),0≤height →
    ∀χ₀ : RayCharacter,
    let amp:=Cycle63.AffineLedger.amp beta
    let P:=CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^amp)
    let omega:=frequencyLoss Z 32 (g.μ/64)+g.μ/8
    let low:=geometryAffineLowTarget g (Fintype.card T) amp omega mesh+(1-Mrow)
    let control:=(p.control S)^2*geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(1+|firstHeight|+height)^D
    ∀CH : ℝ,0≤CH →
    GeometryAffineMainSelectedBranches g.δ (g.μ/64) Z amp (g.μ/8) firstHeight
      ((KL*control)*Z^low) CH dl dh hZ reflected s R seed Mrow key Ψ χ₀ Qfix fixedBadMask
      caps.zero₁ caps.zero₂ →
    (56/(P.card:ℝ))*((amplifierCap 2 0 1+6*amp)/(amp/2))*
      ‖geometryMainRetainedSum reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8) (9/4)
        firstHeight hZ key Mrow (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z (g.μ/64) q))‖≤
      Cm*control*Z^(-((Cycle63.AffineLedger.lowReserve/2):ℝ)+(1-Mrow))+Chigh*Z^(3*g.δ-amp)*CH := by
  obtain ⟨Ksel,hKsel,hselection⟩:=uniform_actual_affine_physical_selection (α:=α) Cs g.δ (g.μ/64) hCs
    g.δ_pos (div_nonneg g.μ_pos.le (by norm_num))
  obtain ⟨Ce,hCe,SE,dE,Co,hCo,hcontract⟩:=actual_affine_main_parent_retained_contraction (α:=α)
    M H hH A (max dl dh) (max dl dh) hc hs Sbad hbad W εaffine mesh hε hmesh
    Qfix hQ hQt hQ72 fixedBadMask fixedBadMask_ne_zero (dvd_mul_right _ _) (dvd_mul_left _ _) Cs
  obtain ⟨Cb,hCb,hratio⟩:=uniform_actual_affine_main_parent_ratio_payment (α:=α) Cs εaffine g.δ hε g.δ_pos
  have hpool:=eventual_affine_cell_prime_pools M H hH Sbad hbad g.δ g.δ_pos
  refine ⟨Ksel,hKsel,Ce+Co*(56*geometryAmplifierCoefficientCap*Cb*Ksel*KL),by have := geometryAmplifierCoefficientCap_pos;positivity,
    Co*(56*geometryAmplifierCoefficientCap*Cb*Ksel),by have := geometryAmplifierCoefficientCap_pos;positivity,SE,dE,?_⟩
  filter_upwards [hselection,hcontract,hratio,hpool,eventual_geometry_small_frequency g.μ g.μ_pos]
    with Z hsel hcZ hrZ hpoolZ hfZ
  rw [←hμ] at hcZ hrZ
  refine ⟨hcZ.1,?_⟩
  intro hZ T s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit hwm hzslot haff
    beta hbeta S D hSE hdE Ψ reflected key firstHeight height hheight χ₀ amp P omega low control CH hCH
    hbranches
  have hside : 0<geometryHighFactor reflected
      (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key :=
    geometry_high_factor_pos reflected _ key (by unfold geometrySupportConstant;positivity)
  have hcontrol : 0≤ control := by dsimp only [control];positivity
  have hcell:=Cycle63.AffineLedger.originalCell_mem hzslot
  have hb : Cycle63.AffineLedger.firstCellTop≤beta ∧ beta≤Cycle63.AffineLedger.slotTop := by
    rw [hbeta]
    exact Cycle63.AffineLedger.cellUpper_bounds hcell.1 hcell.2.1
  have hamp0 : 0≤amp := (Cycle63.AffineLedger.amp_pos hb).le
  have hamp3 : amp≤3 := (Cycle63.AffineLedger.amp_bounds hb).2.trans
    (by linarith only [Cycle63.AffineLedger.amplifierCap_le_one])
  have hcoef:=geometry_affine_main_amplifier_bound beta hb
  have hn:=actual_affine_main_normalized_of_selected_low_high Cs g.δ (g.μ/64) Ksel Z
    ((KL*control)*Z^low) CH dl dh hZ hKsel.le (by positivity) hCH (hsel T) reflected s p caps R seed Mrow
    hseed hMrow amp (g.μ/8) firstHeight key Ψ χ₀ Qfix fixedBadMask ballProfile caps.zero₁ caps.zero₂ hbranches
  let selected:=geometryMainNonzeroBlocks reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8) (9/4)
    firstHeight (Fintype.card T) hZ key caps.zero₁ caps.zero₂
  let datum:=fun j : selected=>geometryLowSecondDatum reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8)
    (9/4) firstHeight (Fintype.card T) hZ key j.val.1 caps.zero₁ caps.zero₂ j.val.2
  let E:=Ksel*Z^g.δ*((KL*control)*Z^low+CH)
  have hE : 0≤E := by dsimp only [E];positivity
  let ratio:=∑r∈secondRatioBins (fun j=>(datum j).block),E/(1+dyadicScale r)^A
  have hnorm : SecondNormalizedBound ballProfile (max dl dh) (max dl dh)
      (fun j=>ordinarySecondDatum (datum j) χ₀ Qfix fixedBadMask)
      (fun j=>geometryMainSecondWeight reflected s R seed Z Mrow amp (g.μ/64) (g.μ/8) (9/4)
        firstHeight (Fintype.card T) hZ key Mrow (Real.logb Z (volume s))
        (fun q=>normPhase (coordinateBlock s R seed Ψ (Z^Mrow) Z (g.μ/64) q)) j.val)
      (fun _=>E) (fun _=>1) := by
    simpa only [geometryMainOrdinaryDatum] using hn
  have hp:=hcZ.2 hZ T s p caps η₀ θ w σ freq hmatch R seed Mrow hR hseed hRcap hMrow hMrow1 hfit hwm
    hzslot haff beta hbeta Ψ reflected key firstHeight (fun _=>χ₀) (fun _=>E) (fun _=>1)
    (fun _ _=>hE) (fun _ _=>by norm_num) (by simpa only [datum,selected] using hnorm)
  have hratioPaid : ratio≤Cb*E*Z^g.δ := by
    simpa only [ratio,datum,selected] using
      ((hrZ.2 hZ T s p caps R seed Mrow amp hseed hMrow (by linarith only [hMrow1]) hamp0 hamp3 reflected
        key firstHeight).2.1 E hE A)
  have hprime : Z^(amp-g.δ)≤(P.card:ℝ) := by
    have hh:=(hpoolZ.2 (Cycle63.AffineLedger.originalCell (∑j,Real.logb Z (s.P j))) hcell.1 hcell.2.1).2
    simpa only [P,amp,hbeta] using hh
  have hcount : Fintype.card T≤N :=
    (Fintype.card_le_of_injective (fun i : T=>i.val) Subtype.val_injective).trans hN
  have htargets:=affine_main_final_branch_exponents g εaffine hε hμ (Fintype.card T) N hcount
    B L amp omega mesh hB hL hδ hfZ.2.2 hmeshμ
  have hN1 : (1:ℝ)≤(seed.absNorm:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hseed.ne_zero)
  have hex : Ce*geometryAffineExceptionalShell reflected Z key*(p.control SE)^2*
      (1+‖firstHeight‖)^dE*Z^(-(1/100:ℝ)+(1-Mrow))/(seed.absNorm:ℝ)≤
      Ce*control*Z^(-((Cycle63.AffineLedger.lowReserve/2):ℝ)+(1-Mrow)) := by
    rw [geometry_affine_exceptional_shell_eq (Fintype.card T) Z hZ]
    have hprofile:=pow_le_pow_left₀ (p.control_nonneg SE) (profile_control_mono p hSE) 2
    have hbase : (1+‖firstHeight‖)^dE≤(1+|firstHeight|+height)^D := by
      rw [Real.norm_eq_abs]
      exact (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
        (pow_le_pow_right₀ (by linarith [abs_nonneg firstHeight]) hdE)
    have hpow:=Real.rpow_le_rpow_of_exponent_le hZ.le
      (by linarith only [geometry_affine_main_reserve_half] :
        -(1/100:ℝ)+(1-Mrow)≤-((Cycle63.AffineLedger.lowReserve/2):ℝ)+(1-Mrow))
    have hh : Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control SE)^2*
        (1+‖firstHeight‖)^dE≤Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control S)^2*
        (1+|firstHeight|+height)^D :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprofile (mul_nonneg hCe.le hside.le))
        hbase (pow_nonneg (by positivity) _) (by positivity)
    have hm:=mul_le_mul hh hpow (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) (by positivity)
    have hX : 0≤Ce*geometryHighFactor reflected
        (geometrySupportConstant (Fintype.card T) 1 (1/4) (1/4)) key*(p.control SE)^2*
        (1+‖firstHeight‖)^dE*Z^(-(1/100:ℝ)+(1-Mrow)) := by positivity
    refine (div_le_self hX hN1).trans ?_
    convert hm using 1;dsimp only [control];ring
  exact geometry_affine_main_contracted_payment_linear Z (P.card:ℝ) amp g.δ low
    (-((Cycle63.AffineLedger.lowReserve/2):ℝ)+(1-Mrow))
    ((amplifierCap 2 0 1+6*amp)/(amp/2)) geometryAmplifierCoefficientCap Cb Ksel KL CH Ce Co control
    _ _ ratio hZ hprime hcoef.1 hcoef.2 hCb.le hKsel.le hKL hCH hCo.le hcontrol
    (by simpa only [P,amp,ratio,datum,selected,mul_assoc] using hp) hex hratioPaid
    (by dsimp only [low];linarith only [htargets.1])

end CanonicalHigh

end
end OAI.SevenEighths.Cycle63InitialMass
