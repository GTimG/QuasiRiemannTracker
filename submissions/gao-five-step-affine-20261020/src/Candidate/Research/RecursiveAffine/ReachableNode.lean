/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ReachableGeometry
import Candidate.Research.RecursiveAffine.RegionalStageSchedule
import Candidate.Research.RecursiveAffine.PrefixHighPresentation
import Candidate.Research.RecursiveAffine.DepthReturnedFamily
import Candidate.Research.RecursiveAffine.DecoratedHistory
import Candidate.Research.RecursiveAffine.ActualFamilyRebase
import Candidate.Research.RecursiveAffine.NativePaidPathNode
import Candidate.Research.RecursiveAffine.NativeCoarseSource
import Candidate.Cycle63.Physical.InitialSourceReduction

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators ContDiff HeckeNotation
open HeckeFamily RayFourExpansion CenteredMomentEnergyState
open CenteredMomentEnergyBands QuadraticInitialBound
open CenteredMomentNaturalFixedRaySource CenteredMomentFiniteProfileExceptional
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData
open CenteredMomentFirstSourceReduction CenteredMomentInductionEnergy
open Cycle63InitialSource Cycle63Moment Cycle153HighProvider Cycle153SourceReturn
open Cycle153JointCount Cycle153ReachableGeometry Cycle153Geometry

/-- The first inner state has already passed the root two-ray transform. -/
def PrefixBase : ℕ → Type
  | 0 => RayCharacter × RayCharacter
  | n+1 => PrefixBase n × (RayCharacter × RayCharacter)

def prefixDictionary : (n : ℕ) → Character → PrefixBase n → Character
  | 0, η => secondFixedDictionary η
  | n+1, η => extendFixedDictionary (prefixDictionary n η)

/-- A terminal HIGH consumes one additional two-ray dictionary. -/
def SuffixDepth : ℕ → Type
  | 0 => Empty
  | n+1 => Option (SuffixDepth n)

instance suffixFintype : (n : ℕ) → Fintype (SuffixDepth n)
  | 0 => inferInstanceAs (Fintype Empty)
  | n+1 => by
    letI := suffixFintype n
    exact inferInstanceAs (Fintype (Option (SuffixDepth n)))

def innerStage (n : ℕ) : Cycle153.RegionalStage :=
  match n with
  | 0 => Cycle153.FixedStages.stage1
  | 1 => Cycle153.FixedStages.stage2
  | 2 => Cycle153.FixedStages.stage3
  | _ => Cycle153.FixedStages.stage4

def modelUnit (j : Fin 4) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.U1 x, Coordinates.U2 x, Coordinates.U3 x, Coordinates.U4 x] j

def modelLength (j : Fin 4) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.A1 x, Coordinates.A2 x, Coordinates.A3 x, Coordinates.A4 x] j

def modelSlots (j : Fin 4) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.z1 x, Coordinates.z2 x, Coordinates.z3 x, Coordinates.z4 x] j

def modelMissing (j : Fin 4) (x : Fin 14→ℝ) : ℝ :=
  ![Coordinates.historicalMissing1 x,Coordinates.historicalMissing2 x,
    Coordinates.historicalMissing3 x,Coordinates.historicalMissing4 x] j

def modelReduction (j : Fin 4) (x : Fin 14→ℝ) : ℝ :=
  ![Coordinates.historicalReduction1 x,Coordinates.historicalReduction2 x,
    Coordinates.historicalReduction3 x,Coordinates.historicalReduction4 x] j

def modelPlane (j : Fin 4) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.inner0*Coordinates.U1 x,Coordinates.inner1*Coordinates.U2 x,
    Coordinates.inner2*Coordinates.U3 x,
    Coordinates.A4 x+((innerStage 3).lam-1)*Coordinates.z4 x] j

def suffixJunction : (start count : ℕ) → SuffixDepth count → ℝ
  | _, 0 => fun d => nomatch d
  | start, count+1 => fun d => match d with
    | none => (innerStage start).q
    | some d => suffixJunction (start+1) count d

def suffixBase : (start count : ℕ) → SuffixDepth count → Type
  | _, 0 => fun d => nomatch d
  | start, count+1 => fun d => match d with
    | none => PrefixBase (start+1)
    | some d => suffixBase (start+1) count d

def suffixDictionary : (start count : ℕ) → (d : SuffixDepth count) →
    Character → suffixBase start count d → Character
  | _, 0 => fun d => nomatch d
  | start, count+1 => fun d => match d with
    | none => prefixDictionary (start+1)
    | some d => suffixDictionary (start+1) count d

def suffixOffset : (count : ℕ) → SuffixDepth count → ℕ
  | 0, d => nomatch d
  | _+1, none => 0
  | count+1, some d => suffixOffset count d+1

theorem suffixOffset_lt : ∀ count (d : SuffixDepth count), suffixOffset count d < count
  | 0, d => nomatch d
  | count+1, none => by simp only [suffixOffset]; omega
  | count+1, some d => by
    have h := suffixOffset_lt count d
    simp only [suffixOffset]
    omega

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- Data fixed before any moving daughter state. Surviving slots always
refer to this original ray dictionary; a continuation only divides their
original exponents by its actual unit. -/
structure SourceContext where
  globalBase : ℝ
  globalBase_gt_one : 1 < globalBase
  etaSeed : Character
  Q : Ideal O
  Q_le_M : Q ≤ M
  fixed_small : internalQ Q etaSeed ≤ Ideal.span {(72:O)}
  W : ℝ → ℂ
  W_smooth : ContDiff ℝ ∞ W
  W_support : Function.support W ⊆ Set.Icc (1:ℝ) 2
  theta : α → RayQuotient.Characters M H
  originalWeight : α → ℝ
  originalWeight_nonneg : ∀ i, 0 ≤ originalWeight i
  sigma : α → ℝ
  sigma_fixed : ∀ i, sigma i ∈ Set.Icc (33/50:ℝ) (33/50)
  frequency : α → ℝ
  gridDenominator : ℕ
  grid_positive : 0 < gridDenominator
  slotMesh : ℝ
  slotMesh_pos : 0 < slotMesh
  slotMesh_grid : slotMesh ≤ 1/gridDenominator
  originalWeight_mesh : ∀ i, originalWeight i ≤ (1/50:ℝ)*slotMesh
  Bnorm : ℝ
  normCap_nonneg : 0 ≤ Bnorm
  normCap_large : (200130:ℝ) ≤ Bnorm
  highClassCap : ℝ
  highClassCap_nonneg : 0 ≤ highClassCap
  Tz : ℝ

variable {M H hH}

abbrev SuffixFamily (start count : ℕ) (eta : Character) (Z Bnorm Tz : ℝ) (root : O) :=
  DepthReturnedFamily M H hH (suffixJunction start count) (suffixBase start count)
    (suffixDictionary start count) eta Z Bnorm Tz root

theorem suffixFamily_transport_value {start count : ℕ} {eta : Character}
    {Z Z' Bnorm Tz : ℝ} {root : O} (he : Z = Z')
    (F : SuffixFamily (hH:=hH) start count eta Z Bnorm Tz root) :
    (he ▸ F).value = F.value := by
  cases he
  rfl

/-- The recursive dictionaries are definitionally the dictionaries of
the native attachment operator; no cast of HIGH witnesses is introduced. -/
def attachSuffixFamily {I : Type} [Fintype I] {start count : ℕ}
    {eta : Character} {Z Bnorm Tz : ℝ} {root : O}
    (own : ReturnedPartAt M H hH (innerStage start).q
      (prefixDictionary (start+1)) eta Z Bnorm Tz root)
    (ownWeight : ℝ) (hOwnWeight : 0 ≤ ownWeight)
    (childRoot : I → O) (hChildRoot : ∀ r, root ∣ childRoot r)
    (children : (r : I) → SuffixFamily (hH:=hH) (start+1) count eta Z Bnorm Tz (childRoot r))
    (edge missing : I → ℝ) (hEdge : ∀ r, 0 ≤ edge r) (hMissing : ∀ r, 0 ≤ missing r) :
    SuffixFamily (hH:=hH) start (count+1) eta Z Bnorm Tz root := by
  let A := DepthReturnedFamily.attach own ownWeight hOwnWeight childRoot hChildRoot children
    edge missing hEdge hMissing
  exact {
    Prefix := A.Prefix
    prefixFintype := A.prefixFintype
    multiplier := A.multiplier
    root_divides := A.root_divides
    historyMissing := A.historyMissing
    historyMissing_nonneg := A.historyMissing_nonneg
    part := fun d => by
      cases d with
      | none => exact A.part none
      | some d => exact A.part (some d)
    weight := A.weight
    weight_nonneg := A.weight_nonneg }

theorem attachSuffixFamily_value {I : Type} [Fintype I] {start count : ℕ}
    {eta : Character} {Z Bnorm Tz : ℝ} {root : O}
    (own : ReturnedPartAt M H hH (innerStage start).q
      (prefixDictionary (start+1)) eta Z Bnorm Tz root)
    (ownWeight : ℝ) (hOwnWeight : 0 ≤ ownWeight)
    (childRoot : I → O) (hChildRoot : ∀ r, root ∣ childRoot r)
    (children : (r : I) → SuffixFamily (hH:=hH) (start+1) count eta Z Bnorm Tz (childRoot r))
    (edge missing : I → ℝ) (hEdge : ∀ r, 0 ≤ edge r) (hMissing : ∀ r, 0 ≤ missing r) :
    (attachSuffixFamily own ownWeight hOwnWeight childRoot hChildRoot children
      edge missing hEdge hMissing).value = ownWeight*own.value + ∑ r, edge r*(children r).value := by
  calc
    _ = (DepthReturnedFamily.attach own ownWeight hOwnWeight childRoot hChildRoot children
      edge missing hEdge hMissing).value := by
        unfold DepthReturnedFamily.value
        apply Finset.sum_congr (Finset.ext (fun d =>
          ⟨fun _ => Finset.mem_univ d, fun _ => Finset.mem_univ d⟩))
        intro d hd
        cases d <;> rfl
    _ = _ := DepthReturnedFamily.value_attach own ownWeight hOwnWeight childRoot hChildRoot children
      edge missing hEdge hMissing

/-- The first inner prefix and each subsequent literal two-ray step
use at most one fixed thousand of global norm exponent. This arithmetic
cap is independent of the returned-count norm cap. -/
def prefixCap (n : ℕ) : ℝ := 1000*((n:ℝ)+1)

theorem prefixCap_succ (n : ℕ) : prefixCap (n+1)=prefixCap n+1000 := by
  simp only [prefixCap,Nat.cast_add,Nat.cast_one]
  ring

theorem prefixCap_le_four (j : Fin 4) : prefixCap j.val ≤ 4000 := by
  have hj : (j.val:ℝ) ≤ 3 := by exact_mod_cast (show j.val ≤ 3 by omega)
  dsimp only [prefixCap]
  linarith only [hj]

/-- An actual reachable inner source. There is no energy estimate,
returned count, child family, or desired endpoint among its fields. The
physical child constructor must supply the literal prefix and source
geometry; only the inequalities visible at the present depth are kept. -/
structure ReachableNode (C : SourceContext (α:=α) M H) (j : Fin 4) where
  coordinates : Fin 14 → ℝ
  prefixRows : PrefixRows (j.val+1) coordinates
  physical_nonnegative : ∀ i : Fin 48, 35 ≤ i.val → 0 ≤ Coordinates.rows i coordinates
  unit : ℝ
  unit_eq : unit = modelUnit j coordinates
  unit_floor : (1/50:ℝ) ≤ unit
  unit_le_one : unit ≤ 1
  localBase : ℝ
  localBase_eq : localBase = C.globalBase^unit
  slots : Finset α
  state : NaturalState localBase 20 2
  fixedModulus : state.fixedModulus = internalQ C.Q C.etaSeed
  width_le_one : state.width ≤ 1
  puncture_global_log : Real.logb C.globalBase (state.puncture.absNorm:ℝ) ≤
    modelMissing j coordinates+modelReduction j coordinates+((j.val:ℝ)+1)/1000000000000000
  presentation : PrefixHighPresentation (prefixDictionary j.val C.etaSeed)
    state.character state.puncture
  presentation_global_norm : ((Ideal.span {presentation.mult}).absNorm:ℝ) ≤
    C.globalBase ^ prefixCap j.val
  profiles : Profiles (1/4) (9/4)
  X1 : ℝ
  X2 : ℝ
  X1_pos : 0 < X1
  X2_pos : 0 < X2
  length_eq : unit*(length localBase X1+length localBase X2+
    ∑ i : slots, C.originalWeight i/unit) = modelLength j coordinates
  slots_eq : (∑ i : slots, C.originalWeight i) = modelSlots j coordinates
  t : ℝ
  height : ℝ
  height_nonneg : 0 ≤ height
  frequency_bound : ∀ i : slots, |C.frequency i| ≤ height
  plane : ℝ
  plane_eq : plane = modelPlane j coordinates/unit
  position : Cycle153.RegionalPosition
  rounded : position = Cycle153.roundedPosition (1/C.gridDenominator) plane
    (length localBase X1) (length localBase X2)
    (∑ i : slots, C.originalWeight i/unit)
  positionFacts : position.Facts (innerStage j.val)
  weight_mesh : ∀ i : slots, C.originalWeight i/unit ≤ C.slotMesh
  window : @Cycle63.AffineLedger.PlainWindow
    (Cycle153.regionalLedger (innerStage j.val) position positionFacts)
    (length localBase X1) (length localBase X2)
    (∑ i : slots, C.originalWeight i/unit)
  overshoot : length localBase X1 + length localBase X2 +
    6*Cycle63.Optimization.slotPrice*(∑ i : slots, C.originalWeight i/unit) ≤ 1+9/1000

namespace ReachableNode
variable {C : SourceContext (α:=α) M H} {j : Fin 4} (N : ReachableNode C j)
variable (hH)

theorem unit_pos : 0 < N.unit := lt_of_lt_of_le (by norm_num) N.unit_floor

theorem weight_mesh_derived (i : N.slots) : C.originalWeight i/N.unit ≤ C.slotMesh := by
  apply (div_le_iff₀ N.unit_pos).mpr
  exact (C.originalWeight_mesh i).trans
    (by nlinarith only [N.unit_floor,C.slotMesh_pos])

theorem localBase_gt_one : 1 < N.localBase := by
  rw [N.localBase_eq]
  exact Real.one_lt_rpow C.globalBase_gt_one N.unit_pos

/-- The local HIGH cap follows from the true global per-depth prefix
invariant. It is not an independent condition at every contracted base. -/
theorem presentation_norm :
    ((Ideal.span {N.presentation.mult}).absNorm:ℝ) ≤ N.localBase^(C.Bnorm-130) := by
  have hB : 0 ≤ C.Bnorm-130 := by linarith only [C.normCap_large]
  have hexp : prefixCap j.val ≤ N.unit*(C.Bnorm-130) := by
    have hm := mul_le_mul_of_nonneg_right N.unit_floor hB
    have hb : (4000:ℝ) ≤ (1/50:ℝ)*(C.Bnorm-130) := by
      linarith only [C.normCap_large]
    exact (prefixCap_le_four j).trans (hb.trans hm)
  calc
    ((Ideal.span {N.presentation.mult}).absNorm:ℝ) ≤ C.globalBase^prefixCap j.val :=
      N.presentation_global_norm
    _ ≤ C.globalBase^(N.unit*(C.Bnorm-130)) :=
      Real.rpow_le_rpow_of_exponent_le C.globalBase_gt_one.le hexp
    _ = N.localBase^(C.Bnorm-130) := by
      rw [N.localBase_eq,← Real.rpow_mul (zero_lt_one.trans C.globalBase_gt_one).le]

@[instance_reducible] def ledger : Cycle63.AffineLedger :=
  Cycle153.regionalLedger (innerStage j.val) N.position N.positionFacts

/-- The same actual affine input used by the HIGH provider and AtState. -/
def input : Input N.slots := by
  letI := N.ledger
  exact affineInput M H hH C.etaSeed (fun i => C.theta i) C.W C.W_smooth.continuous
    1 2 (33/50) (33/50) (by norm_num) C.W_support
    (fun i => C.originalWeight i/N.unit) (fun i => C.sigma i) (fun i => C.frequency i)
    (fun i => C.sigma_fixed i) N.state N.profiles (by norm_num)
    (Cycle63.AffineLedger.comparisonLength
      (length N.localBase N.X1) (length N.localBase N.X2)
      (∑ i : N.slots, C.originalWeight i/N.unit)) N.t N.X1 N.X2 N.X1_pos N.X2_pos

def sourceEnergy : ℝ :=
  energy (N.input hH).η N.state.mask 1 (N.input hH).t (N.input hH).W₁ (N.input hH).W₂
    (N.input hH).slots (N.input hH).coefficient (N.input hH).P (N.input hH).X₁ (N.input hH).X₂
    N.state.radial.keep N.state.radial.profile N.state.radial.scale

abbrev Family := SuffixFamily (hH:=hH) j.val (4-j.val)
  C.etaSeed N.localBase C.Bnorm C.Tz N.presentation.mult

theorem localBase_relative {k : Fin 4} (child : ReachableNode C k) :
    child.localBase = N.localBase^(child.unit/N.unit) := by
  rw [N.localBase_eq,child.localBase_eq]
  rw [← Real.rpow_mul (zero_lt_one.trans C.globalBase_gt_one).le]
  congr 1
  field_simp [ne_of_gt N.unit_pos]

/-- Exact base transport of the entire selected child forest. Its
weights, records, source keys and root multiplier are retained, its value
is unchanged, and Bnorm is the same fixed cap. -/
def rebaseChildFamily {k : Fin 4} (child : ReachableNode C k)
    (hunit : child.unit ≤ N.unit) (F : child.Family hH) :
    SuffixFamily (hH:=hH) k.val (4-k.val) C.etaSeed N.localBase C.Bnorm C.Tz
      child.presentation.mult := by
  have hF : SuffixFamily (hH:=hH) k.val (4-k.val) C.etaSeed
      (N.localBase^(child.unit/N.unit)) C.Bnorm C.Tz child.presentation.mult :=
    (N.localBase_relative child) ▸ F
  exact Cycle153RegionalLow.rebaseDepthReturnedFamily N.localBase_gt_one
    (div_pos child.unit_pos N.unit_pos) ((div_le_one N.unit_pos).mpr hunit)
    C.normCap_nonneg hF

theorem rebaseChildFamily_value {k : Fin 4} (child : ReachableNode C k)
    (hunit : child.unit ≤ N.unit) (F : child.Family hH) :
    (N.rebaseChildFamily hH child hunit F).value = F.value := by
  unfold rebaseChildFamily
  rw [Cycle153RegionalLow.rebaseDepthReturnedFamily_value]
  exact suffixFamily_transport_value (N.localBase_relative child) F

end ReachableNode

variable (hH)

/-- A finite orientation word is part of the literal path code. Source
maximizers may choose different reflections on different physical rows;
the provenance never assumes a common orientation for unrelated rows. -/
abbrev OrientationWord := Fin 4 → Bool

def wordLeft (word : OrientationWord) (k : ℕ) : Bool := word ⟨k%4,Nat.mod_lt _ (by norm_num)⟩

/-- Literal chronology, with only the sixteen possible orientation words
as an extra fixed finite partition. Residual allocations and deleted
subsets are selected source metadata, not additional path coordinates. -/
structure ForestChronology
    {C : SourceContext (α:=α) M H} {j : Fin 4} (N : ReachableNode C j)
    (F : N.Family hH) (Bsrc : ℝ) (boxes : ℕ → Finset (Fin 4 → ℤ)) where
  word : (d : SuffixDepth (4-j.val)) → F.Prefix d → OrientationWord
  word_padding : ∀ d p k, suffixOffset (4-j.val) d ≤ k.val → word d p k = false
  units : OrientationWord → ∀ k, History k → FirstSourceLabel → O
  code : (d : SuffixDepth (4-j.val)) → F.Prefix d → History (suffixOffset (4-j.val) d)
  injective : ∀ d, Function.Injective (fun p => (word d p,code d p))
  multiplier : ∀ d p, F.multiplier d p =
    historyMultiplier (units (word d p)) (wordLeft (word d p)) N.presentation.mult
      (suffixOffset (4-j.val) d) (code d p)
  missing : ∀ d p, F.historyMissing d p =
    historyMissing (wordLeft (word d p)) N.localBase (suffixOffset (4-j.val) d) (code d p)
  facts : ∀ d p, HistoryFacts (units (word d p)) (wordLeft (word d p))
    N.presentation.mult N.localBase Bsrc boxes (suffixOffset (4-j.val) d) (code d p)

/-- Literal non-mass-loss fees of one continuing source edge, in the
original global unit. Actual deletion, native target deletion and model
deletion remain distinct. Their inequalities are supplied by the native
whole-slot detector and the rounded fixed ledger. -/
structure NativePathFee where
  driverDelta : ℝ
  driverError : ℝ
  coefficientError : ℝ
  shellCost : ℝ
  sourcePad : ℝ
  slotLoss : ℝ
  junction : ℝ
  actualDeletion : ℝ
  nativeTargetDeletion : ℝ
  modelDeletion : ℝ
  primeMesh : ℝ
  primeMesh_nonneg : 0 ≤ primeMesh
  deletion_upper : actualDeletion ≤ nativeTargetDeletion+primeMesh
  roundingError : ℝ
  roundingError_nonneg : 0 ≤ roundingError
  target_eq : nativeTargetDeletion = modelDeletion+roundingError

def NativePathFee.amount (fee : NativePathFee) : ℝ :=
  3*fee.driverDelta+fee.driverError+fee.coefficientError+fee.shellCost+
    fee.sourcePad+fee.slotLoss+fee.junction*(fee.actualDeletion-fee.modelDeletion+fee.primeMesh)

def pathStage (n : ℕ) : Fin 4 := ⟨min n 3,by omega⟩

def pathV (n : ℕ) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.V1 x,Coordinates.V2 x,Coordinates.V3 x,0] (pathStage n)

def pathRed (n : ℕ) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.Red1 x,Coordinates.Red2 x,Coordinates.Red3 x,0] (pathStage n)

def pathDeletion (n : ℕ) (x : Fin 14 → ℝ) : ℝ :=
  ![Coordinates.d1 x,Coordinates.d2 x,Coordinates.d3 x,Coordinates.d4 x] (pathStage n)

def prefixCoordinate (depth : ℕ) (i : Fin 14) : Prop :=
  i.val=0 ∨ i.val=13 ∨ (1 ≤ i.val ∧ i.val ≤ depth) ∨
    (5 ≤ i.val ∧ i.val ≤ depth+4) ∨ (9 ≤ i.val ∧ i.val ≤ depth+8)

/-- Physical path provenance of the SAME selected terminal part. All
physical nodes and exponents are kept in C.globalBase units even when
the returned family is currently expressed at a smaller local base.
Consequently an exact family rebase preserves this data. The structure
contains no class bound, final payment inequality, source energy cap,
error-budget conclusion or scalar certificate conclusion. -/
structure ActualPathTrace
    {C : SourceContext (α:=α) M H} {j : Fin 4} (N : ReachableNode C j)
    {representedBase : ℝ} (representedUnit : ℝ)
    (F : SuffixFamily (hH:=hH) j.val (4-j.val) C.etaSeed representedBase C.Bnorm C.Tz N.presentation.mult)
    (d : SuffixDepth (4-j.val)) (p : F.Prefix d) where
  representedBase_eq : representedBase = C.globalBase^representedUnit
  representedUnit_pos : 0 < representedUnit
  count : ℕ
  count_eq : count = suffixOffset (4-j.val) d
  node : ℕ → NativePaidPathNode C.globalBase
  scale : ℕ → ℝ
  volumeLength : ℕ → ℝ
  amplification : ℕ → ℝ
  prefixLog : ℕ → ℝ
  fee : ℕ → NativePathFee
  missingCoordinate : ℕ → ℝ
  reductionCoordinate : ℕ → ℝ
  residualF : ℕ → ℝ
  capacityPad : ℕ → ℝ
  scalePad : ℕ → ℝ
  sourceGates : ∀ i, i < count → (node i).SourceGates
  fineSource : ∀ i, i < count → (node i).FineSourceGates
  fineFee : ∀ i, i < count → (fee i).amount ≤ 1/1000000000000
  fineScalePad : ∀ i, i < count → scalePad i ≤ 1/1000000000000
  fineCapacityPad : ∀ i, i < count → capacityPad i ≤ 1/1000000000000
  remainingFee : ∀ i, i < count → (fee i).junction*(fee i).modelDeletion+(fee i).amount ≤ 2
  node_eq : ∀ i, i < count → scale i = (node i).scale ∧
    volumeLength i = (node i).volumeLength ∧ amplification i = (node i).amplification
  root_scale : scale 0 = N.unit*N.state.rowWidth
  root_length : volumeLength 0 = N.unit*Real.logb N.localBase (volume (N.input hH))
  root_prefix : prefixLog 0 = Real.logb C.globalBase ((Ideal.span {N.presentation.mult}).absNorm:ℝ)
  terminal_scale : scale count = representedUnit*(F.part d p).scale
  terminal_length : volumeLength count = representedUnit*(F.part d p).length
  terminal_amp : amplification count = representedUnit*(F.part d p).amp
  terminal_prefix : prefixLog count = Real.logb C.globalBase ((Ideal.span {F.multiplier d p}).absNorm:ℝ)
  relative_scale : ∀ i, i < count → scale (i+1)+prefixLog (i+1)-prefixLog i ≤
    (node i).coordinate 2+scalePad i
  length_step : ∀ i, i < count → volumeLength (i+1) = volumeLength i-
    (fee i).modelDeletion-missingCoordinate i-reductionCoordinate i
  residualF_nonneg : ∀ i, i < count → 0 ≤ residualF i
  capacity : ∀ i, i < count → volumeLength (i+1) ≤ volumeLength i-
    (fee i).modelDeletion-(node i).commonLog-residualF i+capacityPad i
  weight : F.weight d p = ∏ i ∈ Finset.range count,
    C.globalBase^(scale i+(node i).shiftedOutside+(fee i).junction*(fee i).modelDeletion+(fee i).amount)
  missing : representedUnit*F.historyMissing d p = ∑ i ∈ Finset.range count, (node i).coordinate 1
  coordinates : Fin 14 → ℝ
  physical_prefix : PrefixRows (j.val+count+1) coordinates
  prefix_preserved : ∀ i, prefixCoordinate (j.val+1) i → coordinates i = N.coordinates i
  length_model : ∀ i, i ≤ count → volumeLength i = modelLength (pathStage (j.val+i)) coordinates
  unit_model : ∀ i, i < count → (node i).unit = modelUnit (pathStage (j.val+i)) coordinates
  junction_model : ∀ i, i < count → (fee i).junction = (innerStage (j.val+i)).q
  deletion_model : ∀ i, i < count → (fee i).modelDeletion = pathDeletion (j.val+i) coordinates
  missing_model : ∀ i, i < count → missingCoordinate i = pathV (j.val+i) coordinates
  reduction_model : ∀ i, i < count → reductionCoordinate i = pathRed (j.val+i) coordinates
  amplifierError : ℕ → ℝ
  amplifierError_nonneg : ∀ i, i ≤ count → 0 ≤ amplifierError i
  fineAmplifierError : ∀ i, i ≤ count → amplifierError i ≤ 1/1000000000000
  amplifier_model : ∀ i, i ≤ count → amplification i ≤
    ![Coordinates.a1 coordinates,Coordinates.a2 coordinates,Coordinates.a3 coordinates,Coordinates.a4 coordinates]
      (pathStage (j.val+i))+amplifierError i

/-- Fixed terminal loss allowance after the actual native HIGH loss,
subsequent exact operator shifts and base transports have been charged.
The producers establish this bound from their finite uniform schedules. -/
def terminalLossCap (j : Fin 4) : ℝ := (5-(j.val:ℝ))/1000000000000

theorem terminalLossCap_nonneg (j : Fin 4) : 0 ≤ terminalLossCap j := by
  have hj : (j.val:ℝ) ≤ 3 := by exact_mod_cast (show j.val ≤ 3 by omega)
  dsimp only [terminalLossCap]
  exact div_nonneg (by linarith only [hj]) (by norm_num)

theorem terminalLossCap_step {j k : Fin 4} (h : k.val=j.val+1) :
    terminalLossCap k+1/1000000000000=terminalLossCap j := by
  dsimp only [terminalLossCap]
  rw [h,Nat.cast_add,Nat.cast_one]
  ring

/-- Primitive terminal-source caps. The actual own-HIGH constructor
establishes these from its width, volume, amplifier and prefix norms;
source selection, record shifts and base transports retain them. -/
structure TerminalSourceCaps (scale length amp normLog : ℝ) : Prop where
  scale_le : scale ≤ 1
  length_le : length ≤ 4
  amp_le : amp ≤ 1
  normLog_le : normLog ≤ 250000

/-- Constants belong outside the moving source. The returned family
already contains every raw HIGH normalizer and LOW edge; no row-scale
factor is appended to its value here. -/
structure NodeOutput
    {C : SourceContext (α:=α) M H} {j : Fin 4} (N : ReachableNode C j)
    (constant ε Bsrc : ℝ) (control : Finset (ℕ×ℕ)) (degree : ℕ)
    (boxes : ℕ → Finset (Fin 4 → ℤ)) where
  family : N.Family hH
  chronology : ForestChronology hH N family Bsrc boxes
  path : ∀ d p, ActualPathTrace hH N N.unit family d p
  terminalLoss : ∀ d p, (family.part d p).loss ≤ terminalLossCap j
  terminalSource : ∀ d p, TerminalSourceCaps (family.part d p).scale
    (family.part d p).length (family.part d p).amp
    (Real.logb N.localBase ((Ideal.span {family.multiplier d p}).absNorm:ℝ))
  classCap : ∀ d p b, (Fintype.card ((family.part d p).record b).Class:ℝ) ≤ C.highClassCap
  energy : N.sourceEnergy hH ≤
    constant*diagonalControl N.state.radial.profile*(N.profiles.control control)^2*
      (1+|N.t|+N.height)^degree*(N.localBase^(1+ε)+family.value)

/-- The strict-depth callback expected by the actual LOW producer. This
is a definition of the induction objective, not a theorem assuming the
endpoint. The finite backward proof must construct these outputs. -/
def StrictDepthIH (C : SourceContext (α:=α) M H) (j : Fin 4)
    (constant ε Bsrc : Fin 4 → ℝ) (control : Fin 4 → Finset (ℕ×ℕ))
    (degree : Fin 4 → ℕ) (boxes : Fin 4 → ℕ → Finset (Fin 4 → ℤ)) : Prop :=
  ∀ k : Fin 4, j.val < k.val → ∀ N : ReachableNode C k,
    Nonempty (NodeOutput hH N (constant k) (ε k) (Bsrc k) (control k) (degree k) (boxes k))

end
end OAI.SevenEighths.Cycle153Reachable

#print axioms OAI.SevenEighths.Cycle153Reachable.ReachableNode.localBase_gt_one
#print axioms OAI.SevenEighths.Cycle153Reachable.suffixOffset_lt
#print axioms OAI.SevenEighths.Cycle153Reachable.attachSuffixFamily_value
#print axioms OAI.SevenEighths.Cycle153Reachable.ReachableNode.rebaseChildFamily_value
