/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.ActualNodeCoordinates
import Candidate.Research.RecursiveAffine.NativePhysicalCoordinates
import Candidate.Research.RecursiveAffine.PhysicalMaskBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153Reachable
noncomputable section
open scoped Classical BigOperators HeckeNotation
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSectorLocalization
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical CenteredMomentCommonProfile
open CenteredMomentCommonRawScale CenteredMomentAmplificationChildInput
open CenteredMomentAmplificationChildSourceCaps CenteredMomentAllocatedChildCapacity
open CenteredMomentDivisorRaw CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentSourceLiveColumn CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open Cycle63InitialMass Cycle63FinalLow Cycle63FinalNatural Cycle63FinalCapacity
open Cycle63Moment.LowBranch Cycle153RegionalLow Cycle153ContinuationUnit
open Cycle153Geometry Cycle153ReachableGeometry Cycle63.Optimization

variable {α : Type} [Fintype α] [DecidableEq α]
variable {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
variable {C : SourceContext (α:=α) M H} {j : Fin 4}

/-- The source-selected cell is the sole cell of this actual rounded ledger. -/
def nodeSourceAmp (N : ReachableNode C j) : ℝ := (innerStage j.val).amp N.position

def nodeRoundedDeletion (N : ReachableNode C j) : ℝ :=
  (planeGap (innerStage j.val).price (innerStage j.val).intercept
    (innerStage j.val).lam N.position.B N.position.slotTop+
    6*(innerStage j.val).intercept*nodeSourceAmp N)/(6*(innerStage j.val).price)

/-- The positive native deletion surcharge is separate from the grid and
from the detector's subsequent whole-slot mesh overshoot. -/
def nodeDetectorDeletion (N : ReachableNode C j) : ℝ :=
  nodeRoundedDeletion N+1/100000000000000000000

theorem nodeSourceAmp_eq_native (N : ReachableNode C j) :
    letI : Cycle63.AffineLedger := N.ledger
    Cycle63.AffineLedger.amp (Cycle63.AffineLedger.cellUpper
      (Cycle63.AffineLedger.originalCell (∑i : N.slots,C.originalWeight i/N.unit))) =
      nodeSourceAmp N := by
  letI : Cycle63.AffineLedger := N.ledger
  rw [regional_actual_cell N.positionFacts ⟨N.window.slots_ge,N.window.slots_le⟩]
  rfl

theorem nodeSourceAmp_bounds (N : ReachableNode C j) :
    modelAmplification j N.coordinates/N.unit ≤ nodeSourceAmp N ∧
    nodeSourceAmp N ≤ modelAmplification j N.coordinates/N.unit+42*(1/C.gridDenominator) := by
  have ha := actual_node_amp_bounds N
  rw [nodeSourceAmp_eq_native N] at ha
  exact ha

theorem nodeDetectorDeletion_bounds (N : ReachableNode C j) :
    pathDeletion j.val N.coordinates/N.unit+1/100000000000000000000 ≤ nodeDetectorDeletion N ∧
    nodeDetectorDeletion N ≤ pathDeletion j.val N.coordinates/N.unit+
      2200*(1/C.gridDenominator)+1/100000000000000000000 := by
  have hd := actual_node_deletion_bounds N
  change pathDeletion j.val N.coordinates/N.unit ≤ nodeRoundedDeletion N ∧
    nodeRoundedDeletion N ≤ pathDeletion j.val N.coordinates/N.unit+2200*(1/C.gridDenominator) at hd
  dsimp only [nodeDetectorDeletion]
  constructor <;> linarith only [hd.1,hd.2]

/-- Values measured at one actual physical source. Their positivity and
recurrences are consequences of the source-capacity theorem, not fields
assumed of a recursively desired child. All coordinates except `u` are
in the fixed original global base. -/
structure NativeNodeStepValues where
  u : ℝ
  V : ℝ
  Red : ℝ
  ell : ℝ
  childA : ℝ
  childSlots : ℝ
  pad : ℝ

def nativeNodeStepValues (N : ReachableNode C j)
    (s : Input N.slots) (ch : Chain s) (χ : Character) (t : ℝ)
    (n : ℕ) (b Mrow omega xi reserve : ℝ)
    (g : LiveMainGeometry s ch N.localBase Mrow (nodeSourceAmp N) omega xi b n)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (Rdel : Finset N.slots) : NativeNodeStepValues :=
  let w : N.slots→ℝ := fun i=>C.originalWeight i/N.unit
  let A := modelLength j N.coordinates/N.unit
  let D := pathDeletion j.val N.coordinates/N.unit
  let da := nodeSourceAmp N-modelAmplification j N.coordinates/N.unit
  let v := commonWidthLoss N.localBase ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
  let V := v+(Real.logb N.localBase 128+6*da)
  let Achild := length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 0)+
    length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 1)+
    (∑i∈ch.indices L alloc\Rdel,w i)
  let pad := 2*(n:ℝ)*Real.logb N.localBase b+
    Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂)
  { u := nativeUnit 1 N.localBase (nodeSourceAmp N) omega reserve xi ch.C₁ g.D₁
      g.datum.C g.datum.D g.datum.inactive
    V := N.unit*V
    Red := N.unit*(A-D-V-Achild)
    ell := N.unit*((∑i,w i)-(∑i∈ch.indices L alloc,w i)+((∑i∈Rdel,w i)-D))
    childA := N.unit*Achild
    childSlots := ∑i∈ch.indices L alloc\Rdel,C.originalWeight i
    pad := N.unit*pad }

/-- The actual inner source, its live geometry, attaining residual
allocation and true detector deletion yield the next unit and all three
physical recurrences. A fixed positive deletion surcharge pays the actual
finite source pad and amplifier rounding, so the retained reduction is
nonnegative. The puncture increment comes from the literal own first and
second ideals, and is rebased to the original global base exactly.

The thin source bindings are literal input fields; no desired child
capacity, energy estimate or `NextFacts` is an assumption. -/
theorem actual_inner_native_node_step (N : ReachableNode C j)
    (s : Input N.slots) (ch : Chain s) (χ : Character) (t : ℝ)
    (n : ℕ) (b Mrow omega xi reserve mesh : ℝ)
    (g : LiveMainGeometry s ch N.localBase Mrow (nodeSourceAmp N) omega xi b n)
    (hb : 1 ≤ b) (hcard : Fintype.card N.slots ≤ n)
    (hs : s.upper ≤ b) (hlower : 1 ≤ s.lower)
    (hX₁ : s.X₁=N.X1) (hX₂ : s.X₂=N.X2)
    (hscale : ∀i,s.P i=N.localBase^(C.originalWeight i/N.unit))
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (row : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final χ t).toSource second L alloc row≠0)
    (Rdel : Finset N.slots) (hRdel : Rdel ⊆ ch.indices L alloc) (hproper : Rdel≠ch.indices L alloc)
    (hcover : Rdel=ch.indices L alloc ∨ nodeDetectorDeletion N ≤ ∑i∈Rdel,C.originalWeight i/N.unit)
    (hdelmesh : (∑i∈Rdel,C.originalWeight i/N.unit) ≤ nodeDetectorDeletion N+mesh)
    (homega : omega=frequencyLoss N.localBase 32 xi+reserve*1)
    (hR₂ : ch.R₂=N.state.puncture*ch.C₁) (hPuncture : ch.R₂*ch.E₂≠0)
    (hfinite : Real.logb N.localBase 128+252*(1/C.gridDenominator)+
      (2*(n:ℝ)*Real.logb N.localBase b+
        Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000) :
    let r := nativeNodeStepValues N s ch χ t n b Mrow omega xi reserve g second L alloc Rdel
    0 ≤ r.V ∧ 0 ≤ r.Red ∧ 0 ≤ r.ell ∧
    N.unit*r.u=N.unit-6*modelAmplification j N.coordinates-r.V ∧
    r.childSlots=modelSlots j N.coordinates-pathDeletion j.val N.coordinates-r.ell ∧
    r.childA=modelLength j N.coordinates-pathDeletion j.val N.coordinates-r.V-r.Red ∧
    r.ell ≤ r.V+r.Red+r.pad ∧
    Real.logb C.globalBase ((ch.R₂*ch.E₂).absNorm:ℝ) ≤
      Real.logb C.globalBase (N.state.puncture.absNorm:ℝ)+r.V+r.Red+r.pad ∧
    r.pad ≤ 1/100000000000000000000 := by
  intro r
  let w : N.slots→ℝ := fun i=>C.originalWeight i/N.unit
  let A := modelLength j N.coordinates/N.unit
  let D := pathDeletion j.val N.coordinates/N.unit
  let aModel := modelAmplification j N.coordinates/N.unit
  let da := nodeSourceAmp N-aModel
  let v := commonWidthLoss N.localBase ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive
  let V := v+(Real.logb N.localBase 128+6*da)
  let Achild := length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 0)+
    length N.localBase (rawDaughterScale (ch.final χ t) second L alloc 1)+
      (∑i∈ch.indices L alloc\Rdel,w i)
  let pad := 2*(n:ℝ)*Real.logb N.localBase b+
    Real.logb N.localBase (max 1 s.b₁*max 1 s.b₂)
  let Red := A-D-V-Achild
  let ell := (∑i,w i)-(∑i∈ch.indices L alloc,w i)+((∑i∈Rdel,w i)-D)
  have hu0 := N.unit_pos
  have hz := N.localBase_gt_one
  have hdaBounds : 0 ≤ da ∧ da ≤ 42*(1/C.gridDenominator) := by
    have ha := nodeSourceAmp_bounds N
    dsimp only [da,aModel]
    constructor <;> linarith only [ha.1,ha.2]
  have hP : ∀i,1 ≤ s.P i := by
    intro i
    rw [hscale i]
    exact Real.one_le_rpow hz.le (div_nonneg (C.originalWeight_nonneg i) hu0.le)
  have hA : length N.localBase s.X₁+length N.localBase s.X₂+(∑i,w i) ≤ A := by
    apply le_of_eq
    rw [hX₁,hX₂]
    dsimp only [A,w]
    apply (eq_div_iff (ne_of_gt hu0)).mpr
    calc
      _ = N.unit*(length N.localBase N.X1+length N.localBase N.X2+
        ∑i : N.slots,C.originalWeight i/N.unit) := by ring
      _ = _ := N.length_eq
  have hdeleted : nodeDetectorDeletion N ≤ ∑i∈Rdel,w i := hcover.resolve_left hproper
  have hdBounds := nodeDetectorDeletion_bounds N
  have hd : D ≤ ∑i∈Rdel,w i := by dsimp only [D]; linarith only [hdBounds.1,hdeleted]
  have hdmesh : (∑i∈Rdel,w i) ≤ D+(mesh+2200*(1/C.gridDenominator)+1/100000000000000000000) := by
    dsimp only [D]
    linarith only [hdelmesh,hdBounds.2]
  have hcoords := actual_native_physical_coordinates s ch χ t N.localBase hz n b hb
    Mrow (nodeSourceAmp N) omega xi reserve g hcard hs hlower hP w hscale
    second L alloc row hne Rdel hRdel A 1 aModel da D
    (mesh+2200*(1/C.gridDenominator)+1/100000000000000000000)
    hA hdaBounds.1 (by dsimp only [da]; ring) hd hdmesh homega
  dsimp only at hcoords
  rcases hcoords with ⟨hV,hU,hRedLower,hCommon,hEll,hEllMax,hSlots,hAchild,hRedPaid⟩
  change 0 ≤ V at hV
  change nativeUnit 1 N.localBase (nodeSourceAmp N) omega reserve xi ch.C₁ g.D₁
    g.datum.C g.datum.D g.datum.inactive=1-6*aModel-V at hU
  change 0 ≤ ell at hEll
  change ell ≤ V+Red+pad at hEllMax
  change (∑i∈ch.indices L alloc\Rdel,w i)=(∑i,w i)-D-ell at hSlots
  change Achild=A-D-V-Red at hAchild
  have hfiniteActual : Real.logb N.localBase 128+6*da+pad ≤ 1/100000000000000000000 := by
    dsimp only [pad]
    linarith only [hfinite,hdaBounds.2]
  have hdeletedPaid : D+1/100000000000000000000 ≤ ∑i∈Rdel,w i := by
    dsimp only [D]
    linarith only [hdBounds.1,hdeleted]
  have hRed0 : 0 ≤ Red := hRedPaid (1/100000000000000000000) hfiniteActual hdeletedPaid
  have hcredit := actual_physical_puncture_credit s ch N.state.puncture N.state.puncture_ne_zero
    hR₂ hPuncture χ t N.localBase hz n b hb hcard hs hP w hscale
    g.first_nonzero g.second_nonzero second L alloc row hne Rdel hRdel A D V Red hA hd hAchild
  have hcreditGlobal : Real.logb C.globalBase ((ch.R₂*ch.E₂).absNorm:ℝ) ≤
      Real.logb C.globalBase (N.state.puncture.absNorm:ℝ)+N.unit*V+N.unit*Red+N.unit*pad := by
    have hlog (a : ℝ) : N.unit*Real.logb N.localBase a=Real.logb C.globalBase a := by
      rw [N.localBase_eq]
      exact unit_mul_logb_rebase C.globalBase_gt_one hu0
    have hm := mul_le_mul_of_nonneg_left hcredit hu0.le
    simp only [mul_add,hlog] at hm
    simpa only [pad,mul_add,hlog] using hm
  have hslotsParent : N.unit*(∑i,w i)=modelSlots j N.coordinates := by
    dsimp only [w]
    rw [←Finset.sum_div]
    field_simp [ne_of_gt hu0]
    exact N.slots_eq
  have hslotsChild : N.unit*(∑i∈ch.indices L alloc\Rdel,w i)=
      ∑i∈ch.indices L alloc\Rdel,C.originalWeight i := by
    dsimp only [w]
    rw [←Finset.sum_div]
    field_simp [ne_of_gt hu0]
  have hpad0 : 0 ≤ pad := by
    have hb0 := Real.logb_nonneg hz hb
    have hbp : 1 ≤ max 1 s.b₁*max 1 s.b₂ :=
      one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
    have hlogs := Real.logb_nonneg hz hbp
    dsimp only [pad]
    positivity
  have ht : 0 ≤ Real.logb N.localBase 128 := Real.logb_nonneg hz (by norm_num)
  have hpad : pad ≤ 1/100000000000000000000 := by
    linarith only [hfiniteActual,hdaBounds.1,ht]
  have hpadGlobal : N.unit*pad ≤ 1/100000000000000000000 :=
    (mul_le_of_le_one_left hpad0 N.unit_le_one).trans hpad
  change 0 ≤ N.unit*V ∧ 0 ≤ N.unit*Red ∧ 0 ≤ N.unit*ell ∧
    N.unit*(nativeUnit 1 N.localBase (nodeSourceAmp N) omega reserve xi
      ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive)=
      N.unit-6*modelAmplification j N.coordinates-N.unit*V ∧
    (∑i∈ch.indices L alloc\Rdel,C.originalWeight i)=
      modelSlots j N.coordinates-pathDeletion j.val N.coordinates-N.unit*ell ∧
    N.unit*Achild=modelLength j N.coordinates-pathDeletion j.val N.coordinates-N.unit*V-N.unit*Red ∧
    N.unit*ell ≤ N.unit*V+N.unit*Red+N.unit*pad ∧
    Real.logb C.globalBase ((ch.R₂*ch.E₂).absNorm:ℝ) ≤
      Real.logb C.globalBase (N.state.puncture.absNorm:ℝ)+N.unit*V+N.unit*Red+N.unit*pad ∧
    N.unit*pad ≤ 1/100000000000000000000
  refine ⟨mul_nonneg hu0.le hV,mul_nonneg hu0.le hRed0,mul_nonneg hu0.le hEll,?_,?_,?_,?_,hcreditGlobal,hpadGlobal⟩
  · change N.unit*(nativeUnit 1 N.localBase (nodeSourceAmp N) omega reserve xi
      ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive)=_
    rw [hU]
    dsimp only [aModel]
    field_simp [ne_of_gt hu0]
    <;> ring
  · change _=modelSlots j N.coordinates-pathDeletion j.val N.coordinates-N.unit*ell
    rw [←hslotsChild,hSlots,←hslotsParent]
    dsimp only [D]
    field_simp [ne_of_gt hu0]
    <;> ring
  · change N.unit*Achild=modelLength j N.coordinates-pathDeletion j.val N.coordinates-N.unit*V-N.unit*Red
    rw [hAchild]
    dsimp only [A,D]
    field_simp [ne_of_gt hu0]
    <;> ring
  · change N.unit*ell ≤ N.unit*V+N.unit*Red+N.unit*pad
    have hm := mul_le_mul_of_nonneg_left hEllMax hu0.le
    simpa only [mul_add] using hm
end
end OAI.SevenEighths.Cycle153Reachable
#print axioms OAI.SevenEighths.Cycle153Reachable.actual_inner_native_node_step
