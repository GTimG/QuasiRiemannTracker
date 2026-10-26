/- Copyright (c) 2026 Zhongpai Gao. Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RootLedgerBinding
import Candidate.Research.RecursiveAffine.MarkedRootHigh.BindingLemmas
import Candidate.Research.RecursiveAffine.NativePhysicalCoordinates
import Candidate.Research.RecursiveAffine.PhysicalMaskBridge

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
namespace OAI.SevenEighths.Cycle153RootStep
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
open Cycle153Geometry Cycle63.Optimization

noncomputable local instance rootStepFixedLedger : Cycle63.AffineLedger := Cycle153.Root.rootLedger
local instance rootStepFixedBinding :
    Cycle153.MarkedRootPrice.RootLedgerBinding rootStepFixedLedger :=
  Cycle153.MarkedRootPrice.fixedRootLedgerBinding
variable {α : Type} [Fintype α] [DecidableEq α]

/-- The genuine original total slot length chooses the root cell. -/
def rootSourceCell (w : α→ℝ) : ℝ :=
  Cycle63.AffineLedger.cellUpper (Cycle63.AffineLedger.originalCell (∑i,w i))

def rootSourceSlack (w : α→ℝ) : ℝ := rootSourceCell w-(∑i,w i)
def rootSourceAmp (w : α→ℝ) : ℝ := Cycle63.AffineLedger.amp (rootSourceCell w)

def rootSourceDeletion (w : α→ℝ) : ℝ :=
  (Cycle63.AffineLedger.regionGap (rootSourceCell w)+
    6*Cycle63.AffineLedger.intercept*rootSourceAmp w)/(6*Cycle63.AffineLedger.price)

def rootDetectorDeletion (w : α→ℝ) : ℝ :=
  rootSourceDeletion w+1/100000000000000000000

/-- The exact initial plane majorant uses the actual total slot length,
not a fictitious point at the upper cell edge. -/
def rootSourceLength (w : α→ℝ) : ℝ :=
  Coordinates.outerB-(Coordinates.outerLambda-1)*(∑i,w i)

theorem root_amp_model_alias (w : α→ℝ) (x : Fin 14→ℝ)
    (hb : Coordinates.b x=rootSourceCell w) : rootSourceAmp w=Coordinates.a0 x := by
  rw [rootSourceAmp,Cycle153.MarkedRootPrice.affine_amp_eq]
  change planeAmplifier _ _ _ _ _ _=Coordinates.a0 x
  rw [←hb]
  unfold planeAmplifier Coordinates.a0 Coordinates.gap0 Coordinates.U0
  simp only [mul_one]
  rfl

theorem root_deletion_model_alias (w : α→ℝ) (x : Fin 14→ℝ)
    (hb : Coordinates.b x=rootSourceCell w) : rootSourceDeletion w=Coordinates.d0 x := by
  rw [rootSourceDeletion,root_amp_model_alias w x hb,←hb]
  rfl

theorem root_length_model_alias (w : α→ℝ) (x : Fin 14→ℝ)
    (hb : Coordinates.b x=rootSourceCell w)
    (hslack : Coordinates.rootSlack x=rootSourceSlack w) :
    rootSourceLength w=Coordinates.A0 x ∧ (∑i,w i)=Coordinates.z0 x := by
  unfold Coordinates.A0 Coordinates.z0
  rw [hb,hslack]
  dsimp only [rootSourceLength,rootSourceSlack]
  constructor <;> ring

theorem actual_root_cell_slack (s : Input α) (Z : ℝ) (w : α→ℝ)
    (hwindow : Cycle63.AffineLedger.PlainWindow
      (length Z s.X₁) (length Z s.X₂) (∑i,w i)) :
    (17/500+1/100000000:ℝ) ≤ rootSourceCell w ∧ rootSourceCell w ≤ Coordinates.top ∧
    0 ≤ rootSourceSlack w ∧ rootSourceSlack w ≤ (1/100000000:ℝ) ∧
    length Z s.X₁+length Z s.X₂+(∑i,w i) ≤ rootSourceLength w ∧
    Cycle63.AffineLedger.totalA (rootSourceCell w)-rootSourceLength w =
      (Coordinates.outerLambda-1)*(1/100000000-rootSourceSlack w) := by
  have hc := Cycle63.AffineLedger.originalCell_mem ⟨hwindow.slots_ge,hwindow.slots_le⟩
  have hb := Cycle63.AffineLedger.cellUpper_bounds hc.1 hc.2.1
  have hclo := hc.2.2.1
  have hchi := hc.2.2.2
  have hplane := hwindow.plane
  change (17/500+1/100000000:ℝ) ≤ rootSourceCell w ∧ rootSourceCell w ≤ Coordinates.top at hb
  change rootSourceCell w-(1/100000000:ℝ) ≤ (∑i,w i) at hclo
  change (∑i,w i) ≤ rootSourceCell w at hchi
  have hA : length Z s.X₁+length Z s.X₂+Coordinates.outerLambda*(∑i,w i) ≤ Coordinates.outerB := hplane
  refine ⟨hb.1,hb.2,?_,?_,?_,?_⟩
  · dsimp only [rootSourceSlack];linarith only [hchi]
  · dsimp only [rootSourceSlack];linarith only [hclo]
  · dsimp only [rootSourceLength];linarith only [hA]
  · change planeTotalLength Coordinates.outerLambda Coordinates.outerB (1/100000000) (rootSourceCell w)-
      rootSourceLength w=_
    unfold planeTotalLength rootSourceLength rootSourceSlack
    ring

/-- All quantities are measured from the actual initial source, its
native root cell and its actual residual daughter. The first root has no
inherited puncture, no inner grid rounding, and unit exactly one. -/
structure NativeRootStepValues where
  b : ℝ
  rootSlack : ℝ
  amp : ℝ
  deletion : ℝ
  A0 : ℝ
  u : ℝ
  V : ℝ
  Red : ℝ
  ell : ℝ
  childA : ℝ
  childSlots : ℝ
  pad : ℝ

def nativeRootStepValues (s : Input α) (ch : Chain s) (χ : Character) (t Z : ℝ)
    (n : ℕ) (bs Mrow omega xi reserve : ℝ) (w : α→ℝ)
    (g : LiveMainGeometry s ch Z Mrow (rootSourceAmp w) omega xi bs n)
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (Rdel : Finset α) : NativeRootStepValues :=
  let A := rootSourceLength w
  let D := rootSourceDeletion w
  let V := commonWidthLoss Z ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive+Real.logb Z 128
  let Achild := length Z (rawDaughterScale (ch.final χ t) second L alloc 0)+
    length Z (rawDaughterScale (ch.final χ t) second L alloc 1)+(∑i∈ch.indices L alloc\Rdel,w i)
  { b := rootSourceCell w,rootSlack := rootSourceSlack w,amp := rootSourceAmp w,
    deletion := D,A0 := A,
    u := nativeUnit 1 Z (rootSourceAmp w) omega reserve xi ch.C₁ g.D₁
      g.datum.C g.datum.D g.datum.inactive,
    V := V,Red := A-D-V-Achild,
    ell := (∑i,w i)-(∑i∈ch.indices L alloc,w i)+((∑i∈Rdel,w i)-D),
    childA := Achild,childSlots := ∑i∈ch.indices L alloc\Rdel,w i,
    pad := 2*(n:ℝ)*Real.logb Z bs+Real.logb Z (max 1 s.b₁*max 1 s.b₂) }

/-- Genuine OUTER root-to-first-inner source coordinates. The actual
root plane supplies A0 and the original cell supplies its explicit slack.
The extra 1e-20 deletion surcharge pays only finite native source error;
no inner-grid displacement is silently added. The same actual initial
puncture R=1 gives the first global puncture-history bound. -/
theorem actual_outer_native_root_step
    (s : Input α) (ch : Chain s) (χ : Character) (t Z : ℝ) (hZ : 1<Z)
    (n : ℕ) (bs Mrow omega xi reserve mesh : ℝ) (w : α→ℝ)
    (g : LiveMainGeometry s ch Z Mrow (rootSourceAmp w) omega xi bs n)
    (hb : 1 ≤ bs) (hcard : Fintype.card α ≤ n)
    (hs : s.upper ≤ bs) (hlower : 1 ≤ s.lower)
    (hw : ∀i,0 ≤ w i) (hscale : ∀i,s.P i=Z^(w i))
    (hwindow : Cycle63.AffineLedger.PlainWindow
      (length Z s.X₁) (length Z s.X₂) (∑i,w i))
    (second : Bool) (L : Ideal O)
    (alloc : Allocation L (Finset.univ : Finset
      ((CenteredMomentCommonProfile.liveIndices ch.B₂.val)⊕Fin 2)))
    (row : O) (hne : Cycle63.Physical.sourcePositiveRow (ch.final χ t).toSource second L alloc row≠0)
    (Rdel : Finset α) (hRdel : Rdel ⊆ ch.indices L alloc) (hproper : Rdel≠ch.indices L alloc)
    (hcover : Rdel=ch.indices L alloc ∨ rootDetectorDeletion w ≤ ∑i∈Rdel,w i)
    (hdelmesh : (∑i∈Rdel,w i) ≤ rootDetectorDeletion w+mesh)
    (homega : omega=frequencyLoss Z 32 xi+reserve*1)
    (hR₂ : ch.R₂=(1:Ideal O)*ch.C₁) (hPuncture : ch.R₂*ch.E₂≠0)
    (hfinite : Real.logb Z 128+
      (2*(n:ℝ)*Real.logb Z bs+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) ≤ 1/100000000000000000000) :
    let r := nativeRootStepValues s ch χ t Z n bs Mrow omega xi reserve w g second L alloc Rdel
    (17/500+1/100000000:ℝ) ≤ r.b ∧ r.b ≤ Coordinates.top ∧
    0 ≤ r.rootSlack ∧ r.rootSlack ≤ (1/100000000:ℝ) ∧ r.b-r.rootSlack=(∑i,w i) ∧
    0 ≤ r.V ∧ 0 ≤ r.Red ∧ 0 ≤ r.ell ∧
    r.u=1-6*r.amp-r.V ∧ r.childSlots=(∑i,w i)-r.deletion-r.ell ∧
    r.childA=r.A0-r.deletion-r.V-r.Red ∧ r.ell ≤ r.V+r.Red+r.pad ∧
    Real.logb Z ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ r.V+r.Red+r.pad ∧
    r.pad ≤ 1/100000000000000000000 ∧
    Cycle63.AffineLedger.totalA r.b-r.A0=
      (Coordinates.outerLambda-1)*(1/100000000-r.rootSlack) := by
  intro r
  let A := rootSourceLength w
  let D := rootSourceDeletion w
  let V := commonWidthLoss Z ch.C₁ g.D₁ g.datum.C g.datum.D g.datum.inactive+Real.logb Z 128
  let Achild := length Z (rawDaughterScale (ch.final χ t) second L alloc 0)+
    length Z (rawDaughterScale (ch.final χ t) second L alloc 1)+(∑i∈ch.indices L alloc\Rdel,w i)
  let Red := A-D-V-Achild
  let ell := (∑i,w i)-(∑i∈ch.indices L alloc,w i)+((∑i∈Rdel,w i)-D)
  let pad := 2*(n:ℝ)*Real.logb Z bs+Real.logb Z (max 1 s.b₁*max 1 s.b₂)
  have hcell := actual_root_cell_slack s Z w hwindow
  have hP : ∀i,1 ≤ s.P i := by intro i;rw [hscale];exact Real.one_le_rpow hZ.le (hw i)
  have hdeleted : rootDetectorDeletion w ≤ ∑i∈Rdel,w i := hcover.resolve_left hproper
  have hd : D ≤ ∑i∈Rdel,w i := by dsimp only [rootDetectorDeletion] at hdeleted;linarith only [hdeleted]
  have hdmesh : (∑i∈Rdel,w i) ≤ D+(mesh+1/100000000000000000000) := by
    dsimp only [rootDetectorDeletion] at hdelmesh;linarith only [hdelmesh]
  have hcoords := actual_native_physical_coordinates s ch χ t Z hZ n bs hb
    Mrow (rootSourceAmp w) omega xi reserve g hcard hs hlower hP w hscale
    second L alloc row hne Rdel hRdel A 1 (rootSourceAmp w) 0 D
    (mesh+1/100000000000000000000) hcell.2.2.2.2.1 (by norm_num) (by ring) hd hdmesh homega
  dsimp only at hcoords
  rcases hcoords with ⟨hV,hU,hRedLower,hCommon,hEll,hEllMax,hSlots,hAchild,hRedPaid⟩
  have hV0 : 0 ≤ V := by simpa only [mul_zero,add_zero] using hV
  have hRed0 : 0 ≤ Red := by
    have hf : Real.logb Z 128+6*(0:ℝ)+pad ≤ 1/100000000000000000000 := by
      simpa only [mul_zero,add_zero] using hfinite
    have hdpaid : D+1/100000000000000000000 ≤ ∑i∈Rdel,w i := hdeleted
    have hp := hRedPaid (1/100000000000000000000) hf hdpaid
    simpa only [mul_zero,add_zero] using hp
  have hU' : nativeUnit 1 Z (rootSourceAmp w) omega reserve xi ch.C₁ g.D₁
      g.datum.C g.datum.D g.datum.inactive=1-6*rootSourceAmp w-V := by
    simpa only [mul_zero,add_zero] using hU
  have hEll0 : 0 ≤ ell := hEll
  have hSlots : (∑i∈ch.indices L alloc\Rdel,w i)=(∑i,w i)-D-ell := hSlots
  have hAchild' : Achild=A-D-V-Red := by simpa only [mul_zero,add_zero] using hAchild
  have hEllMax' : ell ≤ V+Red+pad := by simpa only [mul_zero,add_zero] using hEllMax
  have hcredit := actual_physical_puncture_credit s ch (1:Ideal O) one_ne_zero
    hR₂ hPuncture χ t Z hZ n bs hb hcard hs hP w hscale
    g.first_nonzero g.second_nonzero second L alloc row hne Rdel hRdel A D V Red hcell.2.2.2.2.1 hd hAchild'
  have hcredit' : Real.logb Z ((ch.R₂*ch.E₂).absNorm:ℝ) ≤ V+Red+pad := by
    simpa only [map_one,Nat.cast_one,Real.logb_one,zero_add] using hcredit
  have hpad : pad ≤ 1/100000000000000000000 := by
    have ht : 0 ≤ Real.logb Z 128 := Real.logb_nonneg hZ (by norm_num)
    dsimp only [pad];linarith only [hfinite,ht]
  refine ⟨hcell.1,hcell.2.1,hcell.2.2.1,hcell.2.2.2.1,?_,hV0,hRed0,hEll0,hU',hSlots,hAchild',hEllMax',hcredit',hpad,hcell.2.2.2.2.2⟩
  change rootSourceCell w-(rootSourceCell w-(∑i,w i))=(∑i,w i)
  ring
end
end OAI.SevenEighths.Cycle153RootStep
#print axioms OAI.SevenEighths.Cycle153RootStep.root_amp_model_alias
#print axioms OAI.SevenEighths.Cycle153RootStep.root_deletion_model_alias
#print axioms OAI.SevenEighths.Cycle153RootStep.actual_outer_native_root_step
