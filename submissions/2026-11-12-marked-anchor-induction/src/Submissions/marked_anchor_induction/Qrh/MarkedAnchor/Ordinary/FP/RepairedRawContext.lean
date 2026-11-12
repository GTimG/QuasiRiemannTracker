/- Copyright (c) 2026 Sil. Apache-2.0.
Structural root data for actual Raw/Small side assembly. This record has
NO source/energy/moment bound. Its face and minimum conditions are the
proved root-dispatch scalar gates.
Modified by Sil (2026-10-26): RootInput is parametrised by the step gates G : StepGates D (mesh, windowCap, seedCap, omegaLoss of CubeFree.RootParameters); hface is the child face RootParameters.Face D (s0 <= S <= c, P + L S <= B); hmargin is CF (7.1) at the root, log_Z V + 3 uMax G eps S - 5/6 - alphaP G eps * ell <= -9 omega (FP: alpha = 2/3, no uMax, 10 omega); root_capacity uses D.L and 1 - D.B (root_capacity_reserve: rootReserve G); choose selects with target D.sel eps above widthFloor = G.floor eps (Second.Selection; choose_large/choose_small); the u-freezing branch quantity contribution/firstBranch (RepairedSupplierSplit, not ported) is dropped.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane).
-/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.RootParameters
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.Selection
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstActualNonexceptional
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstChosenEnergy
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstGeometricCaps

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary.FP.RepairedRawContext
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.FP
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge
open QRH.Record1252270103KernelMass
open CenteredMomentSourceMass CenteredMomentCommonProfile CenteredMomentCommonAllocationSum
open CenteredMomentCommonAllocationBox CenteredMomentSourceLiveColumn
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
open CenteredMomentNaturalFixedRaySource
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedFirstLiveSource MixedFirstActualNonexceptional MixedFirstGeometricCaps MixedFirstChosenEnergy
open MixedInnerExceptionalBlock MixedOriginalNormCap MixedOriginalTail
open Qrh.MarkedAnchor.Ordinary.RootParameters
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance instDecEqRawContext {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance (priority := 2000) instDecEqSubtypeRawContext {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

variable {D : StepData} (G : StepGates D)
variable (M : Id) [NeZero M]
local instance instFiniteQuotRawContext : Finite (O⧸M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The root data of one cube-free step `D`: the mesh, caps and the reference margin are
those of `CubeFree.RootParameters` at the gates `G`, and the root face is the child face
`P + D.L·S ≤ D.B`, `s₀ ≤ S ≤ D.c` (roots below the crossing `s₀` are inherited). -/
structure RootInput (ι : Type u) [Fintype ι] (Wslot : ℝ → ℂ)
    (N Holes : ℕ) (ε Z Kslot : ℝ) (η η₀ : Character) where
  root : Source ι (1/4) (9/4)
  cover : OriginalEnclosure root
  chars : ι → RayQuotient.Characters M H
  w : ι → ℝ
  freq : ι → ℝ
  t₀ : ℝ
  V : ℝ
  ell : ℝ
  Kroot : ℝ
  R₀ : ι → Finset Id
  hZ : 5 ≤ Z
  hw : ∀ i, 0 ≤ w i
  hwm : ∀ i, w i ≤ mesh G ε
  hV : 0 ≤ V
  hfreq : ∀ i, |freq i| ≤ V
  hholes : ∀ i, (R₀ i).card ≤ Holes
  hcanonical : Canonical M H hH Wslot 16 (windowCap G N ε) Z η₀ chars w (fun _ => 33/50) freq t₀ R₀ root
  hM : ∀ i, root.M i ≤ Kslot
  hunit : root.d = (1,1)
  hR : root.R = 1
  hH : root.H = ∅
  hF : root.Fhole = 1
  hX₁ : root.X₁ ≤ Z^(3:ℝ)
  hX₂ : root.X₂ ≤ Z^(3:ℝ)
  hY₁ : root.Y₁ ≤ Z^(3:ℝ)
  hY₂ : root.Y₂ ≤ Z^(3:ℝ)
  hnorm : sourceNormCap root.P (9/4) root.T root.d ≤ Z^(seedCap G N ε)
  hpool : poolCap root ≤ Z^(8:ℝ)
  hface : RootParameters.Face (D:=D) (Real.logb Z root.T) (∑ i, w i)
  hell : 0 ≤ ell
  hminimum : (2/9:ℝ) * Z^ell ≤ root.L
  /-- CF (7.1) at the root: the principal excess with `+3 u_max` and the parameter
  `α = alphaP G ε < 2/3` (FP: `α = 2/3`, no `u_max`, margin `10ω`). -/
  hmargin : Real.logb Z (sourceVolume root) + 3*uMax G ε (∑ i, w i) - 5/6 - alphaP G ε*ell ≤
    -9*omegaLoss G ε
  hKlow : Z ≤ Kroot
  hKcap : Kroot ≤ Z^(2:ℝ)
  hη : (η.modulus.absNorm:ℝ) ≤ Z

namespace RootInput
variable {G M H hH}
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
variable (d : RootInput G M H hH ι Wslot N Holes ε Z Kslot η η₀)

include d in
theorem one_lt_Z : 1 < Z := by linarith [d.hZ]

theorem radial_pos : 0 < d.Kroot := (zero_lt_one.trans d.one_lt_Z).trans_le d.hKlow

/-- The root marked width lies in `[0, D.c]`. -/
theorem width_bounds : 0 ≤ ∑ i, d.w i ∧ ∑ i, d.w i ≤ D.c :=
  ⟨face_nonneg G d.hface, d.hface.2.1⟩

/-- Root capacity at the child face: `log_Z T + L·∑w ≤ inputWidth - (1 - B)`
(FP: `93/25` and `1 - rootReserve`). -/
theorem root_capacity :
    Real.logb Z (d.root.T / pairNorm d.root.d) + D.L*(∑ i, d.w i) ≤
      inputWidth η d.Kroot Z - (1 - D.B) := by
  have hK : 1 ≤ Real.logb Z d.Kroot := by
    simpa only [Real.logb_self_eq_one d.one_lt_Z] using
      Real.logb_le_logb_of_le d.one_lt_Z (zero_lt_one.trans d.one_lt_Z) d.hKlow
  have hη := Real.logb_nonneg d.one_lt_Z (ideal_norm_one_le η.modulus_ne_bot)
  have hF := Real.logb_nonneg d.one_lt_Z fixed_presentation_one_le
  have hface := d.hface.2.2
  simp only [d.hunit, pairNorm, map_one, Nat.cast_one, one_mul, div_one]
  unfold inputWidth
  linarith

/-- The same capacity with the root reserve (`2·rootReserve ≤ 1 - B`). -/
theorem root_capacity_reserve :
    Real.logb Z (d.root.T / pairNorm d.root.d) + D.L*(∑ i, d.w i) ≤
      inputWidth η d.Kroot Z - rootReserve G := by
  have h := d.root_capacity
  have hr := rootReserve_spec G
  linarith [hr.1, hr.2.2.1]

/-- The live width of a first allocation is at most the root width. -/
theorem liveWidth_le (G₁ : Id) (B : actualAllocations (tuplePools d.root) G₁)
    (L : Finset (liveIndices B.val)) :
    Second.Selection.liveWidth L (fun i => d.w i.val) ≤ ∑ i, d.w i := by
  have hpart := Second.Selection.original_width_partition L (fun i => d.w i.val)
  have hfro : 0 ≤ ∑ i : ↥Lᶜ, d.w i.val.val := Finset.sum_nonneg (fun i _ => d.hw _)
  have hlive : (∑ i : ↥(liveIndices B.val), d.w i.val) ≤ ∑ i, d.w i := by
    rw [Finset.sum_coe_sort (liveIndices B.val) d.w]
    exact Finset.sum_le_univ_sum_of_nonneg (fun i => d.hw i)
  linarith

theorem liveWidth_nonneg (G₁ : Id) (B : actualAllocations (tuplePools d.root) G₁)
    (L : Finset (liveIndices B.val)) :
    0 ≤ Second.Selection.liveWidth L (fun i => d.w i.val) :=
  Finset.sum_nonneg (fun i _ => d.hw _)

theorem sel_live (hε : 0 < ε) (G₁ : Id) (B : actualAllocations (tuplePools d.root) G₁)
    (L : Finset (liveIndices B.val)) :
    0 ≤ D.sel ε (Second.Selection.liveWidth L (fun i => d.w i.val)) ∧
      D.sel ε (Second.Selection.liveWidth L (fun i => d.w i.val)) ≤
        Second.Selection.liveWidth L (fun i => d.w i.val) :=
  (G.sel_spec ε hε).2 _ (d.liveWidth_nonneg G₁ B L)
    ((d.liveWidth_le G₁ B L).trans d.width_bounds.2)

/-- The selected block of the live slots: target `D.sel ε` (FP: `43/100·w`), floor
`widthFloor = G.floor ε` (FP: `mesh ε`), one upward mesh error. -/
def choose (hε : 0 < ε) (G₁ : Id) (B : actualAllocations (tuplePools d.root) G₁)
    (L : Finset (liveIndices B.val)) : Finset {i // i ∉ Lᶜ} :=
  Second.Selection.chosenSlots L (fun i => d.w i.val) (D.sel ε) (widthFloor G ε) (mesh G ε)
    (mesh_spec G ε hε).1.le (fun i => d.hw i.val) (fun i => d.hwm i.val) (d.sel_live hε G₁ B L)

def large (G₁ : Id) (B : actualAllocations (tuplePools d.root) G₁)
    (L : Finset (liveIndices B.val)) : Prop :=
  widthFloor G ε < Second.Selection.liveWidth L (fun i => d.w i.val)

/-- Large branch: the selected width `u` obeys `sel S ≤ u ≤ sel S + mesh` and the retained
live width is `S - u` (`SideGeometry.hsel`, `hs`). -/
theorem choose_large (hε : 0 < ε) (G₁ : Id) (B : actualAllocations (tuplePools d.root) G₁)
    (L : Finset (liveIndices B.val)) (hL : d.large G₁ B L) :
    D.sel ε (Second.Selection.liveWidth L (fun i => d.w i.val)) ≤
        (∑ j ∈ d.choose hε G₁ B L, d.w j.val.val) ∧
      (∑ j ∈ d.choose hε G₁ B L, d.w j.val.val) ≤
        D.sel ε (Second.Selection.liveWidth L (fun i => d.w i.val)) + mesh G ε ∧
      (∑ j ∈ Finset.univ \ d.choose hε G₁ B L, d.w j.val.val) =
        Second.Selection.liveWidth L (fun i => d.w i.val) - (∑ j ∈ d.choose hε G₁ B L, d.w j.val.val) :=
  by
    have h := Second.Selection.chosen_large L (fun i => d.w i.val) (D.sel ε) (widthFloor G ε)
      (mesh G ε) (mesh_spec G ε hε).1.le (fun i => d.hw i.val) (fun i => d.hwm i.val)
      (d.sel_live hε G₁ B L) hL
    unfold RootInput.choose
    convert h

/-- Small branch: nothing is selected. -/
theorem choose_small (hε : 0 < ε) (G₁ : Id) (B : actualAllocations (tuplePools d.root) G₁)
    (L : Finset (liveIndices B.val)) (hL : ¬d.large G₁ B L) : d.choose hε G₁ B L = ∅ :=
  Second.Selection.chosen_small L (fun i => d.w i.val) (D.sel ε) (widthFloor G ε) (mesh G ε)
    (mesh_spec G ε hε).1.le (fun i => d.hw i.val) (fun i => d.hwm i.val) (d.sel_live hε G₁ B L)
    (le_of_not_gt hL)

end RootInput
end
end Qrh.MarkedAnchor.Ordinary.FP.RepairedRawContext
