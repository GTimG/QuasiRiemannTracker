/- Copyright (c) 2026 Sil. Apache-2.0.
Structural root data for actual Raw/Small side assembly. This record has
NO source/energy/moment bound. Its face and minimum conditions are the
proved root-dispatch scalar gates.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedRootParameters
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSupplierSplit
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshRootAdmission
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstActualNonexceptional

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedRawContext
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
open OuterFreshSource OuterFreshSelection RepairedRootParameters RepairedSupplierSplit
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance (priority := 2000) {κ : Type*} {p : κ → Prop} : DecidableEq (Subtype p) := Classical.decEq _

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

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
  hwm : ∀ i, w i ≤ mesh ε
  hV : 0 ≤ V
  hfreq : ∀ i, |freq i| ≤ V
  hholes : ∀ i, (R₀ i).card ≤ Holes
  hcanonical : Canonical M H hH Wslot 16 (windowCap N ε) Z η₀ chars w (fun _ => 33/50) freq t₀ R₀ root
  hM : ∀ i, root.M i ≤ Kslot
  hunit : root.d = (1,1)
  hR : root.R = 1
  hH : root.H = ∅
  hF : root.Fhole = 1
  hX₁ : root.X₁ ≤ Z^(3:ℝ)
  hX₂ : root.X₂ ≤ Z^(3:ℝ)
  hY₁ : root.Y₁ ≤ Z^(3:ℝ)
  hY₂ : root.Y₂ ≤ Z^(3:ℝ)
  hnorm : sourceNormCap root.P (9/4) root.T root.d ≤ Z^(seedCap N ε)
  hpool : poolCap root ≤ Z^(8:ℝ)
  hface : RepairedRootParameters.Face (Real.logb Z root.T) (∑ i, w i)
  hell : 0 ≤ ell
  hminimum : (2/9:ℝ) * Z^ell ≤ root.L
  hmargin : Real.logb Z (sourceVolume root) - 5/6 - 2*ell/3 ≤ -10*omegaLoss ε
  hKlow : Z ≤ Kroot
  hKcap : Kroot ≤ Z^(2:ℝ)
  hη : (η.modulus.absNorm:ℝ) ≤ Z

namespace RootInput
variable {M H hH}
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
variable (d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀)

include d in
theorem one_lt_Z : 1 < Z := by linarith [d.hZ]

theorem radial_pos : 0 < d.Kroot := (zero_lt_one.trans d.one_lt_Z).trans_le d.hKlow

theorem root_capacity :
    Real.logb Z (d.root.T / pairNorm d.root.d) + (93/25:ℝ)*(∑ i, d.w i) ≤
      inputWidth η d.Kroot Z - rootReserve := by
  have hK : 1 ≤ Real.logb Z d.Kroot := by
    simpa only [Real.logb_self_eq_one d.one_lt_Z] using
      Real.logb_le_logb_of_le d.one_lt_Z (zero_lt_one.trans d.one_lt_Z) d.hKlow
  have hη := Real.logb_nonneg d.one_lt_Z (ideal_norm_one_le η.modulus_ne_bot)
  have hF := Real.logb_nonneg d.one_lt_Z fixed_presentation_one_le
  have hface := d.hface.2.2
  simp only [d.hunit, pairNorm, map_one, Nat.cast_one, one_mul, div_one]
  unfold inputWidth
  linarith

def choose (hε : 0 < ε) (G : Id) (B : actualAllocations (tuplePools d.root) G)
    (L : Finset (liveIndices B.val)) : Finset {i // i ∉ Lᶜ} :=
  chosenSlots L (fun i => d.w i.val) (widthFloor ε) (mesh ε)
    (mesh_spec ε hε).1.le (fun i => d.hw i.val) (fun i => d.hwm i.val)

def large (G : Id) (B : actualAllocations (tuplePools d.root) G)
    (L : Finset (liveIndices B.val)) : Prop := widthFloor ε < liveWidth L (fun i => d.w i.val)

/-- Shared branch quantity at the actual first child radius; all first
and supplier counts are those in RepairedSupplierSplit.firstBranch. -/
def contribution (hε : 0 < ε) (largeBranch : Bool) (G u : Id) (τ : Character)
    (v K : ℝ) (rows : Finset O) : ℝ :=
  firstBranch d.root (by norm_num) (by norm_num) d.cover G u (d.choose hε G)
    (fun B L => if largeBranch then d.large G B L else ¬d.large G B L) τ v K rows

end RootInput
end
end Candidate.FourthPower.RepairedRawContext
