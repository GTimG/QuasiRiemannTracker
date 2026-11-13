/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Provider geometry, part 4: `GeometryAt` for the residual splits of a root input.

* `frame_w_sum`, `rest_vol_mul`, `root_vol`: the frame width is `lw - u` (`lw` the live width of
  the allocation, `u = selW J` the selected width), `V_rest·Z^u = V_live`, `V_root = T·Z^S`.
* `cap_le`: the radical cap of a genuine column, `N(rad(C·C₂·L)) ≤ Z²⁴`.
* `geometryAt_of`: **`GeometryAt`** of the residual split `residFin d C B J` with frame source
  `frameOf … (log_Z K_c)`, at `R = frequencyRadius (Tfreq … K_c) Z ξ_r`, `H = capRes`, `u = selW J`,
  frequency tolerance `tl = 2·cutoffLoss`, the plain-length slop absorbed in `hroot`
  and the residual volume lower bound δ₁ (`live_volume_ge`).
* `eventually_bigZ`: the four large-`Z` conditions hold eventually.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderGeometry3
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderLabelData

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentFirstSectors
open CenteredMomentNaturalFixedRaySource CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree Qrh.MarkedAnchor.Ordinary QRH.SilDensitySplit.CubeFree.Second Qrh.MarkedAnchor.Ordinary.Second
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations MixedFirstLiveSource MixedCompletedRows MixedInnerExceptionalBlock
open RepairedRawContext
open Qrh.MarkedAnchor.Ordinary.RootParameters
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete QRH.SilDensitySplit.CubeFree.Second.Provider Qrh.MarkedAnchor.Ordinary.Second.Provider
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open OAI.SevenEighths.CenteredMomentEnergyBands (length)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypePG4 {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

/-! ### Large `Z` -/

theorem eventually_logb_le (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ) :
    ∀ᶠ Z : ℝ in atTop, Real.logb Z c ≤ δ := by
  filter_upwards [(tendsto_rpow_atTop hδ).eventually_ge_atTop c, eventually_gt_atTop (1:ℝ)]
    with Z h1 h2
  calc Real.logb Z c ≤ Real.logb Z (Z^δ) := Real.logb_le_logb_of_le h2 hc h1
    _ = δ := Real.logb_rpow (by linarith) h2.ne'

/-- **The large-`Z` conditions of `geometryAt_of`.** -/
theorem eventually_bigZ {D : StepData} (G : StepGates D) (N : ℕ) (ε : ℝ) (hε : 0 < ε) (n : ℕ)
    (Cst : ℝ) (hCst : 0 < Cst) :
    ∀ᶠ Z : ℝ in atTop, Real.logb Z Cst ≤ cutoffLoss G N ε / 2 ∧
      2 * (n:ℝ) * Real.logb Z 2 ≤ rootReserve G ∧ Real.logb Z (9/2) ≤ cutoffLoss G N ε ∧
      (81/16:ℝ) * 4^n ≤ Z := by
  have hκ : 0 < cutoffLoss G N ε := div_pos (internal_spec G N ε hε).1 (by norm_num)
  have hr := (rootReserve_spec G).1
  have h2 := eventually_logb_le 2 (rootReserve G / (2*n+2)) (by norm_num) (by positivity)
  filter_upwards [eventually_logb_le Cst _ hCst (half_pos hκ), h2,
    eventually_logb_le (9/2) _ (by norm_num) hκ, eventually_ge_atTop ((81/16:ℝ) * 4^n),
    eventually_gt_atTop (1:ℝ)] with Z hZ1 hZ2 hZ3 hZ4 hZ5
  refine ⟨hZ1, ?_, hZ3, hZ4⟩
  have hx0 : 0 ≤ Real.logb Z 2 := Real.logb_nonneg hZ5 (by norm_num)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have h := mul_le_mul_of_nonneg_left hZ2 (show (0:ℝ) ≤ 2*n+2 by positivity)
  rw [mul_div_cancel₀ _ (by positivity)] at h
  nlinarith

/-! ### The radical cap -/

theorem cap_le (C C' Lp : Id) (hC0 : C ≠ 0) (hC'0 : C' ≠ 0) (hLp0 : Lp ≠ 0) (Z Bmask : ℝ)
    (hZ : 1 ≤ Z) (hB : 24 ≤ Bmask) (hC : (Ideal.absNorm C : ℝ) ≤ Z^(8:ℝ))
    (hC' : (Ideal.absNorm C' : ℝ) ≤ Z^(8:ℝ)) (hL : (Ideal.absNorm Lp : ℝ) ≤ Z^(8:ℝ)) :
    (Ideal.absNorm (∏ I ∈ QRH.Record1252270103KernelMass.primeSupport ((C * C') * Lp) ∪ ∅, I) : ℝ)
      ≤ Z^Bmask := by
  have hZ0 : 0 < Z := by linarith
  rw [Finset.union_empty]
  refine (rad_norm_le _ (mul_ne_zero (mul_ne_zero hC0 hC'0) hLp0)).trans ?_
  rw [map_mul, map_mul, Nat.cast_mul, Nat.cast_mul]
  calc (Ideal.absNorm C : ℝ) * Ideal.absNorm C' * Ideal.absNorm Lp
      ≤ Z^(8:ℝ) * Z^(8:ℝ) * Z^(8:ℝ) :=
        mul_le_mul (mul_le_mul hC hC' (Nat.cast_nonneg _) (by positivity)) hL (Nat.cast_nonneg _)
          (by positivity)
    _ = Z^(24:ℝ) := by rw [← Real.rpow_add hZ0, ← Real.rpow_add hZ0]; norm_num
    _ ≤ Z^Bmask := Real.rpow_le_rpow_of_exponent_le hZ hB

/-! ### The residual widths and volumes -/

variable {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
  {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
  {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}

/-- The live width of an allocation. -/
def liveW (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) {C : Id}
    (B : actualAllocations (tuplePools d.root) C) : ℝ :=
  ∑ i : liveIndices B.val, d.w i.val

/-- The selected width of a block. -/
def selW (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) {C : Id}
    {B : actualAllocations (tuplePools d.root) C} (J : Finset (liveIndices B.val)) : ℝ :=
  ∑ j ∈ J, d.w j.val

theorem frame_w_sum (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀)
    (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (bΦ : ℝ) (hbΦ : 2 ≤ bΦ)
    (Q : Id) (hQM : Q ≤ M) (hQ0 : internalQ Q η₀ ≠ 0) (hQt : internalQ Q η₀ ≠ ⊤)
    (hQ72 : internalQ Q η₀ ≤ Ideal.span {(72:O)}) (hε : 0 < ε) (Bmask : ℝ) (hBmask : 0 ≤ Bmask)
    (mesh : ℝ) (hmesh : ∀ i, d.w i ≤ mesh)
    (C : Id) (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val))
    (V₀ : O) (hV₀ : V₀ ≠ 0) (kLog : ℝ) :
    ∑ k, (frameOf d C B J hW hWs bΦ hbΦ Q hQM hQ0 hQt hQ72 hε Bmask hBmask mesh hmesh V₀ hV₀
      kLog).w k = liveW d B - selW d J := by
  change ∑ k, d.w (residSlot (d := d) (C := C) (B := B) (J := J) k) = _
  unfold residSlot
  rw [Equiv.sum_comp (Fintype.equivFin (Rest J)).symm (fun x : Rest J => d.w x.val.val)]
  have h := Fintype.sum_subtype_add_sum_subtype (fun j : liveIndices B.val => j ∈ J)
    (fun j => d.w j.val)
  have h2 : (∑ j : {x : liveIndices B.val // x ∈ J}, d.w j.val.val) = selW d J :=
    Finset.sum_coe_sort J (fun j => d.w j.val)
  have key : selW d J + ∑ i : Rest J, d.w i.val.val = liveW d B := by
    rw [← h2]; unfold liveW; convert h using 4
  linarith [key]

theorem rest_vol_mul (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) (J : Finset (liveIndices B.val)) :
    sourceVolume (residOf d C B J) * Z^(selW d J) =
      sourceVolume (renorm (allocatedLiveSource d.root (by norm_num) d.cover C B)) := by
  have h := rest_volume_mul (allocatedLiveSource d.root (by norm_num) d.cover C B) (fun _ => rfl) J
  obtain ⟨-, -, -, -, hP⟩ := d.hcanonical
  have hprod : (∏ j : J, (allocatedLiveSource d.root (by norm_num) d.cover C B).P j.val) =
      Z^(selW d J) := by
    unfold selW
    rw [← Finset.sum_coe_sort J, Real.rpow_sum_of_pos (zero_lt_one.trans d.one_lt_Z)]
    apply Finset.prod_congr rfl
    intro j _
    change d.root.P j.val.val = _
    rw [hP]
  rw [← hprod]
  exact h

theorem root_vol (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) :
    sourceVolume d.root = d.root.T * Z^(∑ i, d.w i) := by
  obtain ⟨-, -, -, -, hP⟩ := d.hcanonical
  unfold sourceVolume
  rw [hP, ← d.root.hpX, Real.rpow_sum_of_pos (zero_lt_one.trans d.one_lt_Z)]

theorem card_rest_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) {C : Id}
    {B : actualAllocations (tuplePools d.root) C} (J : Finset (liveIndices B.val)) :
    Fintype.card (Rest J) ≤ Fintype.card κ :=
  (Fintype.card_subtype_le _).trans (Fintype.card_subtype_le _)

theorem liveW_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) {C : Id}
    (B : actualAllocations (tuplePools d.root) C) : liveW d B ≤ ∑ i, d.w i := by
  unfold liveW
  rw [Finset.sum_coe_sort (liveIndices B.val) d.w]
  exact Finset.sum_le_univ_sum_of_nonneg (fun i => d.hw i)

theorem selW_le (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) {C : Id}
    {B : actualAllocations (tuplePools d.root) C} (J : Finset (liveIndices B.val)) :
    0 ≤ selW d J ∧ selW d J ≤ liveW d B := by
  unfold selW liveW
  exact ⟨Finset.sum_nonneg fun j _ => d.hw _,
    Finset.sum_le_univ_sum_of_nonneg (f := fun j : liveIndices B.val => d.w j.val)
      (fun j => d.hw _)⟩

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry
