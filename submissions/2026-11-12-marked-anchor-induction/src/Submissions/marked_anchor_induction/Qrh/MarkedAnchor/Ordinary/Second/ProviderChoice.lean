/- Copyright (c) 2026 Sil. Apache-2.0.
Provider: the concrete block choice and the label constants.

* `split_bound_late`: `split_label_bound_final` with the box constant `cb` chosen AFTER
  the constants (its mesh bound does not depend on `cb`); the conclusion is `SplitBoundAt`.
* `selOf`: the selected block of an allocation: `chosenSlots` on all live slots with target
  `D.sel ε`, floor `widthFloor G ε` and the FRAME mesh (`min (mesh G ε) meshCap`, the actual
  slot-width bound of the root).
* `rootChoice`: the `BlockChoice` of a block: `J = selOf`, `W = slotWidth`, `M = Mc` (constant),
  `T B = Tfreq … (16·K·W_B⁴)`, `χ₀ = 1`, `Q = internalQ Q₀ η₀`, `m = fixedBadMask`, `Zs = Z`,
  `ξr` given.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Ordinary.Second.ProviderLabelSplit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Qrh.MarkedAnchor.Ordinary.Second.Provider
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second QRH.SilDensitySplit.CubeFree.Second.Provider
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile CenteredMomentFirstSectors
open CenteredMomentNaturalFixedRaySource CenteredMomentSectorLocalization
open QRH.SilDensitySplit.CubeFree.FP Qrh.MarkedAnchor.Ordinary.FP
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail
open MixedPrincipalAllocations MixedFirstLiveSource MixedInnerExceptionalBlock
open RepairedRawContext Qrh.MarkedAnchor.Ordinary.RootParameters
open QRH.SilDensitySplit.CubeFree.Second.Concrete Qrh.MarkedAnchor.Ordinary.Second.Concrete
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second.ConcreteFrame
open QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteLabelAssembly
open RayFourExpansion CenteredMomentChildRows
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

local instance (priority := 2000) instDecEqSubtypeProviderCh {κ : Type*} {p : κ → Prop} :
    DecidableEq (Subtype p) := Classical.decEq _

/-- **The final split bound with the box constant chosen late.** -/
theorem split_bound_late (D : StepData) (G : StepGates D) (L : ℝ) (hL : 0 ≤ L)
    (hlarge : PricedPackedSource D.price D.Hmin (D.Hmax + 1) (L + 1))
    (hsmall : PricedPackedSource (nativePrice (3/4) (by norm_num)) D.Hmin (D.Hmax + 1) (L + 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ meshMax : ℝ, 0 < meshMax ∧ ∀ mesh : ℝ, 0 < mesh → mesh ≤ meshMax →
    ∀ (θ : GData L) (η : Character),
    ∃ J : ℕ, ∃ control : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧ ∀ cb : ℝ, 0 ≤ cb →
    ∀ᶠ Z : ℝ in atTop, SplitBoundAt D G θ mesh η Z ε cb J control C := by
  intro ε hε
  obtain ⟨meshMax, hmM, h1⟩ := split_label_bound D G L hL hlarge hsmall ε hε
  refine ⟨meshMax, hmM, fun mesh hmesh hmm θ η => ?_⟩
  obtain ⟨J, control, C, hC, hZ⟩ := h1 mesh hmesh hmm θ η
  refine ⟨J, control, C, hC, fun cb hcb => ?_⟩
  filter_upwards [hZ, box_card_subpower cb (ε/2) hcb (by positivity), eventually_gt_atTop (1:ℝ)]
    with Z hZ hbox hZ1
  intro P ξ Q m χ₀ s ha rs Kc R H M Mm clow hR hM hMm A c qC hb hHr t
  have hZ0 : 0 < Z := by linarith
  have h := hZ P ξ Q m χ₀ s ha rs Kc R H M Mm clow hR A c qC hb hHr t
  refine h.trans ?_
  have hcl := hR.hclow_pos
  have hvol := rs.vol_pos hZ0
  obtain ⟨hnn, -⟩ := gAmp_mono L θ mesh η Z rs
  have hamp := hnn J control
  have hb' := hbox M hM.1 hM.2
  have hZE := Real.rpow_nonneg hZ0.le (A - c + qC + ε)
  have hT : 0 ≤ (1 + ‖t‖)^(2*J) := by positivity
  have hprod : ((box M).card : ℝ) * (Mm : ℝ) ≤ Z^ε := by
    calc ((box M).card : ℝ) * (Mm : ℝ) ≤ Z^(ε/2) * Z^(ε/2) :=
          mul_le_mul hb' hMm (Nat.cast_nonneg _) (by positivity)
      _ = Z^ε := by rw [← Real.rpow_add hZ0]; ring_nf
  have e1 : (C * ((box M).card : ℝ) * (rs.vol / clow) * Mm * gAmp L θ mesh η Z rs J control *
      Z^(A - c + qC + ε)) * (1 + ‖t‖)^(2*J) =
      (((box M).card : ℝ) * (Mm : ℝ)) * (C * (rs.vol / clow) * gAmp L θ mesh η Z rs J control *
        Z^(A - c + qC + ε) * (1 + ‖t‖)^(2*J)) := by ring
  have e2 : (C * (rs.vol / clow) * gAmp L θ mesh η Z rs J control * Z^(A - c + qC + 2*ε)) *
      (1 + ‖t‖)^(2*J) = Z^ε * (C * (rs.vol / clow) * gAmp L θ mesh η Z rs J control *
        Z^(A - c + qC + ε) * (1 + ‖t‖)^(2*J)) := by
    rw [show A - c + qC + 2*ε = ε + (A - c + qC + ε) by ring, Real.rpow_add hZ0]; ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right hprod (by positivity)

variable {D : StepData} {G : StepGates D} {κ : Type u} [Fintype κ]
  {M : Id} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
  {W : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}

/-- **The selected block of an allocation** (all live slots, frame mesh). -/
def selOf (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (hε : 0 < ε) (mesh : ℝ)
    (hm : 0 ≤ mesh) (hmesh : ∀ i, d.w i ≤ mesh) (C : Id)
    (B : actualAllocations (tuplePools d.root) C) : Finset (liveIndices B.val) :=
  (Second.Selection.chosenSlots (Finset.univ : Finset (liveIndices B.val)) (fun i => d.w i.val)
    (D.sel ε) (widthFloor G ε) mesh hm (fun i => d.hw _) (fun i => hmesh _)
    (d.sel_live hε C B Finset.univ)).map (Function.Embedding.subtype _)

/-- **The block choice of a block.** -/
def rootChoice (d : RootInput G M H hH κ W N Holes ε Z Kslot η η₀) (hε : 0 < ε) (mesh : ℝ)
    (hm : 0 ≤ mesh) (hmesh : ∀ i, d.w i ≤ mesh) (Q : Id) (C D' : Id) (K ξr Mc : ℝ)
    (hML : MultBound d.root (by norm_num) d.cover C (selOf d hε mesh hm hmesh C) K
      (fun B => slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B)
        (selOf d hε mesh hm hmesh C B)) (fun _ => Mc))
    (hMR : MultBound d.root (by norm_num) d.cover D' (selOf d hε mesh hm hmesh D') K
      (fun B => slotWidth (allocatedLiveSource d.root (by norm_num) d.cover D' B)
        (selOf d hε mesh hm hmesh D' B)) (fun _ => Mc)) :
    BlockChoice d.root (by norm_num) d.cover C D' K where
  JL := selOf d hε mesh hm hmesh C
  JR := selOf d hε mesh hm hmesh D'
  WL := fun B => slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B)
    (selOf d hε mesh hm hmesh C B)
  ML := fun _ => Mc
  WR := fun B => slotWidth (allocatedLiveSource d.root (by norm_num) d.cover D' B)
    (selOf d hε mesh hm hmesh D' B)
  MR := fun _ => Mc
  χ₀ := 1
  Q := internalQ Q η₀
  m := CenteredMomentSecondHeightFamily.fixedBadMask
  TL := fun B => Tfreq d C B (selOf d hε mesh hm hmesh C B)
    (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover C B)
      (selOf d hε mesh hm hmesh C B))^4)
  TR := fun B => Tfreq d D' B (selOf d hε mesh hm hmesh D' B)
    (16 * K * (slotWidth (allocatedLiveSource d.root (by norm_num) d.cover D' B)
      (selOf d hε mesh hm hmesh D' B))^4)
  Zs := Z
  ξr := ξr
  hWL := widthBound_slot d.root (by norm_num) d.cover C _
  hML := hML
  hWR := widthBound_slot d.root (by norm_num) d.cover D' _
  hMR := hMR

end
end Qrh.MarkedAnchor.Ordinary.Second.Provider
