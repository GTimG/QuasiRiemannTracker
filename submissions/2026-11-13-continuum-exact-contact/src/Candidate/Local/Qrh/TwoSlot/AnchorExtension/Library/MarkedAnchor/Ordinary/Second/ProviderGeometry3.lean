/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Provider geometry, part 3: the branch data and the envelope range of one side source from
its defect window, and the plain-length slop of the renormalized lengths.

* `branch_window`: with the side geometry `S` (root marked width), `f = S - lw` (frozen width),
  `u` (selected width), `PC = gP r`, `cg = f + (P + tl - gP r)` (`P = log_Z T`), the defect
  `t = commonH r - 1 + 6u - mesh` and the window `-tl ≤ commonH r - 1 + 6u`, `commonH r - 1 ≤ 1 + tl`,
  the source carries `BranchData` at `H = commonH r` with `A - c + q_C = colLog + twistLog + u`,
  and `commonH r ∈ [Hmin, Hmax]` (large branch: the ledger; small branch, `u = 0`:
  `tl ≤ 1 - Hmin`).
* `length_le_add`, `gP_le_logT`: lengths `≥ 2/9` lose at most `log_Z (9/2)` each against `log_Z`
  (the `o(1)` slop of `hroot`).
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Second.ProviderGeometry2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

namespace Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.CubeFree.Second
open QRH.SilDensitySplit.CubeFree.Packet.Grouped QRH.SilDensitySplit.CubeFree.Second.ConcreteGroup Qrh.MarkedAnchor.Ordinary.Second.ConcreteGroup
open QRH.SilDensitySplit.CubeFree Qrh.MarkedAnchor.Ordinary QRH.SilDensitySplit.CubeFree.Second Qrh.MarkedAnchor.Ordinary.Second

noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open OAI.SevenEighths.CenteredMomentEnergyBands (length)

variable {L : ℝ} {θ : GData L} {mesh Z : ℝ}

theorem length_nonneg (Z X : ℝ) (hZ : 1 < Z) : 0 ≤ length Z X := by
  unfold length; exact Real.logb_nonneg hZ (le_max_left _ _)

theorem gP_nonneg (r : GSrc θ mesh Z) : 0 ≤ gP r := by
  unfold gP
  exact le_max_of_le_left (add_nonneg (length_nonneg _ _ r.hZ) (length_nonneg _ _ r.hZ))

/-- **The plain-length slop**: a length `≥ 2/9` is at most `log_Z X + log_Z (9/2)`. -/
theorem length_le_add (Z X : ℝ) (hZ : 1 < Z) (hX : 2/9 ≤ X) :
    length Z X ≤ Real.logb Z X + Real.logb Z (9/2) := by
  unfold length
  rw [← Real.logb_mul (by linarith) (by norm_num)]
  apply Real.logb_le_logb_of_le hZ (lt_of_lt_of_le one_pos (le_max_left _ _))
  exact max_le (by nlinarith) (by nlinarith)

theorem gP_le_logT (Z X₁ X₂ Y₁ Y₂ N₁ N₂ T : ℝ) (hZ : 1 < Z) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    (hX₁ : 2/9 ≤ X₁) (hX₂ : 2/9 ≤ X₂) (hY₁ : 2/9 ≤ Y₁) (hY₂ : 2/9 ≤ Y₂) (hXT : X₁ * X₂ = T)
    (hYT : Y₁ * Y₂ = T) :
    max (length Z (X₁/N₁) + length Z (X₂/N₂)) (length Z (Y₁/N₁) + length Z (Y₂/N₂)) ≤
      Real.logb Z T + 2 * Real.logb Z (9/2) := by
  have h1 := (length_div_le Z X₁ N₁ hZ hN₁ (by linarith)).trans (length_le_add Z X₁ hZ hX₁)
  have h2 := (length_div_le Z X₂ N₂ hZ hN₂ (by linarith)).trans (length_le_add Z X₂ hZ hX₂)
  have h3 := (length_div_le Z Y₁ N₁ hZ hN₁ (by linarith)).trans (length_le_add Z Y₁ hZ hY₁)
  have h4 := (length_div_le Z Y₂ N₂ hZ hN₂ (by linarith)).trans (length_le_add Z Y₂ hZ hY₂)
  have eX : Real.logb Z T = Real.logb Z X₁ + Real.logb Z X₂ := by
    rw [← hXT, Real.logb_mul (by linarith) (by linarith)]
  have eY : Real.logb Z T = Real.logb Z Y₁ + Real.logb Z Y₂ := by
    rw [← hYT, Real.logb_mul (by linarith) (by linarith)]
  exact max_le (by linarith) (by linarith)

/-- **Branch data and envelope range from the defect window.** -/
theorem branch_window (D : StepData) (G : StepGates D) (η : Character) {ε : ℝ} (hε : 0 < ε)
    (r : GSrc θ mesh Z) (tl u lw S P : ℝ)
    (hm0 : 0 ≤ mesh) (hmL : mesh ≤ G.meshL ε) (htl0 : 0 ≤ tl) (htl : tl ≤ G.tlL ε)
    (htlH : tl ≤ 1 - D.Hmin)
    (hS : D.s₀ ≤ S ∧ S ≤ D.c) (hface : P + D.L*S ≤ D.B) (hgP : gP r ≤ P + tl) (hlw : lw ≤ S)
    (hsum : ∑ i, r.w i = lw - u)
    (hlo : -tl ≤ commonH r - 1 + 6*u) (hhi : commonH r - 1 ≤ 1 + tl)
    (hbranch : (G.floor ε ≤ lw ∧ D.sel ε lw ≤ u ∧ u ≤ D.sel ε lw + mesh) ∨
      (lw ≤ G.floor ε ∧ u = 0)) :
    (∃ A c qC : ℝ, BranchData D G (gFrame L θ mesh η Z) ε mesh r A c qC (commonH r) ∧
        A - c + qC ≤ r.colLog + r.twistLog + u) ∧
      (D.Hmin ≤ commonH r ∧ commonH r ≤ D.Hmax) := by
  rcases hbranch with ⟨hfl, hsel1, hsel2⟩ | ⟨hfl, hu⟩
  · have hsc : SideScalars r (r.colLog + u) 0 0 r.twistLog (commonH r - 1 + 6*u - mesh) u :=
      ⟨by ring, by unfold commonH cutoffLog; ring, by ring⟩
    have eS : S - (S - lw) = lw := by ring
    have hf : 0 ≤ S - lw ∧ S - lw ≤ (S - lw) + (P + tl - gP r) := ⟨by linarith, by linarith⟩
    have hroot : gP r + (((S - lw) + (P + tl - gP r)) - (S - lw)) + D.L*S ≤ D.B + tl := by
      linarith
    have hsel : D.sel ε (S - (S - lw)) ≤ u ∧ u ≤ D.sel ε (S - (S - lw)) + mesh := by
      rw [eS]; exact ⟨hsel1, hsel2⟩
    have hs : (∑ i, r.w i) ≤ S - (S - lw) - u := by rw [hsum]; linarith
    have ht : -tl ≤ (commonH r - 1 + 6*u - mesh) + mesh ∧
        (commonH r - 1 + 6*u - mesh) + mesh ≤ 1 + 6*u + tl := ⟨by linarith, by linarith⟩
    have hfloor : G.floor ε ≤ S - (S - lw) := by rw [eS]; exact hfl
    refine ⟨⟨r.colLog + u, 0, r.twistLog + 0 - 0, ?_, by linarith⟩, ?_⟩
    · exact branch_large D G η ε tl r (r.colLog + u) 0 0 r.twistLog _ u hsc S (S - lw) _ (gP r) hS
        hf (gP_nonneg r) hroot hsel hs le_rfl htl0 htl ht hfloor
    · exact commonH_range_large D G hε tl r (r.colLog + u) 0 0 r.twistLog _ u hsc S (S - lw) _
        (gP r) hS hf (gP_nonneg r) hroot hsel (∑ i, r.w i)
        ⟨Finset.sum_nonneg fun i _ => r.hw i, hs⟩ hm0 hmL htl0 htl ht hfloor
  · subst hu
    have hsc : SideScalars r r.colLog 0 0 r.twistLog (commonH r - 1 - mesh) 0 :=
      ⟨by ring, by unfold commonH cutoffLog; ring, by ring⟩
    have hs : (∑ i, r.w i) ≤ G.floor ε := by rw [hsum]; linarith
    refine ⟨⟨r.colLog, 0, r.twistLog + 0 - 0, branch_small D G η ε r r.colLog 0 0 r.twistLog _ hsc hs,
      by linarith⟩, ?_⟩
    exact commonH_range_small D G tl r r.colLog 0 0 r.twistLog _ hsc htlH
      ⟨by linarith, by linarith⟩

end
end Qrh.MarkedAnchor.Ordinary.Second.ProviderGeometry
