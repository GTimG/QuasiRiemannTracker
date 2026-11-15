/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Selection of the marked block D for the second step (CF Section 4, "selected marked factors").
Adapted from Candidate.FourthPower.GlobalSlotSelection and the `chosenSlots` part of
Candidate.FourthPower.OuterFreshSelection (PR76, Copyright (c) 2026 Sil. Apache-2.0).
Modified by Sil (2026-10-26): the target `43/100 * w` is replaced by an arbitrary target
function `sel` (instantiated by `StepData.sel ε`), with one upward mesh error for the whole
block; the 43/100-specific reserves (`large_branch` gate, `gate_with_half_reserve`) are
dropped (the cube-free skeleton pays the price through `StepGates.ledger` instead); the
supplier-lane volume lemmas of OuterFreshSelection are not ported (u-freezing lane).

The selector is the baseline's whole-slot selector (`whole_slot_removal`): it never discards
or rounds individual slots, and it is fixed by the slot widths alone, before any prime
assignment is summed.
Modified by Sil (2026-11-11): mechanical fork into `Qrh.MarkedAnchor.Ordinary`: forked namespaces `QRH.SilDensitySplit.CubeFree.*` renamed, imports of forked modules redirected, unforked namespaces re-opened; forced by the new step gates (`StepGates` without `1 < L`, reference lane). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.StepData
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SlotRemoval

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary.Second.Selection
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths.CenteredMomentSlotRemoval

/-- Upward greedy subset: total width at least `target`, at most `target + mesh`
(and at most the whole width). -/
theorem upward_subset {ι : Type*} (J : Finset ι) (w : ι → ℝ)
    (target mesh : ℝ) (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh)
    (ht : 0 ≤ target) (hfull : target ≤ ∑ i ∈ J, w i) :
    ∃ R : Finset ι, R ⊆ J ∧ target ≤ ∑ i ∈ R, w i ∧
      (∑ i ∈ R, w i) ≤ min (∑ i ∈ J, w i) (target + mesh) := by
  obtain ⟨R, hR, hbound, hpay⟩ := whole_slot_removal J w mesh (1/6) target
    hm (by norm_num) ht hw hwm
  norm_num only [show (6:ℝ)*(1/6) = 1 by norm_num, div_one, one_mul] at hbound hpay
  refine ⟨R, hR, ?_, hbound⟩
  rcases hpay with he | hp
  · simpa only [he] using hfull
  · exact hp

/-- Selection specification with target function `sel` of the total live width `S`:
below the floor `rho` nothing is selected; above it the selected width lies in
`[sel S, sel S + mesh]` (one upward mesh error for the whole block) and below `S`. -/
def Specification {ι : Type*} (J : Finset ι) (w : ι → ℝ) (sel : ℝ → ℝ)
    (rho mesh : ℝ) (R : Finset ι) : Prop :=
  R ⊆ J ∧ ((∑ i ∈ J, w i) ≤ rho → R = ∅) ∧
    (rho < (∑ i ∈ J, w i) →
      sel (∑ i ∈ J, w i) ≤ (∑ i ∈ R, w i) ∧
      (∑ i ∈ R, w i) ≤ min (∑ i ∈ J, w i) (sel (∑ i ∈ J, w i) + mesh))

theorem exists_selection {ι : Type*} (J : Finset ι) (w : ι → ℝ) (sel : ℝ → ℝ)
    (rho mesh : ℝ) (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh)
    (hsel : 0 ≤ sel (∑ i ∈ J, w i) ∧ sel (∑ i ∈ J, w i) ≤ ∑ i ∈ J, w i) :
    ∃ R : Finset ι, Specification J w sel rho mesh R := by
  by_cases hsmall : (∑ i ∈ J, w i) ≤ rho
  · refine ⟨∅, Finset.empty_subset _, fun _ => rfl, ?_⟩
    intro hlarge
    exact (not_lt_of_ge hsmall hlarge).elim
  · obtain ⟨R, hR, hlo, hhi⟩ := upward_subset J w (sel (∑ i ∈ J, w i)) mesh hm hw hwm
      hsel.1 hsel.2
    exact ⟨R, hR, fun h => (hsmall h).elim, fun _ => ⟨hlo, hhi⟩⟩

/-- The concrete selected subset (fixed by the slot widths). -/
def selectedSlots {ι : Type*} (J : Finset ι) (w : ι → ℝ) (sel : ℝ → ℝ)
    (rho mesh : ℝ) (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh)
    (hsel : 0 ≤ sel (∑ i ∈ J, w i) ∧ sel (∑ i ∈ J, w i) ≤ ∑ i ∈ J, w i) : Finset ι :=
  Classical.choose (exists_selection J w sel rho mesh hm hw hwm hsel)

theorem selectedSlots_spec {ι : Type*} (J : Finset ι) (w : ι → ℝ) (sel : ℝ → ℝ)
    (rho mesh : ℝ) (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh)
    (hsel : 0 ≤ sel (∑ i ∈ J, w i) ∧ sel (∑ i ∈ J, w i) ≤ ∑ i ∈ J, w i) :
    Specification J w sel rho mesh (selectedSlots J w sel rho mesh hm hw hwm hsel) :=
  Classical.choose_spec (exists_selection J w sel rho mesh hm hw hwm hsel)

/-- Floor branch: nothing is selected and deleting every residual slot costs at most
`κ * rho`, independently of the number of slots. -/
theorem small_branch {ι : Type*} (J R : Finset ι) (w : ι → ℝ) (sel : ℝ → ℝ)
    (rho mesh κ : ℝ) (hκ : 0 ≤ κ) (hspec : Specification J w sel rho mesh R)
    (hsmall : (∑ i ∈ J, w i) ≤ rho) :
    R = ∅ ∧ (∑ i ∈ R, w i) = 0 ∧ κ*(∑ i ∈ J \ R, w i) ≤ κ*rho := by
  have he := hspec.2.1 hsmall
  refine ⟨he, ?_, ?_⟩
  · rw [he, Finset.sum_empty]
  · rw [he, Finset.sdiff_empty]
    exact mul_le_mul_of_nonneg_left hsmall hκ

/-- Large branch: the selected width `d` is within one mesh above `sel S`, the complement
has width exactly `S - d`, and `d ≤ S`. -/
theorem large_branch {ι : Type*} (J R : Finset ι) (w : ι → ℝ) (sel : ℝ → ℝ)
    (rho mesh : ℝ) (hspec : Specification J w sel rho mesh R)
    (hlarge : rho < (∑ i ∈ J, w i)) :
    sel (∑ i ∈ J, w i) ≤ (∑ i ∈ R, w i) ∧
      (∑ i ∈ R, w i) ≤ sel (∑ i ∈ J, w i) + mesh ∧
      (∑ i ∈ R, w i) ≤ (∑ i ∈ J, w i) ∧
      (∑ i ∈ J \ R, w i) + (∑ i ∈ R, w i) = (∑ i ∈ J, w i) := by
  obtain ⟨hlo, hhi⟩ := hspec.2.2 hlarge
  exact ⟨hlo, hhi.trans (min_le_right _ _), hhi.trans (min_le_left _ _),
    Finset.sum_sdiff hspec.1 (f := w)⟩

/-! ### The step-data target `sel ε` -/

/-- Selection with the step target `D.sel ε`. -/
abbrev StepSpecification (D : StepData) (ε : ℝ) {ι : Type*} (J : Finset ι) (w : ι → ℝ)
    (rho mesh : ℝ) (R : Finset ι) : Prop :=
  Specification J w (D.sel ε) rho mesh R

/-- The step gates supply the target bounds `0 ≤ sel ε S ≤ S` on `[0, c]`. -/
theorem step_sel_bounds {D : StepData} (G : StepGates D) {ε : ℝ} (hε : 0 < ε)
    {ι : Type*} (J : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ J, 0 ≤ w i)
    (hc : (∑ i ∈ J, w i) ≤ D.c) :
    0 ≤ D.sel ε (∑ i ∈ J, w i) ∧ D.sel ε (∑ i ∈ J, w i) ≤ ∑ i ∈ J, w i :=
  (G.sel_spec ε hε).2 _ (Finset.sum_nonneg hw) hc

theorem exists_step_selection {D : StepData} (G : StepGates D) {ε : ℝ} (hε : 0 < ε)
    {ι : Type*} (J : Finset ι) (w : ι → ℝ) (rho mesh : ℝ) (hm : 0 ≤ mesh)
    (hw : ∀ i ∈ J, 0 ≤ w i) (hwm : ∀ i ∈ J, w i ≤ mesh) (hc : (∑ i ∈ J, w i) ≤ D.c) :
    ∃ R : Finset ι, StepSpecification D ε J w rho mesh R :=
  exists_selection J w (D.sel ε) rho mesh hm hw hwm (step_sel_bounds G hε J w hw hc)

/-- The large branch in the form of `SideGeometry.hsel`: with `u` the selected width and
`S - f` the live width, `sel ε (S - f) ≤ u ≤ sel ε (S - f) + mesh`. -/
theorem step_large_sel {D : StepData} {ε : ℝ} {ι : Type*} (J R : Finset ι) (w : ι → ℝ)
    (rho mesh : ℝ) (hspec : StepSpecification D ε J w rho mesh R)
    (hlarge : rho < (∑ i ∈ J, w i)) :
    D.sel ε (∑ i ∈ J, w i) ≤ (∑ i ∈ R, w i) ∧
      (∑ i ∈ R, w i) ≤ D.sel ε (∑ i ∈ J, w i) + mesh :=
  ⟨(large_branch J R w _ rho mesh hspec hlarge).1,
    (large_branch J R w _ rho mesh hspec hlarge).2.1⟩

/-- On the large branch the retained (unselected) width is `S - u` exactly. -/
theorem step_large_rest {D : StepData} {ε : ℝ} {ι : Type*} (J R : Finset ι) (w : ι → ℝ)
    (rho mesh : ℝ) (hspec : StepSpecification D ε J w rho mesh R)
    (hlarge : rho < (∑ i ∈ J, w i)) :
    (∑ i ∈ J \ R, w i) = (∑ i ∈ J, w i) - (∑ i ∈ R, w i) := by
  have h := (large_branch J R w _ rho mesh hspec hlarge).2.2.2
  linarith

/-! ### Live slots (template: `OuterFreshSelection.chosenSlots`) -/

section Live
variable {ι : Type*} [Fintype ι]

/-- Total width of the live slots `L` (indices outside the frozen complement). -/
def liveWidth (L : Finset ι) (w : ι → ℝ) : ℝ := ∑ i : {i // i ∉ Lᶜ}, w i.val

/-- The selected block among the live slots. -/
def chosenSlots (L : Finset ι) (w : ι → ℝ) (sel : ℝ → ℝ) (rho mesh : ℝ)
    (hm : 0 ≤ mesh) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh)
    (hsel : 0 ≤ sel (liveWidth L w) ∧ sel (liveWidth L w) ≤ liveWidth L w) :
    Finset {i // i ∉ Lᶜ} :=
  selectedSlots Finset.univ (fun i : {i // i ∉ Lᶜ} => w i.val) sel rho mesh hm
    (fun i _ => hw i.val) (fun i _ => hwm i.val) hsel

theorem chosen_spec (L : Finset ι) (w : ι → ℝ) (sel : ℝ → ℝ) (rho mesh : ℝ)
    (hm : 0 ≤ mesh) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh)
    (hsel : 0 ≤ sel (liveWidth L w) ∧ sel (liveWidth L w) ≤ liveWidth L w) :
    Specification Finset.univ (fun i : {i // i ∉ Lᶜ} => w i.val) sel rho mesh
      (chosenSlots L w sel rho mesh hm hw hwm hsel) :=
  selectedSlots_spec _ _ _ _ _ _ _ _ _

/-- Removing the selected live slots loses exactly their total width. -/
theorem remaining_width (L : Finset ι) (J : Finset {i // i ∉ Lᶜ}) (w : ι → ℝ) :
    (∑ j ∈ Finset.univ \ J, w j.val) + (∑ j ∈ J, w j.val) = liveWidth L w :=
  Finset.sum_sdiff (Finset.subset_univ J) (f := fun j => w j.val)

/-- Live width plus frozen width is the total width. -/
theorem original_width_partition (L : Finset ι) (w : ι → ℝ) :
    liveWidth L w + (∑ i : ↥Lᶜ, w i.val) = ∑ i, w i := by
  have hLive : liveWidth L w = ∑ i ∈ Finset.univ \ Lᶜ, w i := by
    exact (Finset.sum_subtype (F := inferInstance) (p := fun i => i ∉ Lᶜ)
      (Finset.univ \ Lᶜ) (by simp) w).symm
  rw [hLive, Finset.sum_coe_sort Lᶜ w]
  exact Finset.sum_sdiff (Finset.subset_univ Lᶜ) (f := w)

/-- Floor branch on the live slots: nothing is selected. -/
theorem chosen_small (L : Finset ι) (w : ι → ℝ) (sel : ℝ → ℝ) (rho mesh : ℝ)
    (hm : 0 ≤ mesh) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh)
    (hsel : 0 ≤ sel (liveWidth L w) ∧ sel (liveWidth L w) ≤ liveWidth L w)
    (hsmall : liveWidth L w ≤ rho) :
    chosenSlots L w sel rho mesh hm hw hwm hsel = ∅ :=
  (chosen_spec L w sel rho mesh hm hw hwm hsel).2.1 hsmall

/-- Large branch on the live slots: the selected width `u` satisfies
`sel S ≤ u ≤ sel S + mesh` and the retained live width is `S - u`. -/
theorem chosen_large (L : Finset ι) (w : ι → ℝ) (sel : ℝ → ℝ) (rho mesh : ℝ)
    (hm : 0 ≤ mesh) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh)
    (hsel : 0 ≤ sel (liveWidth L w) ∧ sel (liveWidth L w) ≤ liveWidth L w)
    (hlarge : rho < liveWidth L w) :
    let J := chosenSlots L w sel rho mesh hm hw hwm hsel
    sel (liveWidth L w) ≤ (∑ j ∈ J, w j.val) ∧
      (∑ j ∈ J, w j.val) ≤ sel (liveWidth L w) + mesh ∧
      (∑ j ∈ Finset.univ \ J, w j.val) = liveWidth L w - (∑ j ∈ J, w j.val) := by
  intro J
  have h := large_branch Finset.univ J (fun i : {i // i ∉ Lᶜ} => w i.val) sel rho mesh
    (chosen_spec L w sel rho mesh hm hw hwm hsel) hlarge
  have hr := remaining_width L J w
  exact ⟨h.1, h.2.1, by linarith⟩

end Live

end
end Qrh.MarkedAnchor.Ordinary.Second.Selection
