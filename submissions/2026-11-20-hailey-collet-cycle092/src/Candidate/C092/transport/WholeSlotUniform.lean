/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Early source mesh and whole-slot selection, uniform in the radial parameter. -/
import Candidate.C092.transport.WholeSlotApplication

set_option autoImplicit false
namespace QRH.Cycle092.WholeSlot
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths
open HeckeFamily QRH.Cycle092.NativeStrip QRH.Record12518109Source QRH.Record12518109Existence
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

/-- The original labelled energy source, simultaneously at every U^V with
V bounded below. The mesh precedes the finite slot type and all ray/profile
metadata; the constants precede both the live scale and the radius. -/
def RadiusUnitBox (N Y l mesh ε Vmin : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α],
  ∀ (rayM : Ideal O) [NeZero rayM] (Hr : Subgroup (O⧸rayM)ˣ)
    (hHr : RayOrthogonality.globalUnits rayM ≤ Hr),
  ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1 : ℝ) 2 →
  ∀ bΦ : ℝ, 2 ≤ bΦ → ∀ (η η₀ : Character) (Q : Ideal O),
    Q ≤ rayM → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
    internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
    ∃ degree : ℕ, ∃ controls : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ᶠ U : ℝ in atTop, ∀ V : ℝ, Vmin ≤ V →
        LabelledAt (α := α) rayM Hr hHr N Y l W 2 (1/4) (9/4) bΦ mesh
          (33/50) (33/50) 1 1 ε (U^V) η η₀ Q degree controls C

/-- No new analytic supplier is assumed: a genuine earlier UniformBox gives
this uniform-radius version with its original unchanged mesh and constants. -/
theorem uniformBox_radius {N Y l ε Vmin : ℝ}
    (hsrc : UniformBox N Y l) (hε : 0 < ε) (hVmin : 0 < Vmin) :
    ∃ mesh : ℝ, 0 < mesh ∧ RadiusUnitBox N Y l mesh ε Vmin := by
  obtain ⟨mesh,hm,hbox⟩ := hsrc ε hε
  refine ⟨mesh,hm,?_⟩
  intro α _ _ rayM _ Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨degree,controls,C,hC,h⟩ := hbox α rayM Hr hHr W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨Z₀,hZ₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨degree,controls,C,hC,?_⟩
  have hlarge := (tendsto_rpow_atTop hVmin).eventually (eventually_ge_atTop Z₀)
  filter_upwards [hlarge,eventually_ge_atTop (1 : ℝ)] with U hUmin hU
  intro V hV
  exact hZ₀ (U^V) (hUmin.trans (Real.rpow_le_rpow_of_exponent_le hU hV))

/-- One fixed positive original mesh works before all radial subdivisions,
using precisely w/V as the retained source's relative width. -/
theorem uniformBox_early_radial_mesh {N Y l ε Vmin : ℝ}
    (hsrc : UniformBox N Y l) (hε : 0 < ε) (hVmin : 0 < Vmin) :
    ∃ originalMesh sourceMesh : ℝ, 0 < originalMesh ∧ 0 < sourceMesh ∧
      originalMesh = Vmin*sourceMesh ∧ RadiusUnitBox N Y l sourceMesh ε Vmin ∧
      ∀ V w : ℝ, Vmin ≤ V → w ≤ originalMesh → w/V ≤ sourceMesh := by
  obtain ⟨mesh,hm,hbox⟩ := uniformBox_radius hsrc hε hVmin
  refine ⟨Vmin*mesh,mesh,mul_pos hVmin hm,hm,rfl,hbox,?_⟩
  intro V w hV hw
  exact mesh_rescale hVmin hV hm.le le_rfl hw

/-- The selected whole set is fixed before ordinary lengths, masks, rows and
amplitudes. Any true ordinary shortening inside the earlier rectangle then
satisfies the exact retained source box. Exhaustion keeps every original slot. -/
theorem selection_with_source_boxes {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (w : Slot → ℝ) (mesh V l : ℝ) (hw : ∀ i, 0 ≤ w i) (hwm : ∀ i, w i ≤ mesh)
    (hmesh : 0 ≤ mesh) (hV : 0 ≤ V) (hl : 0 ≤ l) :
    ∃ F : Finset Slot, (∑ i ∈ F, w i) ≤ V*l ∧
      (∑ i ∈ Finset.univ\F, w i) ≤ max 0 ((∑ i, w i)-V*l+mesh) ∧
      ((∑ i, w i) ≤ V*l → F = Finset.univ) ∧
      ∀ N Y x y : ℝ, Box N Y 0 x y 0 → Box N Y (V*l) x y (∑ i ∈ F, w i) := by
  obtain ⟨F,hF,hdel,hex⟩ := select_before_rows w mesh (V*l) hw hwm hmesh (mul_nonneg hV hl)
  refine ⟨F,hF,hdel,hex,?_⟩
  intro N Y x y hbox
  exact ⟨hbox.1,hbox.2.1,hbox.2.2.1,Finset.sum_nonneg (fun i _ => hw i),hF⟩

end
end QRH.Cycle092.WholeSlot
