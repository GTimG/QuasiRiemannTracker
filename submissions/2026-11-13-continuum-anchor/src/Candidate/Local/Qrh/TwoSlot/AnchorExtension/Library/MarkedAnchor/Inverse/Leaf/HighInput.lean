/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Predicate

/-!
# Inverse.Leaf.HighInput

Interface of the inverse LOW/HIGH leaf (the LOW/HIGH split of the INVERSE child).

* `SlotHigh c lam k Z L ell β u` — the row `u` has a HIGH slot: some whole slot `i` of the
  (canonical) slot vector has squared amplitude `‖directSlot‖² > c·Z^(k·ell i + lam)`, i.e. slot
  amplitude exponent above the cut `k` (up to the constant `c` and the loss `lam`). A row with no
  HIGH slot is LOW: every slot may be erased at price `c·Z^(k·ell i + lam)`.
  Relation to the buffered zero bin (SDS `Density.lowRow`, HIGH classes `(ν,e)`, `ν ≥ k`):
  the LOW slot supplier (inverse analogue of HC `actual_low_slots_parent_mask` /
  SDS `uniform_low_slots_parent_mask`) says that a row whose buffered zero bin is `ν < k` has every
  slot `≤ C·Z^(loss)·Z^(k·ell)`. Hence, for `c ≥ C`, `lam ≥ loss`, every `SlotHigh` row has zero
  bin `ν ≥ k`, and the energy over the `SlotHigh` rows is at most the energy over the zero-bin
  HIGH rows (all terms are nonnegative).
* `InverseHighAt` / `InverseHighEnergy fam ρ k x` — the HIGH input: the inverse marked sum over the
  `SlotHigh` rows of the ball (radius `1`, rectangle `ρ`) is `≤ C·Z^(1+x+ε)` (excess `x` over the
  row size). Same hypotheses and quantifier order as `InverseRectSource` (Contract.lean), with the
  slot threshold `(c, lam)`: `lam > 0` is arbitrary and chosen after `K`; `c > 0` is chosen by the
  HIGH supplier, after the row data. The HIGH part of the induction supplies it for the
  inverse child at `ρ = childRect …`, cut `k = cut n`, excess `x = u/(1-6u-κ)` (see
  `Leaf.Chain`).
* `UniformInverseRectSourceExcess fam ρ x` — the inverse contract with row-size excess `x`
  (`∀ ε>0 ∃ mesh>0, InverseRectSource fam ρ mesh (x+ε)`); `x = 0` is `UniformInverseRectSource`.
  This is the form in which the second Poisson step consumes the child: a physical child moment
  bounded by `Z^(H+u+ε)` (excess `u` over the child radius `H`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Leaf
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseRawInitialGates
open Qrh.MarkedAnchor.Interface.Contract
local notation "O" => HeckeFamily.O

/-! ## The row classifier -/

/-- The row `u` has a HIGH slot at threshold `(c, lam)` and cut `k`. -/
def SlotHigh (c lam k Z : ℝ) {ι : Type} (L : ι → Finset (Ideal O)) (ell : ι → ℝ)
    (β : ι → Ideal O → ℂ) (u : HeckeInverseAmplification.NonzeroElement) : Prop :=
  ∃ i, c * Z^(k * ell i + lam) < ‖directSlot u.val (L i) (β i) (Z^(ell i))‖^2

/-- A row without HIGH slot has every slot bounded by the erasure price. -/
theorem not_slotHigh {c lam k Z : ℝ} {ι : Type} {L : ι → Finset (Ideal O)} {ell : ι → ℝ}
    {β : ι → Ideal O → ℂ} {u : HeckeInverseAmplification.NonzeroElement}
    (h : ¬ SlotHigh c lam k Z L ell β u) (i : ι) :
    ‖directSlot u.val (L i) (β i) (Z^(ell i))‖^2 ≤ c * Z^(k * ell i + lam) := by
  by_contra hlt
  exact h ⟨i, lt_of_not_ge hlt⟩

/-- A larger threshold has fewer HIGH rows. -/
theorem slotHigh_mono {c c' lam lam' k Z : ℝ} (hZ : 1 ≤ Z) (hc : c ≤ c') (hc0 : 0 ≤ c)
    (hl : lam ≤ lam') {ι : Type} {L : ι → Finset (Ideal O)} {ell : ι → ℝ}
    {β : ι → Ideal O → ℂ} {u : HeckeInverseAmplification.NonzeroElement}
    (h : SlotHigh c' lam' k Z L ell β u) : SlotHigh c lam k Z L ell β u := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, lt_of_le_of_lt ?_ hi⟩
  have h1 : Z^(k * ell i + lam) ≤ Z^(k * ell i + lam') :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h0 : 0 ≤ Z^(k * ell i + lam) := Real.rpow_nonneg (zero_le_one.trans hZ) _
  exact mul_le_mul hc h1 h0 (hc0.trans hc)

/-! ## The HIGH input -/

/-- The HIGH energy at one scale: the inverse marked sum over the `SlotHigh` rows of the unit
ball, for every accepted slot vector of the class (same hypotheses as `InverseRectAt` at radius
`1`), is at most `C·Z^(1+x+ε)` times the height polynomial. As in `InverseRectAt`,
every slot height bound `hv ≥ 0` is paid by `((1+‖θ‖+hv)^degree)^2`. -/
def InverseHighAt (cls : SlotClass) (ρ : AnchorRect) (Φ : ℝ → ℂ) (K : ℕ) (mesh ε Z : ℝ)
    (data : RowData) (degree : ℕ) (c lam k x C : ℝ) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ K →
  ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (hv : ℝ), 0 ≤ hv →
    cls ι data L ell β Z hv →
    (∀ i, 0 ≤ ell i) → (∀ i, ell i ≤ mesh) → (∀ i, ∀ P ∈ L i, Prime P) →
    (∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/Z^(ell i)) ∈ Icc (1 : ℝ) 2) →
    (∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1) →
    (∀ i, ((deletedBase data).modulus.absNorm : ℝ) < Z^(ell i)) →
  ∀ r : ℝ, ρ.Admissible r (∑ i, ell i) 1 →
  ∀ rows : Finset HeckeInverseAmplification.NonzeroElement,
    (∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ Z) → ∀ θ : ℝ,
    inverseMarkedSum data Φ L ell β (rows.filter (fun u => SlotHigh c lam k Z L ell β u))
      Z r θ ≤ C*Z^(1+x+ε)*((1+‖θ‖+hv)^degree)^2

/-- **HIGH input** for the inverse child on the rectangle `ρ` (radius `1`) at cut `k` with
row-size excess `x`. Quantifiers: `∀ε>0 ∃mesh>0, ∀K, ∀lam>0, ∀cls∈fam, ∀Φ, ∀data,
∃ degree c C Z₀, ∀ Z ≥ Z₀` (the degree may depend on the row data). -/
def InverseHighEnergy (fam : SlotClass → Prop) (ρ : AnchorRect) (k x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧
  ∀ K : ℕ, ∀ lam : ℝ, 0 < lam → ∀ cls : SlotClass, fam cls →
  ∀ (Φ : ℝ → ℂ) (ao bo : ℝ), 0 < ao → ao ≤ bo → Function.support Φ ⊆ Icc ao bo →
    ContDiff ℝ ∞ Φ →
  ∀ data : RowData, ∃ (degree : ℕ) (c C Z₀ : ℝ), 0 < c ∧ 0 < C ∧ 1 < Z₀ ∧
    ∀ Z : ℝ, Z₀ ≤ Z → InverseHighAt cls ρ Φ K mesh ε Z data degree c lam k x C

/-- A larger excess is a weaker HIGH input. -/
theorem InverseHighEnergy.mono_excess {fam : SlotClass → Prop} {ρ : AnchorRect} {k x x' : ℝ}
    (hxx : x ≤ x') (h : InverseHighEnergy fam ρ k x) : InverseHighEnergy fam ρ k x' := by
  intro ε hε
  obtain ⟨mesh, hmesh, h⟩ := h ε hε
  refine ⟨mesh, hmesh, fun K lam hlam cls hcls Φ ao bo hao hab hΦs hΦ data => ?_⟩
  obtain ⟨degree, c, C, Z₀, hc, hC, hZ₀, hb⟩ :=
    h K lam hlam cls hcls Φ ao bo hao hab hΦs hΦ data
  refine ⟨degree, c, C, Z₀, hc, hC, hZ₀, fun Z hZ => ?_⟩
  intro ι _ _ hK L ell β hv hv0 hcl h1 h2 h3 h4 h5 h6 r hadm rows hrows θ
  refine (hb Z hZ hK L ell β hv hv0 hcl h1 h2 h3 h4 h5 h6 r hadm rows hrows θ).trans ?_
  have hZ1 : 1 ≤ Z := hZ₀.le.trans hZ
  have hpos : 0 ≤ ((1+‖θ‖+hv)^degree)^2 := by positivity
  apply mul_le_mul_of_nonneg_right _ hpos
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)) hC.le

/-- A larger rectangle gives a stronger HIGH input. -/
theorem InverseHighEnergy.restrict {fam : SlotClass → Prop} {strong weak : AnchorRect}
    {k x : ℝ} (hρ : strong.Restricts weak) (h : InverseHighEnergy fam strong k x) :
    InverseHighEnergy fam weak k x := by
  intro ε hε
  obtain ⟨mesh, hmesh, h⟩ := h ε hε
  refine ⟨mesh, hmesh, fun K lam hlam cls hcls Φ ao bo hao hab hΦs hΦ data => ?_⟩
  obtain ⟨degree, c, C, Z₀, hc, hC, hZ₀, hb⟩ :=
    h K lam hlam cls hcls Φ ao bo hao hab hΦs hΦ data
  refine ⟨degree, c, C, Z₀, hc, hC, hZ₀, fun Z hZ => ?_⟩
  intro ι _ _ hK L ell β hv hv0 hcl h1 h2 h3 h4 h5 h6 r hadm rows hrows θ
  exact hb Z hZ hK L ell β hv hv0 hcl h1 h2 h3 h4 h5 h6 r
    (AnchorRect.admissible_of_restricts hρ zero_le_one hadm) rows hrows θ

/-! ## The contract with excess -/

/-- The inverse contract on `ρ` (radius `1`) with row-size excess `x`. -/
def UniformInverseRectSourceExcess (fam : SlotClass → Prop) (ρ : AnchorRect) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧ InverseRectSource fam ρ mesh (x+ε)

theorem uniformInverseRectSourceExcess_zero {fam : SlotClass → Prop} {ρ : AnchorRect} :
    UniformInverseRectSourceExcess fam ρ 0 ↔ UniformInverseRectSource fam ρ := by
  unfold UniformInverseRectSourceExcess UniformInverseRectSource
  simp only [zero_add]

/-- A row-sized source has every nonnegative excess. -/
theorem UniformInverseRectSource.excess {fam : SlotClass → Prop} {ρ : AnchorRect} {x : ℝ}
    (hx : 0 ≤ x) (h : UniformInverseRectSource fam ρ) :
    UniformInverseRectSourceExcess fam ρ x := by
  intro ε hε
  obtain ⟨mesh, hmesh, hs⟩ := h ε hε
  refine ⟨mesh, hmesh, fun K cls hcls Φ ao bo hao hab hΦs hΦ data => ?_⟩
  obtain ⟨degree, C, Z₀, hC, hZ₀, hb⟩ := hs K cls hcls Φ ao bo hao hab hΦs hΦ data
  exact ⟨degree, C, Z₀, hC, hZ₀, fun Z hZ =>
    inverseRectAt_mono Φ K mesh 1 1 ε (x+ε) Z data degree C C 1 1 le_rfl le_rfl
      (hZ₀.le.trans hZ) (by linarith) hC.le le_rfl (hb Z hZ)⟩

theorem UniformInverseRectSourceExcess.restrict {fam : SlotClass → Prop}
    {strong weak : AnchorRect} {x : ℝ} (h : strong.Restricts weak)
    (hs : UniformInverseRectSourceExcess fam strong x) :
    UniformInverseRectSourceExcess fam weak x := by
  intro ε hε
  obtain ⟨mesh, hmesh, hsrc⟩ := hs ε hε
  exact ⟨mesh, hmesh, hsrc.restrict h⟩

theorem UniformInverseRectSourceExcess.mono_excess {fam : SlotClass → Prop} {ρ : AnchorRect}
    {x x' : ℝ} (hxx : x ≤ x') (hs : UniformInverseRectSourceExcess fam ρ x) :
    UniformInverseRectSourceExcess fam ρ x' := by
  intro ε hε
  obtain ⟨mesh, hmesh, hsrc⟩ := hs ε hε
  refine ⟨mesh, hmesh, fun K cls hcls Φ ao bo hao hab hΦs hΦ data => ?_⟩
  obtain ⟨degree, C, Z₀, hC, hZ₀, hb⟩ := hsrc K cls hcls Φ ao bo hao hab hΦs hΦ data
  exact ⟨degree, C, Z₀, hC, hZ₀, fun Z hZ =>
    inverseRectAt_mono Φ K mesh 1 1 (x+ε) (x'+ε) Z data degree C C 1 1 le_rfl le_rfl
      (hZ₀.le.trans hZ) (by linarith) hC.le le_rfl (hb Z hZ)⟩

end
end Qrh.MarkedAnchor.Inverse.Leaf

#print axioms Qrh.MarkedAnchor.Inverse.Leaf.InverseHighEnergy.mono_excess
#print axioms Qrh.MarkedAnchor.Inverse.Leaf.UniformInverseRectSource.excess
