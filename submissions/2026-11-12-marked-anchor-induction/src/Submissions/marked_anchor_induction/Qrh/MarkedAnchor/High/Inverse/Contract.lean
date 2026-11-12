/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Leaf.Chain
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Weighted
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.PriceFloor
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Marked.InvCore

/-!
# High.Inverse.Contract — the marked inputs and the leaf statement of the inverse HIGH child

* `raySlot` — a canonical slot of the fixed ray data at scale `U` and relative width `wr s`
  (`directSlot` of `canonicalPool rayM G.pool (U^wr)` with the `canonicalSlots` coefficient);
  `raySlot_eq_G1`: it is `Marked.raySlotG1` (by `rfl`).
* **`HighMarkedInverseCoreInputs a0 a1 wlo`**:
  - inverse half: `Marked.HighMarkedInverseInvField a0 a1 wlo` — the `inverseMarked` field on rows
    `NonzeroElement` of the ball, family `data.character u`, slots `raySlot`, every witness width
    `x ∈ [wc, 1)`, `wc ≥ wlo`;
  - plain half: `Marked.MarkedCoreR1 a0 a1 wlo` — the core form (rows `RegularCore` sixth-free
    `FreeRow` cores, family `coreFamily`, slots `coreSlot`, bounded heights, no slot separation),
    whose `PlainMarkedField` is the plain witness factor on the cofactor cores (as in the ordinary
    leaf). The plain field on all `NonzeroElement` rows / every `RowData` is NOT derivable from the
    ordinary anchors (fixed-inducing rows); the leaf pays fixed-inducing rows by a native bound.
  Both halves are proved per stage (`highMarkedInverseCoreInputs_stage`).
* `InverseHighPricedAt` / `InverseHighPriced fam a0 a1 k wlo` — the stage-free form of the HIGH
  input (`Inverse.Leaf.InverseHighEnergy`) with the excess replaced by the floored HIGH price
  `highPriceFW a0 a1 k wlo r (∑ ell) 1` of the actual free width and slot width.
* `InverseHighLeaf` — the analytic detector leaf (inverse analogue of `high_branch_mesh`):
  marked inputs ⇒ priced HIGH energy for `canonicalFamily` (fixed ray data). Proved in
  `High.Inverse.Leaf` (`inverseHighLeaf`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Inverse
noncomputable section

open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseRawInitialGates
open Qrh.MarkedAnchor.High
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Inverse.Leaf
open Qrh.MarkedAnchor.Anchor.ChainData
local notation "O" => HeckeFamily.O
local instance contractQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- The canonical slot `s` of the fixed ray data at scale `U`, relative width `wr s`, character
`θ s`, imaginary height `v s` (real part `33/50`). -/
def raySlot (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ) (data : RowData)
    {Slot : Type} (U : ℝ) (θ : Slot → RayQuotient.Characters rayM G.twist) (wr v : Slot → ℝ)
    (u : NonzeroElement) (s : Slot) : ℂ :=
  directSlot u.val (canonicalPool rayM G.pool (U^(wr s)))
    (rayCoeff rayM G hH W (33/50) data (θ s) (U^(wr s)) (v s)) (U^(wr s))

theorem raySlot_eq_G1 (rayM : Ideal O) [NeZero rayM] (G : SlotTwist rayM)
    (hH : RayOrthogonality.globalUnits rayM ≤ G.twist) (W : ℝ → ℂ) (data : RowData)
    {Slot : Type} (U : ℝ) (θ : Slot → RayQuotient.Characters rayM G.twist) (wr v : Slot → ℝ) :
    raySlot rayM G hH W data U θ wr v = Marked.raySlotG1 rayM G hH W data U θ wr v := rfl

/-- **The marked inputs of the inverse HIGH detector**: the inverse field
on the rows of the ball (`raySlot` slots) and the core form `MarkedCoreR1` (whose plain field is
used on the sixth-power cofactor cores). Line `(a0, a1)`, cutoff floor `wlo`. -/
def HighMarkedInverseCoreInputs (a0 a1 wlo : ℝ) : Prop :=
  Marked.HighMarkedInverseInvField a0 a1 wlo ∧ Marked.MarkedCoreR1 a0 a1 wlo

/-- **The marked inputs per stage** (`highMarkedInverseInvField_stage`, `markedCoreR1_stage`). -/
theorem highMarkedInverseCoreInputs_stage (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hres : Qrh.MarkedAnchor.Interface.Native.ReserveParametricSource) (n : ℕ) (hn : n < 176)
    (hE : EarlierAnchors n) :
    HighMarkedInverseCoreInputs (a0 n) (a1 n) ((R n : ℝ) + 1/1000000) :=
  ⟨Marked.highMarkedInverseInvField_stage n hn hE, Marked.markedCoreR1_stage hβ hres n hn hE⟩

/-- The priced HIGH energy at one scale: as `InverseHighAt`, for every free width `r ∈ [0,1]`,
with the excess replaced by the floored HIGH price of `(r, ∑ ell)` at radius `1`. Every
slot height bound `hv ≥ 0` of the class is paid by `((1+‖θ‖+hv)^degree)^2`. -/
def InverseHighPricedAt (cls : SlotClass) (Φ : ℝ → ℂ) (K : ℕ) (mesh ε Z : ℝ)
    (data : RowData) (degree : ℕ) (c lam k a0 a1 wlo C : ℝ) : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ K →
  ∀ (L : ι → Finset (Ideal O)) (ell : ι → ℝ) (β : ι → Ideal O → ℂ) (hv : ℝ), 0 ≤ hv →
    cls ι data L ell β Z hv →
    (∀ i, 0 ≤ ell i) → (∀ i, ell i ≤ mesh) → (∀ i, ∀ P ∈ L i, Prime P) →
    (∀ i, ∀ P ∈ L i, ((P.absNorm : ℝ)/Z^(ell i)) ∈ Icc (1 : ℝ) 2) →
    (∀ i, ∀ P ∈ L i, ‖β i P‖ ≤ 1) →
    (∀ i, ((deletedBase data).modulus.absNorm : ℝ) < Z^(ell i)) →
  ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
  ∀ rows : Finset NonzeroElement,
    (∀ u ∈ rows, ‖ConcreteTraceCRT.eisEmbedding u.val‖^2 ≤ Z) → ∀ θ : ℝ,
    inverseMarkedSum data Φ L ell β (rows.filter (fun u => SlotHigh c lam k Z L ell β u))
      Z r θ ≤ C*Z^(1 + highPriceFW a0 a1 k wlo r (∑ i, ell i) 1 + ε)*((1+‖θ‖+hv)^degree)^2

/-- **The priced HIGH input** (stage-free; quantifiers of `InverseHighEnergy`, degree depending on
the row data). -/
def InverseHighPriced (fam : SlotClass → Prop) (a0 a1 k wlo : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧
  ∀ K : ℕ, ∀ lam : ℝ, 0 < lam → ∀ cls : SlotClass, fam cls →
  ∀ (Φ : ℝ → ℂ) (ao bo : ℝ), 0 < ao → ao ≤ bo → Function.support Φ ⊆ Icc ao bo →
    ContDiff ℝ ∞ Φ →
  ∀ data : RowData, ∃ (degree : ℕ) (c C Z₀ : ℝ), 0 < c ∧ 0 < C ∧ 1 < Z₀ ∧
    ∀ Z : ℝ, Z₀ ≤ Z → InverseHighPricedAt cls Φ K mesh ε Z data degree c lam k a0 a1 wlo C

/-- **The inverse HIGH detector leaf** (statement; proved as `inverseHighLeaf`): the marked inputs
give the priced HIGH energy of the fixed-ray canonical family. -/
def InverseHighLeaf : Prop :=
  ∀ (a0 a1 k wlo : ℝ), (51/100 : ℝ) ≤ HeckeZeroSupremum.beta → 1/6 ≤ k → k ≤ 3/4 →
    0 ≤ a1 → a1 ≤ 1/2 → wlo ≤ cutHi →
    HighMarkedInverseCoreInputs a0 a1 wlo → InverseHighPriced canonicalFamily a0 a1 k wlo

end
end Qrh.MarkedAnchor.High.Inverse
