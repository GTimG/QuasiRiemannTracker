/- Modified by Joseph Bebel (2026-11-12): smaller-tolerance inverse
HIGH leaf; original coefficient, mask and principal-row proofs are retained. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Inverse.Leaf.HighInput
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Weighted
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.PriceFloor
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.Sources

/-!
# The smaller-tolerance inverse HIGH contract

`raySlot` retains the actual fixed-ray canonical coefficients.
`HighMarkedInverseCoreInputs` is the paired, bounded-height core-form input
`MarkedCoreR1`. The original contract's additional raw-row inverse field was
unused by the inverse leaf; the proved leaf here requires only the input that
its physical class estimates actually consume. Principal and fixed-inducing
rows retain their separate estimates.

`InverseHighPriced` records the full masked inverse HIGH energy with its actual
floored price, and `InverseHighLeaf` supplies that estimate from the paired
core source. There is no stage-table hypothesis in these contracts.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Inverse
noncomputable section
variable [shift : WitnessShift]

open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths QRH.Record12518109Source QRH.Record12518109Existence
open HeckeFamily HeckeDyadic HeckeInverseAmplification
open DetectorDictionaryInverseRawInitialGates
open Qrh.TwoSlot.AnchorZeroLoss.High
open Qrh.MarkedAnchor.Interface.Contract Qrh.MarkedAnchor.Inverse.Leaf
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

/-- The paired core-form input actually consumed by the inverse HIGH leaf. -/
def HighMarkedInverseCoreInputs (a0 a1 wlo : ℝ) : Prop :=
  Marked.MarkedCoreR1 a0 a1 wlo (1/10000000000000) WitnessShift.value

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
end Qrh.TwoSlot.AnchorZeroLoss.High.Inverse
