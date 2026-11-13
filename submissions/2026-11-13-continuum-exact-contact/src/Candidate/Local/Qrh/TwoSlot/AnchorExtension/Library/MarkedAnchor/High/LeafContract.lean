/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
`HighBranchMesh` is sil-density-split's `high_branch` (Apache-2.0) with the cut fixed, an arbitrary
HIGH price and the whole-slot mesh added. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.High.Weighted
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.High.RowSplit
import Submissions.hailey_collet_1252270103.Record12518109Gain.WholeRegularSetup

/-!
# High.LeafContract

The statements the HIGH leaf is built against. These are definitions only;
nothing here is assumed as an axiom.

* `HighBranchMesh high q` — sil-density-split's `high_branch` with the cut fixed to `q`, the HIGH
  price `high`, and one change which the detector method needs: every slot width is at most a
  `mesh` (`∀ i, w i ≤ mesh`), and the exponent carries `+ mesh`. The whole-slot selection loses one
  slot width; without the mesh, slot widths are only `≤ 1`, so the loss is not small.
  `PricedPackedAt` already has `w i ≤ mesh`, with `mesh ≤ meshMax` chosen after `ε`.
* `tinyCore Z v z` — `z = f⁶ c` with `N(c) ≤ Z^v` (the tiny cores, `v = 2/25`).
* `TinyCoreCount` — the lattice count of tiny-core rows, `#{z : N(z) ≤ X, tinyCore} ≤ C X^(1/6+δ) Z^(5v/6+δ)`
  (sixth-power counting).
* Core batches: `coreFamily`,
  `coreSlot`, `RegularCore` (HC `wholeNaturalBatch` objects for the fixed dictionary of the state
  character), and
  - `HighMarkedCoreInputs a0 a1 wlo` — the MARKED fields (`inverseMarked`, `plainMarked`) of
    `AnchorFiberMoments` on core fibers, for cutoffs `wc ≥ wlo`, with a total witness function
    (the leaf uses the row-local, bounded-height form `HighMarkedCoreInputsH` of
    `High.LeafMarkedInput`);
  - `HighCoreFiberInputs a0 a1 wlo` — the whole `AnchorFiberMoments` on core fibers; it follows from
    `HighMarkedCoreInputs` and `Cofactor.core_unmarked_fields` (`High.CoreInputs`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set
open QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree QRH.SilDensitySplit.Density
open OAI OAI.SevenEighths OAI.SevenEighths.Cycle61Moment
open HeckeFamily CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open ConcretePrimeRowBridge CenteredMomentPrimeSlot CenteredMomentEnergyState
open CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open LocalMoment HeckeDyadic HeckeDetectorWitnessRows CenteredMomentWholeSlotDeletion
open HeckeDetectorSupportedWitness HeckeDetectorRowwisePolynomial HeckeInverseAmplification
local notation "O" => HeckeFamily.O
local instance leafContractQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- **The HIGH rows statement with the whole-slot mesh.** sil-density-split's `high_branch` at the
cut `q` with the HIGH price `high`, plus
* `0 ≤ mesh`, `∀ i, w i ≤ mesh` and `+ mesh` in the exponent (the bound `w i ≤ 1` is kept);
* a row-width floor `Mmin > 0` (`Mmin ≤ st.rowWidth`) and the detector budget
  `ε_det := 592 e + 4 d v / min Mmin (2/25) ≤ 10^-6`, `200 ε_det (Mcap+1) ≤ loss·Mmin` (the
  detector runs at core widths down to the tiny-core threshold `2/25`). These come from the
  witness family: buffer `e`, height budget `(Z^d)^v` read at the detector scale `≥ Z^Mmin`, and the
  `10^-6` cutoff padding;
* `loss` and `Mmin` come first (with `0 < loss ≤ 1`, `0 < Mmin`), then
  `∃ meshH > 0` before all data, and `mesh ≤ meshH` is required: the anchors' marked moments hold
  only for slot widths below a mesh fixed by the moment loss (`meshH = meshm(εm)·Mmin/2`, `εm` from
  `loss, Mmin`). The leaf `Price.anchor_priced_source` picks `loss` from `ε, Mmax` and its mesh
  bound `≤ meshH` right after `ε`. -/
def HighBranchMesh (high : QRH.SilDensitySplit.CubeFree.Price) (q : ℝ) : Prop :=
  ∀ (loss Mmin : ℝ), 0 < loss → loss ≤ 1 → 0 < Mmin → ∃ meshH : ℝ, 0 < meshH ∧
  ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) {α : Type} [Fintype α] [DecidableEq α]
    (W : ℝ → ℂ), Function.support W ⊆ Set.Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
    ∀ (bΦ : ℝ), 1 ≤ bΦ → ∀ {κ : Type} [Fintype κ] (anchors : κ → Character) (η₀ : Character),
    (51/100:ℝ) ≤ HeckeZeroSupremum.beta → HeckeZeroSupremum.beta ≤ 7/8 →
    ∀ (Mcap Lplain ε₁ e kap v d mesh : ℝ), 0 ≤ Lplain →
    0 < ε₁ → 0 < e → e < 1/1000 → 0 < kap → kap ≤ 1 →
    0 ≤ v → 0 < d → Mcap+0+1 ≤ d →
    8*e*(1/d)+kap ≤ ε₁ →
    12*e*(Lplain/d+2)+8*kap+2*v ≤ ε₁ →
    0 ≤ mesh → mesh ≤ meshH →
    592*e + 4*d*v/min Mmin (2/25) ≤ 1/1000000 →
    200*(592*e + 4*d*v/min Mmin (2/25))*(Mcap+1) ≤ loss*Mmin →
    ∃ J : ℕ, ∀ τ : ℝ, 0 < τ → ∃ K : ℝ, 0 < K ∧ ∃ S : Finset (ℕ×ℕ),
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ 2 < Z^τ ∧
      ∀ (j : κ) (w₀ : ℝ),
      ∀ st : NaturalState Z 0 bΦ, st.character = anchors j → st.puncture = 1 →
        st.width ≤ Mcap → Mmin ≤ st.rowWidth →
      ∀ (hQM : st.fixedModulus ≤ rayM) (hQη : st.fixedModulus ≤ η₀.modulus) (h : ℕ),
      ∀ (T : Finset α) (θ : T → RayQuotient.Characters rayM H) (w σ v' : T → ℝ)
        (t height : ℝ),
      (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) → (∀ i, w i ≤ 1) →
      (∀ i, (33/50:ℝ) ≤ σ i) → (∀ i, σ i ≤ 33/50) →
      0 ≤ height → (∀ i, |v' i| ≤ height) →
      |t| + height + Z^τ/2 ≤ (3*h+2 : ℕ)*Z^τ → (h:ℝ) ≤ |t| + height + 1 →
      (3 + 3*(((bufferCount e + 1)*(h+1) : ℕ) : ℝ)*Z^τ)^4 ≤ (Z^d)^v →
      ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
        length Z X₁ ≤ Lplain → length Z X₂ ≤ Lplain →
      energy st.character st.mask 1 t (p.profile 0) (p.profile 1)
        (fun i => primePool rayM H 2 (Z^(w i)))
        (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θ i)) I *
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v' i) I)
        (fun i => Z^(w i)) X₁ X₂
        (fun z => st.radial.keep z ∧
          ¬ lowRow rayM H hH st η₀ hQM hQη e (((h+1 : ℕ) : ℝ)*Z^τ) q z)
        st.radial.profile st.radial.scale ≤
      K * QuadraticInitialBound.diagonalControl st.radial.profile * (p.control S)^2 *
        (1+|t|+height)^J *
        Z^(st.rowWidth + high.f w₀ (length Z X₁ + length Z X₂) (∑ i, w i) st.rowWidth +
          (2*ε₁*d*(Fintype.card α + 1) + loss*Mcap + τ*J + mesh))

/-- Tiny core: `z = f⁶ c` with `N(c) ≤ Z^v`. -/
def tinyCore (Z v : ℝ) (z : O) : Prop :=
  ∃ f c : O, z = f^6 * c ∧ ((Ideal.span {c}).absNorm : ℝ) ≤ Z^v

/-- **Tiny-core count**: rows of norm `≤ X` with a core of norm `≤ Z^v` number at
most `C X^(1/6 + δ) Z^(5v/6 + δ)`. -/
def TinyCoreCount : Prop :=
  ∀ v δ : ℝ, 0 ≤ v → 0 < δ → ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ X : ℝ, 1 ≤ X →
    ∀ rows : Finset O, (∀ z ∈ rows, z ≠ 0 ∧ ((Ideal.span {z}).absNorm : ℝ) ≤ X ∧ tinyCore Z v z) →
      (rows.card : ℝ) ≤ C * X^(1/6 + δ) * Z^(5*v/6 + δ)

/-! ### Core batches of one sixth-power cofactor class

A raw HIGH row `z = c·B⁶` (`sixthFrequencyEquiv (c, B)`) with sixth-free core `c : FreeRow` is
counted inside the batch of its cofactor class `B`, at the core scale `U_B = Z^(coreWidth Z M B +
margin)` (`High.Cofactor.Lift.coreWidth`), with the objects of Hailey Collet's
`Record12518109Natural.wholeNaturalBatch` for the FIXED dictionary of the state character `η`
(`wholeRegularDictionary rayM H hH η η₀`):
* `coreFamily`: the clean core family `j ↦ naturalRow (cleanWholeBase … j) c` (its zero maxima equal
  those of the raw row's whole-source family, `source_root_maximum_eq_clean`);
* `coreSlot`: the core slots (the raw slots are compared with them by
  `eventually_whole_original_raw_max_comparison`, factor `4^#slots`); slot widths are RELATIVE to
  `U` (`wr = w/(coreWidth + margin)`), so the prime pools are `primePool (U^wr) = primePool (Z^w)`.
The rows of a core batch are regular (`¬ exceptionalCore`, the finitely many exceptional cores are
removed as in HC). -/

section Core
variable (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
  (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- The clean core family of the fixed dictionary of `η` (HC `wholeNaturalBatch.family`). -/
def coreFamily (η η₀ : Character) (u : FreeRow) (j : WholeSourceIndex rayM H) : Character :=
  (CenteredMomentNaturalRowSource.naturalRow
    (OAI.SevenEighths.Record12518109Natural.cleanWholeBase rayM H hH η η₀ j)
    u.val u.property.1).character

/-- The core slots at scale `U` with relative widths `wr` (HC `wholeNaturalBatch.Q`). -/
def coreSlot {Slot : Type} (η η₀ : Character) (W : ℝ → ℂ) (U : ℝ)
    (θ : Slot → RayQuotient.Characters rayM H) (wr σ v : Slot → ℝ) (t : FreeRow → ℝ)
    (u : FreeRow) (s : Slot) : ℂ :=
  CenteredMomentCommonMaskExpansion.naturalSlot
    (CenteredMomentNaturalRowSource.naturalRow
      (CenteredMomentNaturalRowSource.excluded η
        (OAI.SevenEighths.Record12518109Natural.wholeAnchorMask rayM H hH η₀))
      u.val u.property.1).character
    (primePool rayM H 2 (U^(wr s)))
    (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ s)) I *
      HeckePrimeAnnular.annularWeight W (U^(wr s)) (σ s) (t u + v s) I) (U^(wr s))

/-- The regular cores of the fixed dictionary of `η`. -/
def RegularCore (η η₀ : Character) (u : FreeRow) : Prop :=
  ¬ (OAI.SevenEighths.Record12518109GainWholeGeometry.wholeRegularDictionary rayM H hH η η₀).exceptionalCore u

end Core

/-- **The MARKED fields of the HIGH detector fibers on core batches** (from the earlier anchors,
`High.Sources.high_child_sources` / `EarlierAnchors`, transported to the core fibers). Line
`(a0, a1)`, cutoff floor `wlo` (the witness widths must exceed the current stage:
`wlo = R n + 10^-6`, see `High.PriceFloor`).

Quantifiers, in order:
* the moment loss `εm > 0`; then a slot mesh `meshm > 0` (the anchors' `∃ mesh` after `ε`; the
  anchors are uniform in all data, so `meshm` precedes the data);
* the data: ray modulus, subgroup, slot profile `W`, the state character `η` (an anchor) and `η₀`;
* the slot type `Slot` (its cardinality is the anchors' `K`) and a width floor `wrmin > 0`;
* then `J, C`, and eventually in the scale `U`:
  every zero level `a`, detector loss `ε`, height data, every slot configuration (relative widths
  `wrmin ≤ wr ≤ meshm`, `σ = 33/50`), every set of regular cores of norm `≤ U`, every cutoff
  `wc ∈ cutoffs` with `wlo ≤ wc`, every witness function of the core family at
  `tstar = 3 wc/2 + 10^-6`, and every fiber of it (`label, J', K'` constant on the rows):
  the `inverseMarked` and `plainMarked` fields of `AnchorFiberMoments`, with any `C' ≥ C (1+height)^J`.
-/
def HighMarkedCoreInputs (a0 a1 wlo : ℝ) : Prop :=
  ∀ (εm : ℝ), 0 < εm → ∃ meshm : ℝ, 0 < meshm ∧
  ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), Function.support W ⊆ Set.Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
    ∀ (η η₀ : Character) {Slot : Type} [Fintype Slot] [DecidableEq Slot] (wrmin : ℝ), 0 < wrmin →
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (a ε Tz allowance height : ℝ) (i : ℕ),
      1/2 ≤ a → 0 ≤ ε → ε ≤ 1/1000 → 0 ≤ height →
      2*Real.pi*allowance+(3*i : ℕ)*Tz ≤ height →
      ∀ (slots : Finset Slot) (θ : Slot → RayQuotient.Characters rayM H) (wr σ v : Slot → ℝ)
        (t : FreeRow → ℝ),
      (∀ s ∈ slots, wrmin ≤ wr s) → (∀ s ∈ slots, wr s ≤ meshm) →
      (∀ s ∈ slots, σ s = 33/50) →
      ∀ (rows : Finset FreeRow), (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      (∀ u ∈ rows, RegularCore rayM H hH η η₀ u) →
      ∀ (wc : ℝ), wc ∈ cutoffs → wlo ≤ wc →
      ∀ (wit : ∀ u, SupportedWitness (coreFamily rayM H hH η η₀ u) U a ε (3*wc/2+1/1000000)
          Tz allowance i)
        (label : WholeSourceIndex rayM H) (J' K' : Fin (dyadicLength U)),
      (∀ u ∈ rows, (wit u).label = label ∧ (wit u).left = J' ∧ (wit u).right = K') →
      ∀ C' : ℝ, C * (1+height)^J ≤ C' →
      -- `inverseMarked`
      (wc ≤ Real.logb U ((2 : ℝ)^J'.val) → Real.logb U ((2 : ℝ)^J'.val) < 1 →
        ∀ selected : Finset Slot, selected ⊆ slots →
          (∑ s ∈ selected, wr s) ≤ selW a0 a1 (∑ s ∈ slots, wr s) (Real.logb U ((2 : ℝ)^J'.val)) →
        ∀ n : ℕ, n ≤ 2 → ∀ σ' ∈ Set.Icc (0 : ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
        ∑ u ∈ rows, ‖polynomial (coreFamily rayM H hH η η₀ u label) true
          ((HeckeDetectorRowwisePolynomial.logProfile^[n])
            (HeckeDetectorInverseFiberCount.inverseTest U (3*wc/2+1/1000000)
              (Real.logb U ((2 : ℝ)^J'.val))))
          (U^(Real.logb U ((2 : ℝ)^J'.val))) σ' freq *
          (∏ s ∈ selected, coreSlot rayM H hH η η₀ W U θ wr σ v t u s)‖^2 ≤ C' * U^(1+εm)) ∧
      -- `plainMarked`
      (wc ≤ 2*Real.logb U ((2 : ℝ)^K'.val) → 2*Real.logb U ((2 : ℝ)^K'.val) < 1 →
        ∀ selected : Finset Slot, selected ⊆ slots →
          (∑ s ∈ selected, wr s) ≤
            selW a0 a1 (∑ s ∈ slots, wr s) (2*Real.logb U ((2 : ℝ)^K'.val)) →
        ∀ j k : ℕ, j+k ≤ 2 → ∀ σ' ∈ Set.Icc (0 : ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
        ∑ u ∈ rows, ‖polynomial (coreFamily rayM H hH η η₀ u label) false
          ((HeckeDetectorRowwisePolynomial.logProfile^[j]) HeckeDetectorDyadicProfiles.positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K'.val))) σ' freq *
          polynomial (coreFamily rayM H hH η η₀ u label) false
          ((HeckeDetectorRowwisePolynomial.logProfile^[k]) HeckeDetectorDyadicProfiles.positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K'.val))) σ' freq *
          (∏ s ∈ selected, coreSlot rayM H hH η η₀ W U θ wr σ v t u s)‖^2 ≤ C' * U^(1+εm))

/-- **The per-fiber inputs of the HIGH detector count on core batches.** Same quantifiers as `HighMarkedCoreInputs`; the conclusion is the whole
`AnchorFiberMoments` of the fiber. Proved from `HighMarkedCoreInputs` in `High.CoreInputs`
(the unmarked fields are `Cofactor.core_unmarked_fields` for `wholeRegularDictionary`). -/
def HighCoreFiberInputs (a0 a1 wlo : ℝ) : Prop :=
  ∀ (εm : ℝ), 0 < εm → ∃ meshm : ℝ, 0 < meshm ∧
  ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), Function.support W ⊆ Set.Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
    ∀ (η η₀ : Character) {Slot : Type} [Fintype Slot] [DecidableEq Slot] (wrmin : ℝ), 0 < wrmin →
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (a ε Tz allowance height : ℝ) (i : ℕ),
      1/2 ≤ a → 0 ≤ ε → ε ≤ 1/1000 → 0 ≤ height →
      2*Real.pi*allowance+(3*i : ℕ)*Tz ≤ height →
      ∀ (slots : Finset Slot) (θ : Slot → RayQuotient.Characters rayM H) (wr σ v : Slot → ℝ)
        (t : FreeRow → ℝ),
      (∀ s ∈ slots, wrmin ≤ wr s) → (∀ s ∈ slots, wr s ≤ meshm) →
      (∀ s ∈ slots, σ s = 33/50) →
      ∀ (rows : Finset FreeRow), (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      (∀ u ∈ rows, RegularCore rayM H hH η η₀ u) →
      ∀ (wc : ℝ), wc ∈ cutoffs → wlo ≤ wc →
      ∀ (wit : ∀ u, SupportedWitness (coreFamily rayM H hH η η₀ u) U a ε (3*wc/2+1/1000000)
          Tz allowance i)
        (label : WholeSourceIndex rayM H) (J' K' : Fin (dyadicLength U)),
      (∀ u ∈ rows, (wit u).label = label ∧ (wit u).left = J' ∧ (wit u).right = K') →
      ∀ C' : ℝ, C * (1+height)^J ≤ C' →
      AnchorFiberMoments rows slots (coreFamily rayM H hH η η₀)
        (coreSlot rayM H hH η η₀ W U θ wr σ v t) wr U a ε (3*wc/2+1/1000000) a0 a1 wc εm C'
        height label J' K'

end
end Qrh.MarkedAnchor.High
