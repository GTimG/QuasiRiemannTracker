/- Modified by Joseph Bebel (2026-11-12): actual source adapters for the
smaller-tolerance HIGH contract; original notices follow. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.LeafInputs

/-!
# High.Marked.Contract

The provable form of `High.HighMarkedCoreInputs`: the marked fields of the HIGH detector fibers on
core batches, with bounded slot and row heights, `|v s| ≤ height`, `|t u| ≤ height` (without them
the statement is false: the rows may align the slot phases). No separation of the slot widths is
required: the inverse anchor contract admits overlapping canonical pools.
Everything else is verbatim `HighMarkedCoreInputs`. The two fields are named
(`InvMarkedField`, `PlainMarkedField`) so that they can be proved separately; unfolded they are
literally the `inverseMarked` / `plainMarked` fields of `AnchorFiberMoments`.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Marked
noncomputable section
open scoped Classical BigOperators ContDiff
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
open Qrh.TwoSlot.AnchorZeroLoss.High
local notation "O" => HeckeFamily.O
local instance markedContractQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

section Fields
variable (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
  (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- The `inverseMarked` field of `AnchorFiberMoments` on a core fiber. -/
def InvMarkedField (η η₀ : Character) (W : ℝ → ℂ) {Slot : Type} [Fintype Slot] [DecidableEq Slot]
    (U a0 a1 wc tstar height εm C' : ℝ) (slots : Finset Slot)
    (θ : Slot → RayQuotient.Characters rayM H) (wr σ v : Slot → ℝ) (t : FreeRow → ℝ)
    (rows : Finset FreeRow) (label : WholeSourceIndex rayM H) (J' : Fin (dyadicLength U)) (pad : ℝ := 1/10000000000000) : Prop :=
  wc ≤ Real.logb U ((2 : ℝ)^J'.val) → Real.logb U ((2 : ℝ)^J'.val) < 1 →
    ∀ selected : Finset Slot, selected ⊆ slots →
      (∑ s ∈ selected, wr s) ≤ min (max 0 ((1-Real.logb U ((2 : ℝ)^J'.val))/2 + (a0-a1*Real.logb U ((2 : ℝ)^J'.val))-pad)) (∑ s ∈ slots, wr s) →
    ∀ n : ℕ, n ≤ 2 → ∀ σ' ∈ Set.Icc (0 : ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
    ∑ u ∈ rows, ‖polynomial (coreFamily rayM H hH η η₀ u label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n])
        (HeckeDetectorInverseFiberCount.inverseTest U tstar
          (Real.logb U ((2 : ℝ)^J'.val))))
      (U^(Real.logb U ((2 : ℝ)^J'.val))) σ' freq *
      (∏ s ∈ selected, coreSlot rayM H hH η η₀ W U θ wr σ v t u s)‖^2 ≤ C' * U^(1+εm)

/-- The `plainMarked` field of `AnchorFiberMoments` on a core fiber. -/
def PlainMarkedField (η η₀ : Character) (W : ℝ → ℂ) {Slot : Type} [Fintype Slot]
    [DecidableEq Slot]
    (U a0 a1 wc height εm C' : ℝ) (slots : Finset Slot)
    (θ : Slot → RayQuotient.Characters rayM H) (wr σ v : Slot → ℝ) (t : FreeRow → ℝ)
    (rows : Finset FreeRow) (label : WholeSourceIndex rayM H) (K' : Fin (dyadicLength U)) (pad : ℝ := 1/10000000000000) : Prop :=
  wc ≤ 2*Real.logb U ((2 : ℝ)^K'.val) → 2*Real.logb U ((2 : ℝ)^K'.val) < 1 →
    ∀ selected : Finset Slot, selected ⊆ slots →
      (∑ s ∈ selected, wr s) ≤
        min (max 0 ((1-2*Real.logb U ((2 : ℝ)^K'.val))/2 + (a0-a1*(2*Real.logb U ((2 : ℝ)^K'.val)))-pad)) (∑ s ∈ slots, wr s) →
    ∀ j k : ℕ, j+k ≤ 2 → ∀ σ' ∈ Set.Icc (0 : ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
    ∑ u ∈ rows, ‖polynomial (coreFamily rayM H hH η η₀ u label) false
      ((HeckeDetectorRowwisePolynomial.logProfile^[j]) HeckeDetectorDyadicProfiles.positiveAnnular)
      (U^(Real.logb U ((2 : ℝ)^K'.val))) σ' freq *
      polynomial (coreFamily rayM H hH η η₀ u label) false
      ((HeckeDetectorRowwisePolynomial.logProfile^[k]) HeckeDetectorDyadicProfiles.positiveAnnular)
      (U^(Real.logb U ((2 : ℝ)^K'.val))) σ' freq *
      (∏ s ∈ selected, coreSlot rayM H hH η η₀ W U θ wr σ v t u s)‖^2 ≤ C' * U^(1+εm)

end Fields

/-- **Marked core inputs, witness-free form**: `HighMarkedCoreInputsR` without the witness (the
marked fields only see its label and dyadic indices, so every `label J' K'` is quantified), plus
bounded heights (`≤ height`); no slot separation. -/
def MarkedCoreR1 (a0 a1 wlo : ℝ)
    (pad : ℝ := 1/10000000000000) (shift : ℝ := 1/1000000000000) : Prop :=
  ∀ (εm : ℝ), 0 < εm → ∃ meshm : ℝ, 0 < meshm ∧
  ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ), Function.support W ⊆ Set.Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
    ∀ (η η₀ : Character) {Slot : Type} [Fintype Slot] [DecidableEq Slot] (wrmin : ℝ), 0 < wrmin →
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (height : ℝ), 0 ≤ height →
      ∀ (slots : Finset Slot) (θ : Slot → RayQuotient.Characters rayM H) (wr σ v : Slot → ℝ)
        (t : FreeRow → ℝ),
      (∀ s ∈ slots, wrmin ≤ wr s) → (∀ s ∈ slots, wr s ≤ meshm) →
      (∀ s ∈ slots, σ s = 33/50) →
      (∀ s ∈ slots, |v s| ≤ height) →
      ∀ (rows : Finset FreeRow), (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      (∀ u ∈ rows, RegularCore rayM H hH η η₀ u) →
      (∀ u ∈ rows, |t u| ≤ height) →
      ∀ (wc : ℝ), wc ∈ cutoffs → wlo ≤ wc →
      ∀ (label : WholeSourceIndex rayM H) (J' K' : Fin (dyadicLength U)),
      ∀ C' : ℝ, C * (1+height)^J ≤ C' →
      InvMarkedField rayM H hH η η₀ W U a0 a1 wc (3*wc/2+shift) height εm C' slots θ wr σ v t
        rows label J' pad ∧
      PlainMarkedField rayM H hH η η₀ W U a0 a1 wc height εm C' slots θ wr σ v t rows label K' pad

/-- **Marked core inputs in the consumer's form**: `HighMarkedCoreInputsR` (witness on the rows)
plus bounded slot and row heights; no slot separation. -/
def HighMarkedCoreInputsR1 (a0 a1 wlo : ℝ)
    (pad : ℝ := 1/10000000000000) (shift : ℝ := 1/1000000000000) : Prop :=
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
      (∀ s ∈ slots, |v s| ≤ height) →
      ∀ (rows : Finset FreeRow), (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      (∀ u ∈ rows, RegularCore rayM H hH η η₀ u) →
      (∀ u ∈ rows, |t u| ≤ height) →
      ∀ (wc : ℝ), wc ∈ cutoffs → wlo ≤ wc →
      ∀ (wit : ∀ u ∈ rows, SupportedWitness (coreFamily rayM H hH η η₀ u) U a ε
          (3*wc/2+shift) Tz allowance i)
        (label : WholeSourceIndex rayM H) (J' K' : Fin (dyadicLength U)),
      (∀ u (hu : u ∈ rows), (wit u hu).label = label ∧ (wit u hu).left = J' ∧
        (wit u hu).right = K') →
      ∀ C' : ℝ, C * (1+height)^J ≤ C' →
      InvMarkedField rayM H hH η η₀ W U a0 a1 wc (3*wc/2+shift) height εm C' slots θ wr σ v t
        rows label J' pad ∧
      PlainMarkedField rayM H hH η η₀ W U a0 a1 wc height εm C' slots θ wr σ v t rows label K' pad

/-- The witness-free form gives the consumer's form. -/
theorem r1_of_marked_with_tolerances {a0 a1 wlo pad shift : ℝ}
    (h : MarkedCoreR1 a0 a1 wlo pad shift) :
    HighMarkedCoreInputsR1 a0 a1 wlo pad shift := by
  intro εm hεm
  obtain ⟨meshm, hm, h'⟩ := h εm hεm
  refine ⟨meshm, hm, ?_⟩
  intro rayM _ H hH W hWs hW η η₀ Slot _ _ wrmin hwrmin
  obtain ⟨J, C, hC, hev⟩ := h' rayM H hH W hWs hW η η₀ (Slot := Slot) wrmin hwrmin
  refine ⟨J, C, hC, hev.mono fun U hU => ⟨hU.1, ?_⟩⟩
  intro a ε Tz allowance height i _ _ _ hh _ slots θ wr σ v t hwmin hwm hσ hv rows hnorm
    hreg ht wc hwc hwlo _ label J' K' _ C' hC'
  exact hU.2 height hh slots θ wr σ v t hwmin hwm hσ hv rows hnorm hreg ht wc hwc hwlo
    label J' K' C' hC'

theorem r1_of_marked {a0 a1 wlo : ℝ} (h : MarkedCoreR1 a0 a1 wlo) :
    HighMarkedCoreInputsR1 a0 a1 wlo :=
  r1_of_marked_with_tolerances h

/-- The form `HighMarkedCoreInputsR` without height bounds implies the bounded-height one: the
height bounds only add hypotheses. -/
theorem r1_of_R {a0 a1 wlo : ℝ} (h : HighMarkedCoreInputsR a0 a1 wlo) :
    HighMarkedCoreInputsR1 a0 a1 wlo := by
  intro εm hεm
  obtain ⟨meshm, hm, h'⟩ := h εm hεm
  refine ⟨meshm, hm, ?_⟩
  intro rayM _ H hH W hWs hW η η₀ Slot _ _ wrmin hwrmin
  obtain ⟨J, C, hC, hev⟩ := h' rayM H hH W hWs hW η η₀ (Slot := Slot) wrmin hwrmin
  refine ⟨J, C, hC, hev.mono fun U hU => ⟨hU.1, ?_⟩⟩
  intro a ε Tz allowance height i ha hε0 hε1 hh hf slots θ wr σ v t hwmin hwm hσ _ rows hnorm
    hreg _ wc hwc hwlo wit label J' K' hfib C' hC'
  exact hU.2 a ε Tz allowance height i ha hε0 hε1 hh hf slots θ wr σ v t hwmin hwm hσ rows hnorm
    hreg wc hwc hwlo wit label J' K' hfib C' hC'

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Marked
