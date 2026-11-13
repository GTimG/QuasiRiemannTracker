/- Modified by Joseph Bebel (2026-11-12): positive source and detector
pads for the stronger anchor target. The actual physical coefficient,
mask and height contracts are preserved. Inherited attribution follows. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Adapted from Hailey Collet's `Record1252270103Source/High/ActualWeighted.lean`
(`ordinary_actual_weighted_row_sum`, the `UnmarkedBatch` block, Apache-2.0): the unmarked gates
`actual_unmarked_fiber_gates` are delivered as the two unmarked fields of
`AnchorFiberMoments` for any witness fiber of sixth-free (core) rows. -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Weighted
import Submissions.hailey_collet_1252270103.Record12518109Gain.ActualUnmarkedGates

/-!
# High.Cofactor.Unmarked

The native part of the core inputs: the unmarked inverse count and the unmarked ordinary
moment of a detector fiber of SIXTH-FREE rows (`FreeRow`, the cores of `High.Cofactor.Lift`).

`core_unmarked_fields`: for a fixed dictionary `D` (HC `FixedUnmarkedDictionary`, chosen before the
scale) there are `J, C` and eventually in `U`: for every legal `a, ε, tstar ∈ [1, 3/2], height`,
every finite set of free rows of norm `≤ U` whose family has the (possibly conjugated) coefficients of
`D.data`, and every witness function whose label / dyadic widths are constant (`label, J', K'`) on
the set, the `inverseUnmarked` and `plainUnmarked` fields of `AnchorFiberMoments` hold with any
constant `C' ≥ C (1+height)^J`.

`anchorFiberMoments_of_core` packages them with the two marked fields.

The witness hypothesis is necessary: `inverseUnmarked` is a count, false for arbitrary sets.
Raw (non-sixth-free) rows cannot carry `plainUnmarked` at one scale (one core repeats for every
sixth-power cofactor); they are reduced to cores by `High.Cofactor.Lift`.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Cofactor
noncomputable section
open scoped Classical BigOperators
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open HeckeDetectorWitnessRows HeckeDetectorInverseFiberCount HeckeDetectorRawFiber
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles HeckeDyadic
open LocalMoment
local notation "O" => HeckeFamily.O

/-- **The unmarked fields on core fibers.** -/
theorem core_unmarked_fields {Label : Type*} [Fintype Label]
    (D : FixedUnmarkedDictionary Label) (setup : DensityCountingSetup)
    (εm : ℝ) (hεm : 0 < εm) (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (a ε tstar T allowance height : ℝ) (i : ℕ),
      1/2 ≤ a → 0 ≤ ε → ε ≤ 1/1000 → 1 ≤ tstar → tstar ≤ 3/2 →
      0 ≤ height → 2*Real.pi*allowance+(3*i : ℕ)*T ≤ height →
      ∀ (rows : Finset FreeRow) (χ : FreeRow → Label → Character) (reverse : Label → Bool),
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      (∀ u ∈ rows, ∀ j, ∀ I : Ideal O, idealCoeff (χ u j) I =
        if reverse j then starRingEnd ℂ (idealCoeff ((D.data j).character ⟨u.val, u.property.1⟩) I)
        else idealCoeff ((D.data j).character ⟨u.val, u.property.1⟩) I) →
      ∀ (wit : ∀ u, SupportedWitness (χ u) U a ε tstar T allowance i) (label : Label)
        (J' K' : Fin (dyadicLength U)),
      (∀ u ∈ rows, (wit u).label = label ∧ (wit u).left = J' ∧ (wit u).right = K') →
      ∀ C' : ℝ, C * (1+height)^J ≤ C' →
      ((rows.card : ℝ) ≤ (192*(1+height)*C') *
        U^(max 1 ((1+5*Real.logb U ((2 : ℝ)^J'.val))/6) -
          (2*a-1)*Real.logb U ((2 : ℝ)^J'.val) + 2*ε + εm)) ∧
      (∀ j k : ℕ, j+k ≤ 2 → ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
        ∑ u ∈ rows, ‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K'.val))) σ freq *
          polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K'.val))) σ freq‖^2 ≤
            C' * U^(max 1 (2*Real.logb U ((2 : ℝ)^K'.val)) + εm)) := by
  obtain ⟨J, C, hC, hU⟩ :=
    Record12518109GainActualUnmarked.actual_unmarked_fiber_gates D setup εm hεm hβ
  refine ⟨J, C, hC, ?_⟩
  filter_upwards [hU] with U hU
  refine ⟨hU.1, ?_⟩
  intro a ε tstar T allowance height i ha hε hε' ht ht' hh hf rows χ reverse hnorm hcoeff wit
    label J' K' hfib C' hC'
  have hU0 : 0 < U := zero_lt_one.trans hU.1
  by_cases hne : rows.Nonempty
  · let ub : UnmarkedBatch Label U a ε tstar T allowance i :=
      { rows := rows
        family := χ
        witness := wit
        row_norm := hnorm
        data := D.data
        reverse := reverse
        row_coeff := hcoeff }
    have huf : ub.fiberRows label J' K' = rows := by
      apply Finset.filter_eq_self.mpr
      intro u hu
      exact hfib u hu
    have hune : (ub.fiberRows label J' K').Nonempty := huf.symm ▸ hne
    have hu := hU.2 a ε tstar T allowance height i ha hε hε' ht ht' hh hf ub rfl label J' K' hune
    dsimp only [UnmarkedBatch.fiber, UnmarkedFiber.r, UnmarkedFiber.m] at hu
    rw [huf] at hu
    refine ⟨hu.1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hC' (by positivity)) (Real.rpow_nonneg hU0.le _)), ?_⟩
    intro j k hjk σ hσ freq hfreq
    exact (hu.2 j k hjk σ hσ freq hfreq).trans
      (mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hU0.le _))
  · have he : rows = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst he
    have hC'0 : 0 ≤ C' := le_trans (by positivity) hC'
    refine ⟨?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg hU0.le _)
    · intro j k _ σ _ freq _
      simp only [Finset.sum_empty]
      exact mul_nonneg hC'0 (Real.rpow_nonneg hU0.le _)

/-- `AnchorFiberMoments` of a core fiber from its four fields (the unmarked ones as supplied by
`core_unmarked_fields`). -/
theorem anchorFiberMoments_of_core {Label Slot : Type*} (rows : Finset FreeRow)
    (slots : Finset Slot) (χ : FreeRow → Label → Character) (Q : FreeRow → Slot → ℂ)
    (widths : Slot → ℝ) (U a ε tstar a0 a1 w εm C height : ℝ) (label : Label)
    (J' K' : Fin (dyadicLength U))
    (hI0 : (rows.card : ℝ) ≤ (192*(1+height)*C) *
        U^(max 1 ((1+5*Real.logb U ((2 : ℝ)^J'.val))/6) -
          (2*a-1)*Real.logb U ((2 : ℝ)^J'.val) + 2*ε + εm))
    (hP0 : ∀ j k : ℕ, j+k ≤ 2 → ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
        ∑ u ∈ rows, ‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K'.val))) σ freq *
          polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K'.val))) σ freq‖^2 ≤
            C * U^(max 1 (2*Real.logb U ((2 : ℝ)^K'.val)) + εm))
    (hI : w ≤ Real.logb U ((2 : ℝ)^J'.val) → Real.logb U ((2 : ℝ)^J'.val) < 1 →
      ∀ selected : Finset Slot, selected ⊆ slots →
        (∑ s ∈ selected, widths s) ≤
          selW a0 a1 (∑ s ∈ slots, widths s) (Real.logb U ((2 : ℝ)^J'.val)) →
      ∀ n : ℕ, n ≤ 2 → ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
      ∑ u ∈ rows, ‖polynomial (χ u label) true
        ((logProfile^[n]) (inverseTest U tstar (Real.logb U ((2 : ℝ)^J'.val))))
        (U^(Real.logb U ((2 : ℝ)^J'.val))) σ freq * (∏ s ∈ selected, Q u s)‖^2 ≤ C*U^(1+εm))
    (hP : w ≤ 2*Real.logb U ((2 : ℝ)^K'.val) → 2*Real.logb U ((2 : ℝ)^K'.val) < 1 →
      ∀ selected : Finset Slot, selected ⊆ slots →
        (∑ s ∈ selected, widths s) ≤
          selW a0 a1 (∑ s ∈ slots, widths s) (2*Real.logb U ((2 : ℝ)^K'.val)) →
      ∀ j k : ℕ, j+k ≤ 2 → ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
      ∑ u ∈ rows, ‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
        (U^(Real.logb U ((2 : ℝ)^K'.val))) σ freq *
        polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
        (U^(Real.logb U ((2 : ℝ)^K'.val))) σ freq * (∏ s ∈ selected, Q u s)‖^2 ≤ C*U^(1+εm)) :
    AnchorFiberMoments rows slots χ Q widths U a ε tstar a0 a1 w εm C height label J' K' :=
  ⟨hI0, hP0, hI, hP⟩

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Cofactor
