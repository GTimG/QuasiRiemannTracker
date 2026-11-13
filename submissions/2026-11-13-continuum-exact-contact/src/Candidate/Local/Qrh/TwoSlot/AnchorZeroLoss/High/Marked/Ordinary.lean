/- Modified by Joseph Bebel (2026-11-12): actual source adapters for the
smaller-tolerance HIGH contract; original notices follow. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Uses Hailey Collet's `ordinary_rowwise_plain_fixedmesh`, `whole_family_common_slot`,
`whole_regular_retained` (Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.Marked.Contract
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.RowwisePlain

/-!
# High.Marked.Ordinary

The ordinary (squared plain) marked moment on core fibers from ONE unit-face ordinary source
`UnitFaceSource ⟨B, lam, 0, B, 0, h⟩` (an anchor's `OrdinaryRectSource` with `lam = 0`, or a
global source `G(B, L, c)`):

`core_plain_of_face`: for every label of the fixed dictionary `wholeRegularDictionary` of the
state character, every finite set of regular cores of norm `≤ U`, every selection with
`∑ wr ≤ h`, `2m + lam ∑ wr ≤ B`, the plain marked moment with the literal `coreSlot`s is
`≤ C (1+height)^J U^(1+εm)`, slot widths `≤ mesh` (the source's mesh), heights `≤ height`.

The slot identity is HC's `whole_family_common_slot` (the core slot is the natural slot of the
label's own character with the label's anchor), the keep predicate is HC's
`whole_regular_retained`.
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High.Marked
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot CenteredMomentDetectorEnergyInitialState
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles Cycle61Moment
open CenteredMomentDetectorPlainFiberSource
open Qrh.TwoSlot.AnchorZeroLoss.High
local notation "O" => HeckeFamily.O
local instance markedOrdinaryQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- A support bound `≥ 2` for the radial majorant. -/
theorem radial_bound : ∃ bΦ : ℝ, 2 ≤ bΦ ∧
    Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bΦ := by
  obtain ⟨b, -, hb⟩ := radialMajorant_support_bound
  exact ⟨max 2 b, le_max_left _ _, hb.trans (Set.Iic_subset_Iic.mpr (le_max_right _ _))⟩

/-- The core slot is the label's natural slot (HC `whole_family_common_slot`). -/
theorem coreSlot_eq_label (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (η η₀ : Character) {Slot : Type}
    (W : ℝ → ℂ) (U : ℝ) (θ : Slot → RayQuotient.Characters rayM H) (wr σ v : Slot → ℝ)
    (t : FreeRow → ℝ) (u : FreeRow) (s : Slot) (label : WholeSourceIndex rayM H) :
    coreSlot rayM H hH η η₀ W U θ wr σ v t u s =
      naturalSlot (coreFamily rayM H hH η η₀ u label) (primePool rayM H 2 (U^(wr s)))
        (fun I => idealCoeff (relativeCharacter rayM H hH
          (Record12518109Natural.wholeSourceAnchor rayM H hH η₀ label) (θ s)) I *
          HeckePrimeAnnular.annularWeight W (U^(wr s)) (σ s) (t u + v s) I) (U^(wr s)) :=
  (Record12518109Natural.whole_family_common_slot rayM H hH η η₀ u.val u.property.1 label (θ s)
    (primePool rayM H 2 (U^(wr s)))
    (fun I => HeckePrimeAnnular.annularWeight W (U^(wr s)) (σ s) (t u + v s) I) (U^(wr s))).symm

/-- **Plain marked moment on core fibers from one ordinary unit-face source.** -/
theorem core_plain_of_face (B lam h meshS εm : ℝ) (hlam : 0 ≤ lam) (hεm : 0 < εm)
    (hsrc : QRH.Record12518109Existence.UnitFaceSource ⟨B, lam, 0, B, 0, h⟩ meshS εm)
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (η η₀ : Character) (Slot : Type) [Fintype Slot] [DecidableEq Slot] :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (label : WholeSourceIndex rayM H) (rows : Finset FreeRow),
      (∀ u ∈ rows, RegularCore rayM H hH η η₀ u) →
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      ∀ (m : ℝ), 0 ≤ m → m ≤ 1 →
      ∀ (selected : Finset Slot) (θ : Slot → RayQuotient.Characters rayM H) (wr σ v : Slot → ℝ)
        (t : FreeRow → ℝ) (height : ℝ),
      (∀ s ∈ selected, 0 ≤ wr s) → (∀ s ∈ selected, wr s ≤ meshS) →
      (∀ s ∈ selected, σ s = 33/50) → 0 ≤ height → (∀ s ∈ selected, |v s| ≤ height) →
      (∀ u ∈ rows, |t u| ≤ height) →
      (∑ s ∈ selected, wr s) ≤ h → 2*m + lam*(∑ s ∈ selected, wr s) ≤ B →
      ∀ j k : ℕ, j+k ≤ 2 → ∀ σ' ∈ Set.Icc (0:ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
      ∑ u ∈ rows, ‖polynomial (coreFamily rayM H hH η η₀ u label) false
          ((logProfile^[j]) positiveAnnular) (U^m) σ' freq *
        polynomial (coreFamily rayM H hH η η₀ u label) false
          ((logProfile^[k]) positiveAnnular) (U^m) σ' freq *
        (∏ s ∈ selected, coreSlot rayM H hH η η₀ W U θ wr σ v t u s)‖^2 ≤
        C*(1+height)^J*U^(1+εm) := by
  obtain ⟨bΦ, hbΦ, hrad⟩ := radial_bound
  have hP (label : WholeSourceIndex rayM H) := QRH.Record1252270103Source.High.ordinary_rowwise_plain_fixedmesh
    (α := Slot) rayM H hH B lam h meshS εm hlam hsrc W bΦ hWs hW hbΦ hrad
    (Record12518109Natural.cleanWholeBase rayM H hH η η₀ label)
    (Record12518109Natural.wholeSourceAnchor rayM H hH η₀ label)
    (Record12518109GainWholeGeometry.wholeRegularBad rayM H hH η η₀ label)
    (inf_le_left.trans inf_le_left)
    ((Record12518109GainWholeGeometry.wholeRegularDictionary rayM H hH η η₀).nonzero label)
    ((Record12518109GainWholeGeometry.wholeRegularDictionary rayM H hH η η₀).proper label)
    ((Record12518109GainWholeGeometry.wholeRegularDictionary rayM H hH η η₀).divides72 label)
  choose Jl Cl hCl hev using hP
  have hCs : 0 ≤ ∑ l, Cl l := Finset.sum_nonneg (fun l _ => (hCl l).le)
  refine ⟨∑ l, Jl l, 1 + ∑ l, Cl l, by linarith, ?_⟩
  filter_upwards [eventually_all.mpr hev, eventually_gt_atTop (1:ℝ)] with U hU hU1
  refine ⟨hU1, ?_⟩
  intro label rows hreg hnorm m hm hm1 selected θ wr σ v t height hw hwm hσ hh hv ht hsum hcap
    j k hjk σ' hσ' freq hfreq
  have hkeep : ∀ u ∈ rows, initialKeep (Record12518109Natural.cleanWholeBase rayM H hH η η₀ label)
      (internalQ (Record12518109GainWholeGeometry.wholeRegularBad rayM H hH η η₀ label)
        (Record12518109Natural.wholeSourceAnchor rayM H hH η₀ label)) u.val := by
    intro u hu
    exact Record12518109GainWholeGeometry.whole_regular_retained rayM H hH η η₀ rows u
      (Finset.mem_filter.mpr ⟨hu, hreg u hu⟩) label
  have he := (hU label).2 rows (fun u : FreeRow => u.val) Subtype.val_injective
    (fun u => coreFamily rayM H hH η η₀ u label)
    (fun u _ n => Record12518109Natural.natural_initial_element _ u.val u.property.1 n)
    hkeep
    (fun u hu => by
      rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      exact hnorm u hu)
    m hm hm1 selected (fun s => θ s.val) (fun s => wr s.val) (fun s => σ s.val)
    (fun s => v s.val) height t (fun s => hw s.val s.property) (fun s => hwm s.val s.property)
    (fun s => (hσ s.val s.property).ge) (fun s => (hσ s.val s.property).le) hh
    (fun s => hv s.val s.property) ht
    (by simpa only [Finset.sum_coe_sort] using hsum)
    (by simpa only [Finset.sum_coe_sort] using hcap) j k hjk σ' hσ' freq (abs_le.mpr hfreq)
  have heq : ∀ u ∈ rows, (∏ s ∈ selected, coreSlot rayM H hH η η₀ W U θ wr σ v t u s) =
      ∏ s : selected, naturalSlot (coreFamily rayM H hH η η₀ u label)
        (primePool rayM H 2 (U^(wr s.val)))
        (fun I => idealCoeff (relativeCharacter rayM H hH
          (Record12518109Natural.wholeSourceAnchor rayM H hH η₀ label) (θ s.val)) I *
          HeckePrimeAnnular.annularWeight W (U^(wr s.val)) (σ s.val) (t u + v s.val) I)
        (U^(wr s.val)) := by
    intro u _
    rw [← Finset.prod_coe_sort selected]
    exact Finset.prod_congr rfl (fun s _ => coreSlot_eq_label rayM H hH η η₀ W U θ wr σ v t u
      s.val label)
  rw [Finset.sum_congr rfl (fun u hu => by rw [heq u hu])]
  refine he.trans ?_
  have hJ : Jl label ≤ ∑ l, Jl l :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ label)
  have hC : Cl label ≤ 1 + ∑ l, Cl l := by
    have := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => (hCl l).le) (Finset.mem_univ label)
    linarith
  have h1 : (1:ℝ) ≤ 1 + height := by linarith
  have hUp : 0 ≤ U^(1+εm) := Real.rpow_nonneg (by linarith) _
  apply mul_le_mul_of_nonneg_right _ hUp
  exact mul_le_mul hC (pow_le_pow_right₀ h1 hJ) (by positivity) (by positivity)

end
end Qrh.TwoSlot.AnchorZeroLoss.High.Marked
