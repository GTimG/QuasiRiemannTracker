/- Copyright (c) 2026 Sil. Apache-2.0.
Uses Hailey Collet's `actual_rowwise_marked_plain_energy_fixedmesh` (Apache-2.0). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Marked.Ordinary
import Submissions.hailey_collet_1252270103.Record12518109Gain.Upstream.ActualRowwiseMarkedPlain

/-!
# High.Marked.PlainEmpty

`core_plain_empty`: the squared ordinary moment of core fibers WITHOUT slots, for every
`2m ≤ 1` (HC's native rowwise plain energy with an empty slot set; needs `51/100 ≤ β`). Used for
the empty selection of the plain marked field near `2m = 1`, where no ordinary source face reaches.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Marked
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot CenteredMomentDetectorEnergyInitialState
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles Cycle61Moment
open CenteredMomentDetectorPlainFiberSource
open Qrh.MarkedAnchor.High
local notation "O" => HeckeFamily.O
local instance markedPlainEmptyQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- **Unmarked squared ordinary moment on core fibers, `2m ≤ 1`.** -/
theorem core_plain_empty (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) (εm : ℝ) (hεm : 0 < εm)
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (η η₀ : Character) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (label : WholeSourceIndex rayM H) (rows : Finset FreeRow),
      (∀ u ∈ rows, RegularCore rayM H hH η η₀ u) →
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      ∀ (m : ℝ), 0 ≤ m → 2*m ≤ 1 → ∀ (height : ℝ), 0 ≤ height →
      ∀ j k : ℕ, j+k ≤ 2 → ∀ σ' ∈ Set.Icc (0:ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
      ∑ u ∈ rows, ‖polynomial (coreFamily rayM H hH η η₀ u label) false
          ((logProfile^[j]) positiveAnnular) (U^m) σ' freq *
        polynomial (coreFamily rayM H hH η η₀ u label) false
          ((logProfile^[k]) positiveAnnular) (U^m) σ' freq‖^2 ≤
        C*(1+height)^J*U^(1+εm) := by
  obtain ⟨bΦ, hbΦ, hrad⟩ := radial_bound
  have hκ : (3/4:ℝ) ≤ max (3/4) (2*HeckeZeroSupremum.beta-1) := le_max_left _ _
  have hκβ : 2*HeckeZeroSupremum.beta-1 ≤ max (3/4) (2*HeckeZeroSupremum.beta-1) :=
    le_max_right _ _
  have hP (label : WholeSourceIndex rayM H) :=
    Cycle61MarkedPlain.actual_rowwise_marked_plain_energy_fixedmesh (α := Empty) rayM H hH
    (0 : ℝ → ℂ) 1 2 bΦ (33/50) (33/50) (max (3/4) (2*HeckeZeroSupremum.beta-1)) εm one_pos
    (by simp) contDiff_const (by norm_num) (by linarith) hrad hκ hεm hβ hκβ
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
  intro label rows hreg hnorm m hm hm1 height hh j k hjk σ' hσ' freq hfreq
  have hkeep : ∀ u ∈ rows, initialKeep (Record12518109Natural.cleanWholeBase rayM H hH η η₀ label)
      (internalQ (Record12518109GainWholeGeometry.wholeRegularBad rayM H hH η η₀ label)
        (Record12518109Natural.wholeSourceAnchor rayM H hH η₀ label)) u.val := by
    intro u hu
    exact Record12518109GainWholeGeometry.whole_regular_retained rayM H hH η η₀ rows u
      (Finset.mem_filter.mpr ⟨hu, hreg u hu⟩) label
  have hE : ∀ s : (∅ : Finset Empty), False := fun s => s.1.elim
  have he := (hU label).2 rows (fun u : FreeRow => u.val) Subtype.val_injective
    (fun u => coreFamily rayM H hH η η₀ u label)
    (fun u _ n => Record12518109Natural.natural_initial_element _ u.val u.property.1 n)
    hkeep
    (fun u hu => by
      rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
      exact hnorm u hu)
    m hm (by linarith) ∅ (fun s => (hE s).elim) (fun s => (hE s).elim) (fun s => (hE s).elim)
    (fun s => (hE s).elim) height (fun _ => 0) (fun s => (hE s).elim) (fun s => (hE s).elim)
    (fun s => (hE s).elim) (fun s => (hE s).elim) hh (fun s => (hE s).elim)
    (fun _ _ => by simpa using hh)
    (by simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, add_zero]; exact hm1)
    j k hjk σ' hσ' freq (abs_le.mpr hfreq)
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at he
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
end Qrh.MarkedAnchor.High.Marked
