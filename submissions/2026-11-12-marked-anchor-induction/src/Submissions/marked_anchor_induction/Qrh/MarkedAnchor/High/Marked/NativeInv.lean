/- Copyright (c) 2026 Sil. Apache-2.0.
Uses Hailey Collet's `actual_free_inverse_energy` (Apache-2.0). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Marked.Contract
import Submissions.hailey_collet_1252270103.Record12518109Gain.ActualSourceFields

/-!
# High.Marked.NativeInv

`core_inverse_native`: the marked inverse moment on core fibers inside the native region
`x + 2S < 1`, `2x + 8S < 3` (HC's unconditional `actual_free_inverse_energy`: row-wise heights,
arbitrary, even overlapping, pools). Used above `TOP - 10^-7`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High.Marked
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDyadic
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentPrimeSlot
open HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount Cycle61Moment
open Qrh.MarkedAnchor.High
local notation "O" => HeckeFamily.O
local instance markedNativeQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- **Native marked inverse moment on core fibers.** -/
theorem core_inverse_native (εm : ℝ) (hεm : 0 < εm)
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H)
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ W)
    (η η₀ : Character) (Slot : Type) [Fintype Slot] [DecidableEq Slot]
    (wrmin : ℝ) (hwrmin : 0 < wrmin) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
      ∀ (label : WholeSourceIndex rayM H) (rows : Finset FreeRow),
      (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
      ∀ (selected : Finset Slot) (θ : Slot → RayQuotient.Characters rayM H) (wr σ v : Slot → ℝ)
        (t : FreeRow → ℝ) (height : ℝ),
      (∀ s ∈ selected, wrmin ≤ wr s) →
      (∀ s ∈ selected, σ s = 33/50) → 0 ≤ height → (∀ u ∈ rows, |t u| ≤ height) →
      ∀ x : ℝ, 0 ≤ x → x + 2*(∑ s ∈ selected, wr s) < 1 → 2*x + 8*(∑ s ∈ selected, wr s) < 3 →
      ∀ (tstar : ℝ) (n : ℕ), n ≤ 2 → ∀ σ' ∈ Set.Icc (0:ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
      ∑ u ∈ rows, ‖polynomial (coreFamily rayM H hH η η₀ u label) true
          ((logProfile^[n]) (inverseTest U tstar x)) (U^x) σ' freq *
        (∏ s ∈ selected, coreSlot rayM H hH η η₀ W U θ wr σ v t u s)‖^2 ≤
        C*(1+height)^J*U^(1+εm) := by
  obtain ⟨deg, hfield⟩ := Record12518109GainActual.actual_free_inverse_energy W (33/50) (33/50) εm
    hWs hW hεm (Fintype.card Slot)
  let data : WholeSourceIndex rayM H → RowData := fun l =>
    ProbeHighRowFamily.momentData (Record12518109Natural.cleanWholeBase rayM H hH η η₀ l)
  choose Cl Ul hCl hUl hb using fun l => hfield (data l)
  let Csum : ℝ := ∑ l, Cl l
  have hCsum : 0 ≤ Csum := Finset.sum_nonneg (fun l _ => (hCl l).le)
  have hCl_le (l : WholeSourceIndex rayM H) : Cl l ≤ 1 + Csum := by
    have := Finset.single_le_sum (fun l _ => (hCl l).le) (Finset.mem_univ l)
    linarith
  refine ⟨deg, 1 + Csum, by linarith, ?_⟩
  let Nbig : ℝ :=
    ∑ l, ((DetectorDictionaryInverseRawInitialGates.deletedBase (data l)).modulus.absNorm : ℝ)
  have hbig : ∀ᶠ U : ℝ in atTop, Nbig < U^wrmin :=
    (tendsto_rpow_atTop hwrmin).eventually (eventually_gt_atTop Nbig)
  filter_upwards [eventually_gt_atTop (1:ℝ), hbig,
    eventually_all.mpr (fun l => eventually_ge_atTop (Ul l))] with U hU1 hUbig hUl'
  refine ⟨hU1, ?_⟩
  intro label rows hnorm selected θ wr σ v t height hwmin hσ hh ht x hx0 hg1 hg2 tstar n hn
    σ' hσ' freq hfreq
  have hU0 : 0 < U := zero_lt_one.trans hU1
  have hDel (s : Slot) (hs : s ∈ selected) :
      ((DetectorDictionaryInverseRawInitialGates.deletedBase (data label)).modulus.absNorm : ℝ) <
        U^(wr s) := by
    have h1 := lt_of_lt_of_le hUbig (Real.rpow_le_rpow_of_exponent_le hU1.le (hwmin s hs))
    have hl := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) =>
      (Nat.cast_nonneg _ : (0:ℝ) ≤
        ((DetectorDictionaryInverseRawInitialGates.deletedBase (data l)).modulus.absNorm : ℝ)))
      (Finset.mem_univ label)
    linarith
  have he := hb label U (hUl' label) (ι := selected) (by simpa using Finset.card_le_univ selected)
    (fun s => Cycle61MarkedPlain.annularPool (primePool rayM H 2 (U^(wr s.val))) (U^(wr s.val)))
    (fun s => wr s.val) (fun s => hwrmin.le.trans (hwmin s.val s.property))
    (fun s P hP => (Finset.mem_filter.mp (Cycle61MarkedPlain.annularPool_subset _ _ hP)).2.1)
    (fun s P hP => Cycle61MarkedPlain.annularPool_ratio _ _ _ hP)
    (fun s => hDel s.val s.property)
    (excluded η (Record12518109Natural.wholeAnchorMask rayM H hH η₀))
    (fun s => relativeCharacter rayM H hH η₀ (θ s.val)) (fun s => σ s.val) (fun s => v s.val) t
    (fun s => (hσ s.val s.property).ge) (fun s => (hσ s.val s.property).le) x hx0
    (by simpa only [Finset.sum_coe_sort] using hg1) (by simpa only [Finset.sum_coe_sort] using hg2)
    rows
    (fun u hu => by
      rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]; exact hnorm u hu)
    (fun u => coreFamily rayM H hH η η₀ u label)
    (fun u _ I => LocalMoment.natural_raw_coefficients _ ⟨u.val, u.property.1⟩ I)
    tstar n hn σ' hσ' height freq hh hfreq ht
  refine le_trans (le_of_eq ?_) (he.trans ?_)
  · apply Finset.sum_congr rfl
    intro u _
    congr 2
    rw [← Finset.prod_coe_sort selected]
    congr 1
    apply Finset.prod_congr rfl
    intro s _
    exact (Cycle61MarkedPlain.naturalSlot_annular_filter _ _
      (fun I => idealCoeff (relativeCharacter rayM H hH η₀ (θ s.val)) I) W hWs _ _ _).symm
  · have h1 : (1:ℝ) ≤ 1 + height := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCl_le label) (by positivity))
      (Real.rpow_nonneg hU0.le _)

end
end Qrh.MarkedAnchor.High.Marked
