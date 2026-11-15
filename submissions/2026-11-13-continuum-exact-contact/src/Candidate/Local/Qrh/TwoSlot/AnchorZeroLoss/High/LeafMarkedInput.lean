/- Modified by Joseph Bebel (2026-11-12): positive source and detector
pads for the stronger anchor target. The actual physical coefficient,
mask and height contracts are preserved. Inherited attribution follows. -/
/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
The localized family follows Hailey Collet's `NaturalBatch.localizeFamily`
(`Record12518109Gain/LocalizedBatch.lean`, Apache-2.0). -/
import Candidate.Local.Qrh.TwoSlot.AnchorZeroLoss.High.LeafInputs

/-!
# High.LeafMarkedInput

The marked core inputs the HIGH leaf consumes: the inverse anchors accept overlapping pools, so no
slot separation is required; the slot and row heights are bounded.

* `HighMarkedCoreInputsH a0 a1 wlo` — `HighMarkedCoreInputsR` (witness on the rows) plus bounded
  heights: `(∀ s ∈ slots, |v s| ≤ height)` after `σ = 33/50`, and `(∀ u ∈ rows, |t u| ≤ height)`
  after `RegularCore`;
* `locFiberInputsH` — `locFiberInputs` for it: the whole `AnchorFiberMoments` of every sub-fiber of a
  core batch, for the localized family (the `hmom` of `High.BatchMax.core_batch_guards`).
-/

set_option autoImplicit false

namespace Qrh.TwoSlot.AnchorZeroLoss.High
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open HeckeDyadic HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount
open HeckeDetectorDyadicProfiles Cycle61Moment
local notation "O" => HeckeFamily.O
local instance leafMarkedInputQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- **Marked core inputs with bounded heights, no slot separation.** -/
def HighMarkedCoreInputsH (a0 a1 wlo : ℝ)
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
      -- `inverseMarked`
      (wc ≤ Real.logb U ((2 : ℝ)^J'.val) → Real.logb U ((2 : ℝ)^J'.val) < 1 →
        ∀ selected : Finset Slot, selected ⊆ slots →
          (∑ s ∈ selected, wr s) ≤ min (max 0 ((1-Real.logb U ((2 : ℝ)^J'.val))/2 + (a0-a1*Real.logb U ((2 : ℝ)^J'.val))-pad)) (∑ s ∈ slots, wr s) →
        ∀ n : ℕ, n ≤ 2 → ∀ σ' ∈ Set.Icc (0 : ℝ) 1, ∀ freq ∈ Set.Icc (-height) height,
        ∑ u ∈ rows, ‖polynomial (coreFamily rayM H hH η η₀ u label) true
          ((HeckeDetectorRowwisePolynomial.logProfile^[n])
            (HeckeDetectorInverseFiberCount.inverseTest U (3*wc/2+shift)
              (Real.logb U ((2 : ℝ)^J'.val))))
          (U^(Real.logb U ((2 : ℝ)^J'.val))) σ' freq *
          (∏ s ∈ selected, coreSlot rayM H hH η η₀ W U θ wr σ v t u s)‖^2 ≤ C' * U^(1+εm)) ∧
      -- `plainMarked`
      (wc ≤ 2*Real.logb U ((2 : ℝ)^K'.val) → 2*Real.logb U ((2 : ℝ)^K'.val) < 1 →
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
          (∏ s ∈ selected, coreSlot rayM H hH η η₀ W U θ wr σ v t u s)‖^2 ≤ C' * U^(1+εm))

/-- The unconditional row-local form implies the bounded-height form. -/
theorem highMarkedCoreInputsH_of_R {a0 a1 wlo : ℝ} (h : HighMarkedCoreInputsR a0 a1 wlo) :
    HighMarkedCoreInputsH a0 a1 wlo := by
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

/-- **`locFiberInputs` for the bounded-height marked contract.** -/
theorem locFiberInputsH_with_shift (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {shift a0 a1 wlo : ℝ} (hs0 : 0 ≤ shift) (hshi : shift ≤ 1/1000)
    (hM : HighMarkedCoreInputsH a0 a1 wlo (1/10000000000000) shift) :
    ∀ (εm : ℝ), 0 < εm → ∃ meshm : ℝ, 0 < meshm ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
      (hH : RayOrthogonality.globalUnits rayM ≤ H)
      (W : ℝ → ℂ), Function.support W ⊆ Set.Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
      ∀ (η η₀ : Character) {Slot : Type} [Fintype Slot] [DecidableEq Slot] (wrmin : ℝ),
      0 < wrmin →
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
        (∀ u ∈ rows, |t u| ≤ height) → ∀ (u0 : FreeRow),
        ∀ (wc : ℝ), wc ∈ cutoffs → wlo ≤ wc →
        ∀ (wit : ∀ u, SupportedWitness (locFamily rayM H hH η η₀ rows u0 u) U a ε
            (3*wc/2+shift) Tz allowance i),
        ∀ F : Finset FreeRow, F ⊆ rows →
        ∀ (label : WholeSourceIndex rayM H) (J' K' : Fin (dyadicLength U)),
        (∀ u ∈ F, (wit u).label = label ∧ (wit u).left = J' ∧ (wit u).right = K') →
        ∀ C' : ℝ, C * (1+height)^J ≤ C' →
        AnchorFiberMoments F slots (locFamily rayM H hH η η₀ rows u0)
          (coreSlot rayM H hH η η₀ W U θ wr σ v t) wr U a ε (3*wc/2+shift) a0 a1 wc εm C'
          height label J' K' := by
  intro εm hεm
  obtain ⟨meshm, hmeshm, hM'⟩ := hM εm hεm
  refine ⟨meshm, hmeshm, ?_⟩
  intro rayM _ H hH W hWs hW η η₀ Slot _ _ wrmin hwrmin
  obtain ⟨Jm, Cm, hCm, hevM⟩ := hM' rayM H hH W hWs hW η η₀ (Slot := Slot) wrmin hwrmin
  obtain ⟨Ju, Cu, hCu, hevU⟩ := Cofactor.core_unmarked_fields
    (OAI.SevenEighths.Record12518109GainWholeGeometry.wholeRegularDictionary rayM H hH η η₀)
    OAI.SevenEighths.LocalMoment.canonicalDensityCountingSetup εm hεm hβ
  refine ⟨Jm + Ju, max Cm Cu, lt_max_of_lt_left hCm, ?_⟩
  filter_upwards [hevM, hevU] with U hUm hUu
  refine ⟨hUm.1, ?_⟩
  intro a ε Tz allowance height i ha hε0 hε1 hh hf slots θ wr σ v t hwmin hwm hσ hv rows
    hnorm hreg ht u0 wc hwc hwlo wit F hF label J' K' hfib C' hC'
  have h1 : (1:ℝ) ≤ 1 + height := by linarith
  have hJm : Cm * (1+height)^Jm ≤ C' := by
    refine le_trans ?_ hC'
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h1 (Nat.le_add_right _ _))
      (by positivity) (le_trans hCm.le (le_max_left _ _))
  have hJu : Cu * (1+height)^Ju ≤ C' := by
    refine le_trans ?_ hC'
    exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ h1 (Nat.le_add_left _ _))
      (by positivity) (le_trans hCm.le (le_max_left _ _))
  obtain ⟨ht1, ht2⟩ := tstar_mem_with_shift hs0 hshi hwc
  have hloc : ∀ u ∈ F, locFamily rayM H hH η η₀ rows u0 u = coreFamily rayM H hH η η₀ u :=
    fun u hu => locFamily_of_mem rayM H hH η η₀ u0 (hF hu)
  obtain ⟨hI, hP⟩ := hUm.2 a ε Tz allowance height i ha hε0 hε1 hh hf slots θ wr σ v t hwmin hwm
    hσ hv F (fun u hu => hnorm u (hF hu)) (fun u hu => hreg u (hF hu))
    (fun u hu => ht u (hF hu)) wc hwc hwlo
    (fun u hu => castWit (hloc u hu) (wit u)) label J' K'
    (fun u hu => by
      obtain ⟨e1, e2, e3⟩ := castWit_fields (hloc u hu) (wit u)
      rw [e1, e2, e3]
      exact hfib u hu) C' hJm
  have hcoeff : ∀ u ∈ F, ∀ j, ∀ I : Ideal O,
      idealCoeff (locFamily rayM H hH η η₀ rows u0 u j) I =
      if (fun _ => false) j then starRingEnd ℂ (idealCoeff
        (((OAI.SevenEighths.Record12518109GainWholeGeometry.wholeRegularDictionary rayM H hH η
          η₀).data j).character ⟨u.val, u.property.1⟩) I)
      else idealCoeff
        (((OAI.SevenEighths.Record12518109GainWholeGeometry.wholeRegularDictionary rayM H hH η
          η₀).data j).character ⟨u.val, u.property.1⟩) I := by
    intro u hu j I
    rw [hloc u hu]
    simp only [Bool.false_eq_true, ite_false]
    exact OAI.SevenEighths.LocalMoment.natural_raw_coefficients _ ⟨u.val, u.property.1⟩ I
  obtain ⟨hI0, hP0⟩ := hUu.2 a ε (3*wc/2+shift) Tz allowance height i ha hε0 hε1 ht1 ht2 hh hf
    F (locFamily rayM H hH η η₀ rows u0) (fun _ => false) (fun u hu => hnorm u (hF hu)) hcoeff
    wit label J' K' hfib C' hJu
  refine ⟨hI0, hP0, ?_, ?_⟩
  · intro e1 e2 sel hsel hz n hn σ' hσ' freq hfreq
    rw [Finset.sum_congr rfl (fun u hu => by rw [hloc u hu])]
    exact hI e1 e2 sel hsel hz n hn σ' hσ' freq hfreq
  · intro e1 e2 sel hsel hz j k hjk σ' hσ' freq hfreq
    rw [Finset.sum_congr rfl (fun u hu => by rw [hloc u hu])]
    exact hP e1 e2 sel hsel hz j k hjk σ' hσ' freq hfreq

/-- Specialization to the frozen finite witness shift. -/
theorem locFiberInputsH (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {a0 a1 wlo : ℝ} (hM : HighMarkedCoreInputsH a0 a1 wlo) :
    ∀ (εm : ℝ), 0 < εm → ∃ meshm : ℝ, 0 < meshm ∧
    ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
      (hH : RayOrthogonality.globalUnits rayM ≤ H)
      (W : ℝ → ℂ), Function.support W ⊆ Set.Icc (1:ℝ) 2 → ContDiff ℝ ∞ W →
      ∀ (η η₀ : Character) {Slot : Type} [Fintype Slot] [DecidableEq Slot] (wrmin : ℝ),
      0 < wrmin →
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
        (∀ u ∈ rows, |t u| ≤ height) → ∀ (u0 : FreeRow),
        ∀ (wc : ℝ), wc ∈ cutoffs → wlo ≤ wc →
        ∀ (wit : ∀ u, SupportedWitness (locFamily rayM H hH η η₀ rows u0 u) U a ε
            (3*wc/2+1/1000000000000) Tz allowance i),
        ∀ F : Finset FreeRow, F ⊆ rows →
        ∀ (label : WholeSourceIndex rayM H) (J' K' : Fin (dyadicLength U)),
        (∀ u ∈ F, (wit u).label = label ∧ (wit u).left = J' ∧ (wit u).right = K') →
        ∀ C' : ℝ, C * (1+height)^J ≤ C' →
        AnchorFiberMoments F slots (locFamily rayM H hH η η₀ rows u0)
          (coreSlot rayM H hH η η₀ W U θ wr σ v t) wr U a ε (3*wc/2+1/1000000000000) a0 a1 wc εm C'
          height label J' K' :=
  locFiberInputsH_with_shift hβ (by norm_num) (by norm_num) hM

end
end Qrh.TwoSlot.AnchorZeroLoss.High
