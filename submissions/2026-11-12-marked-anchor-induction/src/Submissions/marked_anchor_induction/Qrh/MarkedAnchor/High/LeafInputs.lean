/- Copyright (c) 2026 Sil. Apache-2.0.
The localized family follows Hailey Collet's `NaturalBatch.localizeFamily`
(`Record12518109Gain/LocalizedBatch.lean`, Apache-2.0). -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.CoreInputs

/-!
# High.LeafInputs

The row-local marked inputs, and the detector inputs of one core batch in the form
`High.BatchMax.core_batch_guards` consumes.

**Witnesses on the rows.** `HighMarkedCoreInputs` (`High.LeafContract`) quantifies over a witness
function `wit : ∀ u : FreeRow, SupportedWitness (coreFamily … u) …` that is TOTAL on `FreeRow`. A
witness contains an actual zero `ρ` with `a ≤ re ρ` of some member of `coreFamily … u`, so for a
general free row `u` none exists. The leaf can only produce witnesses on the rows of the batch,
from the buffered zero guards of those rows, so that hypothesis cannot be instantiated.

The marked fields do not involve the witness, only its label and dyadic indices on the rows. So we
ask for the witness on the rows only:
* `HighMarkedCoreInputsR` is `HighMarkedCoreInputs` with `wit : ∀ u ∈ rows, SupportedWitness …`;
* it is STRONGER than the total-witness statement (`HighMarkedCoreInputsR.frozen`).

With it, `locFiberInputs` gives the whole `AnchorFiberMoments` for the LOCALIZED family
`locFamily … rows u0`, which agrees with `coreFamily` on `rows` and with the family of a fixed row `u0`
elsewhere. That family has total witnesses (every row's guards are those of a batch row), which is
the form `core_batch_guards` needs (`Row = FreeRow`). The unmarked fields come from
`Cofactor.core_unmarked_fields` (generic family, coefficients only on the rows); the marked ones
come from `HighMarkedCoreInputsR` through `castWit`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
open HeckeDyadic HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount
open HeckeDetectorDyadicProfiles Cycle61Moment
local notation "O" => HeckeFamily.O
local instance leafInputsQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- **`HighMarkedCoreInputs` with the witness on the rows only.** -/
def HighMarkedCoreInputsR (a0 a1 wlo : ℝ) : Prop :=
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
      ∀ (wit : ∀ u ∈ rows, SupportedWitness (coreFamily rayM H hH η η₀ u) U a ε
          (3*wc/2+1/1000000) Tz allowance i)
        (label : WholeSourceIndex rayM H) (J' K' : Fin (dyadicLength U)),
      (∀ u (hu : u ∈ rows), (wit u hu).label = label ∧ (wit u hu).left = J' ∧
        (wit u hu).right = K') →
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

/-- The row-local version is stronger than the total-witness one. -/
theorem HighMarkedCoreInputsR.frozen {a0 a1 wlo : ℝ} (h : HighMarkedCoreInputsR a0 a1 wlo) :
    HighMarkedCoreInputs a0 a1 wlo := by
  intro εm hεm
  obtain ⟨meshm, hm, h'⟩ := h εm hεm
  refine ⟨meshm, hm, ?_⟩
  intro rayM _ H hH W hWs hW η η₀ Slot _ _ wrmin hwrmin
  obtain ⟨J, C, hC, hev⟩ := h' rayM H hH W hWs hW η η₀ (Slot := Slot) wrmin hwrmin
  refine ⟨J, C, hC, ?_⟩
  filter_upwards [hev] with U hU
  refine ⟨hU.1, ?_⟩
  intro a ε Tz allowance height i ha hε0 hε1 hh hf slots θ wr σ v t hwmin hwm hσ rows hnorm hreg
    wc hwc hwlo wit label J' K' hfib C' hC'
  exact hU.2 a ε Tz allowance height i ha hε0 hε1 hh hf slots θ wr σ v t hwmin hwm hσ rows hnorm
    hreg wc hwc hwlo (fun u _ => wit u) label J' K' (fun u hu => hfib u hu) C' hC'

/-! ### Witness transport along an equality of families -/

/-- A witness of `χ` is a witness of any family equal to `χ`. -/
def castWit {L : Type*} {χ χ' : L → Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (h : χ = χ') (w : SupportedWitness χ U a ε tstar T allowance i) :
    SupportedWitness χ' U a ε tstar T allowance i := h ▸ w

theorem castWit_fields {L : Type*} {χ χ' : L → Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (h : χ = χ') (w : SupportedWitness χ U a ε tstar T allowance i) :
    (castWit h w).label = w.label ∧ (castWit h w).left = w.left ∧
      (castWit h w).right = w.right := by
  subst h
  exact ⟨rfl, rfl, rfl⟩

/-! ### The localized core family -/

section Loc
variable (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
  (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- The core family on `rows`, and the family of the fixed row `u0` elsewhere. -/
def locFamily (η η₀ : Character) (rows : Finset FreeRow) (u0 : FreeRow) (u : FreeRow) :
    WholeSourceIndex rayM H → Character :=
  coreFamily rayM H hH η η₀ (if u ∈ rows then u else u0)

theorem locFamily_of_mem (η η₀ : Character) {rows : Finset FreeRow} (u0 : FreeRow) {u : FreeRow}
    (hu : u ∈ rows) : locFamily rayM H hH η η₀ rows u0 u = coreFamily rayM H hH η η₀ u := by
  unfold locFamily
  rw [if_pos hu]

end Loc

/-- **The detector inputs of one core batch, localized family.** Same prefix as
`HighCoreFiberInputs`; then for every batch `rows`, base row `u0`, witness function of the
localized family and sub-fiber `F ⊆ rows`, the whole `AnchorFiberMoments`. -/
theorem locFiberInputs (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {a0 a1 wlo : ℝ} (hM : HighMarkedCoreInputsR a0 a1 wlo) :
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
        ∀ (rows : Finset FreeRow), (∀ u ∈ rows, ((Ideal.span {u.val}).absNorm : ℝ) ≤ U) →
        (∀ u ∈ rows, RegularCore rayM H hH η η₀ u) → ∀ (u0 : FreeRow),
        ∀ (wc : ℝ), wc ∈ cutoffs → wlo ≤ wc →
        ∀ (wit : ∀ u, SupportedWitness (locFamily rayM H hH η η₀ rows u0 u) U a ε
            (3*wc/2+1/1000000) Tz allowance i),
        ∀ F : Finset FreeRow, F ⊆ rows →
        ∀ (label : WholeSourceIndex rayM H) (J' K' : Fin (dyadicLength U)),
        (∀ u ∈ F, (wit u).label = label ∧ (wit u).left = J' ∧ (wit u).right = K') →
        ∀ C' : ℝ, C * (1+height)^J ≤ C' →
        AnchorFiberMoments F slots (locFamily rayM H hH η η₀ rows u0)
          (coreSlot rayM H hH η η₀ W U θ wr σ v t) wr U a ε (3*wc/2+1/1000000) a0 a1 wc εm C'
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
  intro a ε Tz allowance height i ha hε0 hε1 hh hf slots θ wr σ v t hwmin hwm hσ rows hnorm hreg
    u0 wc hwc hwlo wit F hF label J' K' hfib C' hC'
  have h1 : (1:ℝ) ≤ 1 + height := by linarith
  have hJm : Cm * (1+height)^Jm ≤ C' := by
    refine le_trans ?_ hC'
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h1 (Nat.le_add_right _ _))
      (by positivity) (le_trans hCm.le (le_max_left _ _))
  have hJu : Cu * (1+height)^Ju ≤ C' := by
    refine le_trans ?_ hC'
    exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ h1 (Nat.le_add_left _ _))
      (by positivity) (le_trans hCm.le (le_max_left _ _))
  obtain ⟨ht1, ht2⟩ := tstar_mem hwc
  have hloc : ∀ u ∈ F, locFamily rayM H hH η η₀ rows u0 u = coreFamily rayM H hH η η₀ u :=
    fun u hu => locFamily_of_mem rayM H hH η η₀ u0 (hF hu)
  obtain ⟨hI, hP⟩ := hUm.2 a ε Tz allowance height i ha hε0 hε1 hh hf slots θ wr σ v t hwmin hwm
    hσ F (fun u hu => hnorm u (hF hu)) (fun u hu => hreg u (hF hu)) wc hwc hwlo
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
  obtain ⟨hI0, hP0⟩ := hUu.2 a ε (3*wc/2+1/1000000) Tz allowance height i ha hε0 hε1 ht1 ht2 hh hf
    F (locFamily rayM H hH η η₀ rows u0) (fun _ => false) (fun u hu => hnorm u (hF hu)) hcoeff
    wit label J' K' hfib C' hJu
  refine ⟨hI0, hP0, ?_, ?_⟩
  · intro e1 e2 sel hsel hz n hn σ' hσ' freq hfreq
    rw [Finset.sum_congr rfl (fun u hu => by rw [hloc u hu])]
    exact hI e1 e2 sel hsel hz n hn σ' hσ' freq hfreq
  · intro e1 e2 sel hsel hz j k hjk σ' hσ' freq hfreq
    rw [Finset.sum_congr rfl (fun u hu => by rw [hloc u hu])]
    exact hP e1 e2 sel hsel hz j k hjk σ' hσ' freq hfreq

end
end Qrh.MarkedAnchor.High
