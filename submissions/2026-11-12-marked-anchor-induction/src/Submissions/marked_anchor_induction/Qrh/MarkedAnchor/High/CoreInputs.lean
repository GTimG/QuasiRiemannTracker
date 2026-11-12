/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.LeafContract
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.High.Cofactor.Unmarked

/-!
# High.CoreInputs

The per-fiber inputs of the HIGH detector on the core batches of one sixth-power cofactor class
follow from the MARKED core inputs (`HighMarkedCoreInputs`):

`highCoreFiberInputs_of_marked : HighMarkedCoreInputs a0 a1 wlo → HighCoreFiberInputs a0 a1 wlo`.

The unmarked fields are `Cofactor.core_unmarked_fields` for the fixed dictionary
`wholeRegularDictionary rayM H hH η η₀` (whose data are the clean core bases, so the core family
`coreFamily` has exactly its coefficients, `natural_raw_coefficients`), with HC's
`canonicalDensityCountingSetup`.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Set
open OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness HeckeDetectorWitnessRows
local notation "O" => HeckeFamily.O

/-- `1 ≤ 3 wc/2 + 10^-6 ≤ 3/2` on the cutoffs. -/
theorem tstar_mem {wc : ℝ} (hwc : wc ∈ cutoffs) :
    1 ≤ 3*wc/2+1/1000000 ∧ 3*wc/2+1/1000000 ≤ 3/2 := by
  obtain ⟨h1, h2⟩ := hwc
  unfold cutLo at h1; unfold cutHi at h2
  constructor <;> linarith

/-- **Core fiber inputs from the marked core inputs.** -/
theorem highCoreFiberInputs_of_marked (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    {a0 a1 wlo : ℝ} (hM : HighMarkedCoreInputs a0 a1 wlo) : HighCoreFiberInputs a0 a1 wlo := by
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
    wc hwc hwlo wit label J' K' hfib C' hC'
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
  obtain ⟨hI, hP⟩ := hUm.2 a ε Tz allowance height i ha hε0 hε1 hh hf slots θ wr σ v t hwmin hwm
    hσ rows hnorm hreg wc hwc hwlo wit label J' K' hfib C' hJm
  have hcoeff : ∀ u ∈ rows, ∀ j, ∀ I : Ideal O, idealCoeff (coreFamily rayM H hH η η₀ u j) I =
      if (fun _ => false) j then starRingEnd ℂ (idealCoeff
        (((OAI.SevenEighths.Record12518109GainWholeGeometry.wholeRegularDictionary rayM H hH η
          η₀).data j).character ⟨u.val, u.property.1⟩) I)
      else idealCoeff
        (((OAI.SevenEighths.Record12518109GainWholeGeometry.wholeRegularDictionary rayM H hH η
          η₀).data j).character ⟨u.val, u.property.1⟩) I := by
    intro u _ j I
    simp only [Bool.false_eq_true, ite_false]
    exact OAI.SevenEighths.LocalMoment.natural_raw_coefficients _ ⟨u.val, u.property.1⟩ I
  obtain ⟨hI0, hP0⟩ := hUu.2 a ε (3*wc/2+1/1000000) Tz allowance height i ha hε0 hε1 ht1 ht2 hh hf
    rows (coreFamily rayM H hH η η₀) (fun _ => false) hnorm hcoeff wit label J' K' hfib C' hJu
  exact ⟨hI0, hP0, hI, hP⟩

end
end Qrh.MarkedAnchor.High
