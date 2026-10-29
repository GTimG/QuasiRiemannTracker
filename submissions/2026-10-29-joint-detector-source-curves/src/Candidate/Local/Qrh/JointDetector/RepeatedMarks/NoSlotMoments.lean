/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.RootedBatch
import Submissions.hailey_collet_1252270103.Cycle61.Density.NaturalEndpoint

namespace Qrh.JointDetector.RepeatedMarks
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators
open Set Filter OAI OAI.SevenEighths
open HeckeFamily HeckeInverseAmplification HeckeDetectorSupportedWitness
open LocalMoment HeckeDetectorWitnessRows HeckeDetectorDyadicProfiles

/-- Exact unmarked detector batch extracted from the same rooted rows.
Only coefficient identities are assumed; neither raw moments nor counts
are fields of the rooted batch. -/
def RootedBatch.unmarked {Label Slot : Type*}
    {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
    {hH : RayOrthogonality.globalUnits M≤H}
    {base anchor : Label→Character} {bad : Label→Ideal O}
    {W : ℝ→ℂ} {U Aroot a ε tstar T allowance : ℝ} {i : ℕ}
    (B : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot)
    (reverse : Label → Bool) (χ : FreeRow → Label → Character)
    (witness : ∀ u, SupportedWitness (χ u) U a ε tstar T allowance i)
    (hχ : ∀ u∈B.rows,∀ j I, idealCoeff (χ u j) I=
      if reverse j then starRingEnd ℂ (idealCoeff (B.family u j) I)
      else idealCoeff (B.family u j) I) :
    UnmarkedBatch Label U a ε tstar T allowance i where
  rows := B.rows
  family := χ
  witness := witness
  row_norm := B.rowNorm
  data := (FixedUnmarkedDictionary.ofBases base).data
  reverse := reverse
  row_coeff := by
    intro u hu j I
    rw [hχ u hu j I,B.idealCoefficients u hu j I]
    rfl

/-- The established analytic no-slot fields apply uniformly to every
rooted batch and both actual detector orientations. Constants precede
the scale, witnesses, original slots and common root masks. -/
theorem rooted_actual_no_slot_moments {Label : Type*} [Fintype Label]
    (base : Label → Character) (c κ εm : ℝ)
    (hc : 0 < c) (hκ : 0 < κ) (hεm : 0 < εm)
    (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop, 1 < U ∧
    ∀ {a ε tstar T allowance : ℝ} {i : ℕ},
    1 ≤ tstar → tstar ≤ 3/2 → 0 ≤ ε → ε ≤ 1/1000 →
    ∀ {Slot : Type} {M : Ideal O} [NeZero M] {H : Subgroup (O⧸M)ˣ}
      {hH : RayOrthogonality.globalUnits M≤H}
      {anchor : Label→Character} {bad : Label→Ideal O} {W : ℝ→ℂ} {Aroot : ℝ}
      (B : RootedBatch (Slot:=Slot) M H hH base anchor bad W U Aroot)
      (reverse : Label → Bool) (χ : FreeRow → Label → Character)
      (witness : ∀ u, SupportedWitness (χ u) U a ε tstar T allowance i)
      (hχ : ∀ u∈B.rows,∀ j I,idealCoeff (χ u j) I=
        if reverse j then starRingEnd ℂ (idealCoeff (B.family u j) I)
        else idealCoeff (B.family u j) I),
    ∀ height : ℝ, 0 ≤ height → ∀ j left right,
      ∀ hne : ((B.unmarked reverse χ witness hχ).fiberRows j left right).Nonempty,
      UnmarkedMoments ((B.unmarked reverse χ witness hχ).fiber j left right hne)
        c κ (C*(1+height)^J) height εm := by
  obtain ⟨J,C,hC,h⟩ := fixed_dictionary_actual_batch_moments
    (FixedUnmarkedDictionary.ofBases base) c κ εm hc hκ hεm hβ
  refine ⟨J,C,hC,?_⟩
  filter_upwards [h] with U hU
  refine ⟨hU.1,?_⟩
  intro a ε tstar T allowance i ht ht' hε hε' Slot M inst H hH anchor bad W Aroot
    B reverse χ witness hχ height hh j left right hne
  exact hU.2 ht ht' hε hε' (B.unmarked reverse χ witness hχ) rfl height hh j left right hne

end
end Qrh.JointDetector.RepeatedMarks
#print axioms Qrh.JointDetector.RepeatedMarks.rooted_actual_no_slot_moments
