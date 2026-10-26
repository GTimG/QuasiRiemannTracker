import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondExceptionalFamily

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonical
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondRetainedWidth
open CenteredMomentSupport CenteredMomentSecondRadicalColumns
open CenteredMomentSecondRadicalBudget CenteredMomentSecondSixthSource
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockSupport
open CenteredMomentSecondPhysicalBlock CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O

def SecondRowConductorBudget (η : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (U : Finset (CommonIndex C D))
    (τ : RayCharacter→ Character) : Prop :=
  ∀w : O,idealCorrelation C D hC hD (commonFrequencyGenerator C D*w)≠0 → ∀χ,
    (τ χ).modulus.absNorm≤η.modulus.absNorm*fixedFactor*(∏P∈U,P.val).absNorm*
      (Ideal.span {nonunitFrequencyGenerator C D U}).absNorm

/-- Retain the row-level conductor evidence from the existing character
construction, before it is weakened to a nonzero-whole-block premise. -/
theorem exists_row_budgeted_second_family (η : Character) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (hCD : primeSupport C=primeSupport D)
    (U : Finset (CommonIndex C D)) :
    ∃τ,Family η C D hC hD U τ ∧ SecondRowConductorBudget η C D hC hD U τ := by
  choose τ he ht hrest using fun χ : RayCharacter=>exists_retained_width_family η χ C D hC U
  refine ⟨τ,⟨he,?_,?_⟩,?_⟩
  · intro χ I hI hi t
    rw [ht χ I hI t]
    rcases hi with hi|hi
    · rw [residual_sixth_coefficient C D hC hCD U I hI hi]
    · rw [residual_sixth_coefficient_right C D hC hD hCD U I hI hi]
  · intro t S β R rows W K hK n hne χ
    have hne' : physicalBlock η t S β C D hC hD U R (liveRows C D U R rows) W K n≠0 := by
      rwa [←physicalBlock_live_rows η t S β C D hC hD U R rows W K n]
    obtain ⟨w,_,hwc⟩ := physicalBlock_nonzero_common η t S β C D hC hD hCD U R
      (liveRows C D U R rows) (fun z hz=>(liveRows_geometry C D U R rows z hz).2.1)
      W K hK n hne'
    obtain ⟨hN,hwidth⟩ := hrest χ hD hCD (nonunitFrequencyGenerator C D U*w) hwc
    refine ⟨hN,?_⟩
    intro Z hZ z hz
    exact (hwidth Z R hZ z (liveRows_weight C D U R rows z hz)).2.2.2.2.2
  · intro w hw χ
    exact (hrest χ hD hCD w hw).1

end
end OAI.SevenEighths.Cycle63InitialMass
