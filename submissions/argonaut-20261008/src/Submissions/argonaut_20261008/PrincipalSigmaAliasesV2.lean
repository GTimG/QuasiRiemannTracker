import Submissions.argonaut_20261008.PrincipalSignalFiniteSigma
import Submissions.argonaut_20261008.PrincipalBoundaryB0

namespace OAI
noncomputable section
open scoped Classical BigOperators
open Complex

namespace SevenEighths.PrincipalSlotEstimate

/-- The actual finite principal slot differentiability theorem specialized at `b0`. -/
abbrev principalSlot_differentiableAt_actual_b0 {Q : ℝ} {A η s : ℂ} :=
  OAI.SevenEighths.PrincipalSignalComparison.principalSlot_differentiableAt_sigma
    (Q := Q) (A := A) (η := η) (s := s)
    (b := analyticBoundaryB0)
    seventyNineHundredths_le_analyticBoundaryB0
    analyticBoundaryB0_le_one

end SevenEighths.PrincipalSlotEstimate

namespace SevenEighths.PrincipalSignalComparison

/-- Actual `P ^ (-b0)` ratio error; no projection to the old `7/8` record. -/
abbrev slotRatio_error_actual_b0 {κ ι : Type*} :=
  slotRatio_error_sigma (κ := κ) (ι := ι)
    (b := analyticBoundaryB0)
    seventyNineHundredths_le_analyticBoundaryB0
    analyticBoundaryB0_le_one

/-- Actual `P ^ (-b0)` ratio norm bound; no old-line conversion. -/
abbrev slotRatio_bound_actual_b0 {κ ι : Type*} :=
  slotRatio_bound_sigma (κ := κ) (ι := ι)
    (b := analyticBoundaryB0)
    seventyNineHundredths_le_analyticBoundaryB0
    analyticBoundaryB0_le_one

/-- Continuity on the `b0` line from the actual sigma finite-slot theorem. -/
abbrev slotRatio_continuous_line_actual_b0 {κ ι : Type*} :=
  slotRatio_continuous_line_sigma (κ := κ) (ι := ι)
    (b := analyticBoundaryB0)
    seventyNineHundredths_le_analyticBoundaryB0
    analyticBoundaryB0_le_one

end SevenEighths.PrincipalSignalComparison

end
end OAI
