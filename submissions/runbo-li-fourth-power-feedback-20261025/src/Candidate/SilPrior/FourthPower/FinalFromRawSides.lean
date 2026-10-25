/- Copyright (c) 2026 Sil. Apache-2.0.
Final nonvanishing argument from the ordinary source and the established
PR67 bound. The source is supplied in the contrary branch and combined
with the analytic return.
-/
import Candidate.SilPrior.FourthPower.RepairedRestrictedSource
import Candidate.SilPrior.FourthPower.ReturnCommonProbe
import Candidate.SilPrior.FourthPower.OlderIncumbentSupplier

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.FinalFromRawSides
noncomputable section
open OAI.SevenEighths QRH.Record12518109Existence

/-- Literal six-field equality. No source domain is weakened or enlarged. -/
theorem source_face_eq : SourceContract.face = ReturnSourceFaces.fullSourceFace := rfl

/-- The full ordinary source supplied by the restricted-source construction. -/
theorem full_source_of_raw_sides (hcontra : theta < HeckeZeroSupremum.beta) :
    UniformUnitFaceSource ReturnSourceFaces.fullSourceFace := by
  have hs := RepairedRestrictedSource.actual_required_source hcontra
  change UniformUnitFaceSource SourceContract.face at hs
  simpa only [source_face_eq] using hs

/-- Applies the analytic return to the full source and the established prior. -/
theorem common_probe_of_raw_sides :
    Cycle25.UniformCommonProbe theta TargetCompatibility.probeShift :=
  ReturnCommonProbe.common_probe_of_contrary_source
    OlderIncumbentSupplier.actual full_source_of_raw_sides

/-- Uses the source estimate and analytic return in the contrary branch;
the complementary branch already satisfies the target inequality. -/
theorem beta_of_raw_sides : HeckeZeroSupremum.beta ≤ theta := by
  classical
  by_cases hle : HeckeZeroSupremum.beta ≤ theta
  · exact hle
  · have hcontra : theta < HeckeZeroSupremum.beta := lt_of_not_ge hle
    have hsource := full_source_of_raw_sides hcontra
    have hprobe := ReturnCommonProbe.common_probe_from_full_source
      OlderIncumbentSupplier.actual hsource
    exact TerminalTransfer.beta_of_common_probe hprobe

/-- Exact all-moduli challenge target from the actual source and prior. -/
theorem canonical_of_raw_sides : TerminalTransfer.CanonicalGoal :=
  TerminalTransfer.canonical_of_beta beta_of_raw_sides

end
end Candidate.SilPrior.FourthPower.FinalFromRawSides
