/- Copyright (c) 2026 Sil. Apache-2.0.
Dirichlet nonvanishing from the ordinary source, the established
unconditional bound, and the analytic return.
-/
import Candidate.Feedback.FourthPower.FinalFromRawSides

set_option autoImplicit false
namespace Candidate.Feedback.FourthPower.RepairedUnconditionalEndpoint
noncomputable section
open OAI.SevenEighths

theorem actual_common_probe :
    Cycle25.UniformCommonProbe theta TargetCompatibility.probeShift :=
  FinalFromRawSides.common_probe_of_raw_sides

theorem actual_beta_bound : HeckeZeroSupremum.beta ≤ theta :=
  FinalFromRawSides.beta_of_raw_sides

theorem actual_canonical_bound : TerminalTransfer.CanonicalGoal :=
  FinalFromRawSides.canonical_of_raw_sides

theorem dirichlet_nonvanishing
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (21867321 / 25000000:ℝ) < s.re) (hpole : ¬(χ=1 ∧ s=1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  actual_canonical_bound χ hs hpole

end
end Candidate.Feedback.FourthPower.RepairedUnconditionalEndpoint
