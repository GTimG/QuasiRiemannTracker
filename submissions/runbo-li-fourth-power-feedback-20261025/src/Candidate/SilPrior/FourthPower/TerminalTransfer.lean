/- Copyright (c) 2026 Sil. Apache-2.0.
GENERIC TERMINAL ADAPTERS. Their named beta/common-probe inputs are still to
be supplied by the actual analytical return. This is not Candidate.Main and
does not assert Candidate.bound. No source estimate is concealed in a typeclass.

Reuse: PR69 Cycle25.Assembly.Continuation, itself the general continuation
and Dirichlet transfer on the pinned OpenAI Hecke definitions.
-/
import Candidate.SilPrior.FourthPower.TargetCompatibility
import Submissions.hailey_collet_1252270103.Cycle25.Assembly.Continuation

set_option autoImplicit false

namespace Candidate.SilPrior.FourthPower.TerminalTransfer
noncomputable section
open OAI.SevenEighths
open TargetCompatibility

/-- The complete canonical all-moduli target, with no analytical argument. -/
def CanonicalGoal : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
    (1749387 / 2000000 : ℝ) < s.re →
    ¬ (χ = 1 ∧ s = 1) →
    _root_.DirichletCharacter.LFunction χ s ≠ 0

/-- The beta consumed here is the pinned actual primitive-zero supremum. -/
theorem beta_primitive_supremum :
    HeckeZeroSupremum.beta = sSup HeckePrimitiveSupremum.primitiveSetWithSentinel :=
  HeckePrimitiveSupremum.beta_eq_primitive_supremum

/-- H may export any actual common shift; the target stays exactly theta. -/
theorem beta_of_common_probe {c : ℝ}
    (hprobe : Cycle25.UniformCommonProbe theta c) :
    HeckeZeroSupremum.beta ≤ theta :=
  Cycle25.beta_le_of_common_probe target_half target_seven_eighths hprobe

theorem hecke_of_beta (hbeta : HeckeZeroSupremum.beta ≤ theta)
    (χ : HeckeFamily.Character) (s : ℂ) (hs : theta < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) :
    HeckeFamily.LFunction χ s ≠ 0 :=
  HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ (hbeta.trans_lt hs) hpole

/-- Generic endpoint pending H. The pole condition is exactly the challenge's. -/
theorem dirichlet_of_beta (hbeta : HeckeZeroSupremum.beta ≤ theta)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1749387 / 2000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact Cycle25.dirichlet_of_hecke target_positive (hecke_of_beta hbeta)
    χ s hs hpole

theorem dirichlet_of_common_probe {c : ℝ}
    (hprobe : Cycle25.UniformCommonProbe theta c)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (1749387 / 2000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  dirichlet_of_beta (beta_of_common_probe hprobe) χ hs hpole

theorem canonical_of_beta (hbeta : HeckeZeroSupremum.beta ≤ theta) :
    CanonicalGoal := by
  intro q hq χ s hs hpole
  exact dirichlet_of_beta hbeta χ hs hpole

theorem canonical_of_common_probe {c : ℝ}
    (hprobe : Cycle25.UniformCommonProbe theta c) : CanonicalGoal :=
  canonical_of_beta (beta_of_common_probe hprobe)

/-- The intended actual H endpoint specializes the same proved adapter. -/
theorem canonical_of_return_probe
    (hprobe : Cycle25.UniformCommonProbe theta probeShift) : CanonicalGoal :=
  canonical_of_common_probe hprobe

end
end Candidate.SilPrior.FourthPower.TerminalTransfer
