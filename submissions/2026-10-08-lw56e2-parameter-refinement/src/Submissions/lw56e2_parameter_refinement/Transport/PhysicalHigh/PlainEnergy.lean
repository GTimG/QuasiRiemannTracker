/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalHigh/PlainEnergy.lean
Original SHA-256: 94460474177655bac3edb2e0002e9b25c3bfbbf2eb84e3f10b48c2056d182571
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CertifiedExistence

/-!
# Actual plain-moment energy certificate at kappa = 3/4

This is a specialization of the proved OpenAI003 analytic energy induction,
not an assumed energy estimate. Its `CertifiedBand` conclusion contains the
actual `ZeroAt` and `PositiveAt` arithmetic moment estimates with uniform
degree and seminorm controls. It avoids the source final-assembly `HighData`
structure, whose positive old-boundary gap is inappropriate for this task.

The family ceiling beta <= 7/8 is explicit. The contradiction regime for the
tuned candidate supplies beta >= 51/100. No new analytic axiom is introduced.
-/

namespace LW56e2.Transport.PhysicalHigh

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open HeckeFamily CenteredMomentEnergyCappedWidthInduction
open CenteredMomentEnergyCertifiedExistence CenteredMomentEnergyWidthSchedule

local notation "O" => HeckeFamily.O
variable {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
variable (M : Ideal O) [NeZero M]
local instance plainEnergyQuotient : Finite (O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- A producer for the actual terminal arithmetic energy band. The theorem
allows every finite number of physical slots and every positive error loss. -/
theorem actual_plain_energy_fixed_kappa
    (W : ℝ → ℂ) (hWs : Function.support W ⊆ Set.Icc 1 2)
    (hW : ContDiff ℝ ∞ W) (radial ε : ℝ) (hrad : 0 < radial) (hε : 0 < ε)
    (hbeta : (51 / 100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hceiling : HeckeZeroSupremum.beta ≤ 7 / 8) :
    CertifiedBand (α := Slot) M H hH W
      2 (1 / 4) (9 / 4) radial 0 1 (33 / 50) (33 / 50)
      2 (3 / 4) ε (count 2 ε) := by
  exact terminal_certificate (α := Slot) M H hH W
    1 2 (1 / 4) (9 / 4) radial 0 1 (33 / 50) (33 / 50) 2 (3 / 4) ε
    (by norm_num) hWs hW (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hrad (by norm_num) (by norm_num) (by norm_num) hε hbeta
    (by linarith)

end
end LW56e2.Transport.PhysicalHigh
