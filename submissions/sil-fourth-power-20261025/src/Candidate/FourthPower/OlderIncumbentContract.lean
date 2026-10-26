/- Copyright (c) 2026 Sil. Apache-2.0.
Interface for the established unconditional nonvanishing bound.
OlderIncumbentSupplier proves this input using PR67. The intermediate
return and the target bound are derived separately.
-/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace Candidate.FourthPower.OlderIncumbentContract
noncomputable section
open OAI.SevenEighths

/-- Exactly the older cap sufficient for the inherited C30 natural input. -/
def cap : ℝ := 87481891/100000000

/-- Explicit upstream A obligation, not an axiom or a target conclusion. -/
def OlderIncumbentInput : Prop := HeckeZeroSupremum.beta≤cap

/-- The scalar native cost corresponding to that cap. Its identification
with C30.naturalK/6 is performed in the actual C30 adapter. -/
theorem natural_cost (hPrior : OlderIncumbentInput) :
    2*HeckeZeroSupremum.beta-1≤(37481891/50000000:ℝ) := by
  change HeckeZeroSupremum.beta≤(87481891/100000000:ℝ) at hPrior
  linarith

end
end Candidate.FourthPower.OlderIncumbentContract
