/- Copyright (c) 2026 Sil, Hailey Collet, ArviFoxy and predecessors. Apache-2.0.
Unconditional bound used to initiate the analytic return.
The accepted PR67 proof is reused through its pinned PR69 namespace,
with all inherited proof dependencies.
-/
import Candidate.FourthPower.OlderIncumbentContract
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.Incumbent

set_option autoImplicit false
namespace Candidate.FourthPower.OlderIncumbentSupplier
noncomputable section
open OAI.SevenEighths OlderIncumbentContract

/-- Retain the exact established PR67 result and its actual proof source. -/
theorem pr67_exact :
    HeckeZeroSupremum.beta≤(174963413/200000000:ℝ) :=
  QRH.Record1252270103Bootstrap.incumbent_beta

/-- Supplies the established bound without a source or target-bound assumption. -/
theorem actual : OlderIncumbentInput := by
  change HeckeZeroSupremum.beta≤cap
  exact pr67_exact.trans (by norm_num [cap])

/-- The previous theorem has positive reserve over the required A threshold. -/
theorem reserve_exact :
    cap-(174963413/200000000:ℝ)=369/200000000 := by
  norm_num [cap]

end
end Candidate.FourthPower.OlderIncumbentSupplier
