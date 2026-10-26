/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainParameters
import Candidate.Uneven.MainLowPaidMain
import Candidate.Uneven.MainPhysicalRowsPayment
set_option autoImplicit false
namespace OAI.SevenEighths.MainPhysical
open OAI OAI.SevenEighths
open OAI.SevenEighths.MainLow
open OAI.SevenEighths.Cycle63InitialMass
open OAI.SevenEighths.Cycle63Moment.LowBranch
open OAI.SevenEighths.LocalMoment
noncomputable section
open Sil.Uneven.MainSource
open scoped Classical BigOperators
local notation "O" => HeckeFamily.O
/-- The complete selected scalar cost, staged independently of physical
block types so the public receipt does not normalize their ancestry. -/
def mainLowCompleteSelectedCost (P : Plane) {Label : Type*} [Fintype Label]
    (ordinaryRows : Label→ Finset O) {e : ℝ}
    (select : (r : Label)→ ordinaryRows r→ BufferIndex e)
    (Ds : Label→ Finset (Ideal O)) (coefficient : Label→ Ideal O→ ℝ)
    (value : Label→ Ideal O→ O→ ℝ) : ℝ :=
  ∑r,∑D∈Ds r,coefficient r D*
    (∑z : ordinaryRows r,if bufferValue e (select r z) < ((1+P.q)/2) then value r D z.val else 0)

end
end OAI.SevenEighths.MainPhysical
