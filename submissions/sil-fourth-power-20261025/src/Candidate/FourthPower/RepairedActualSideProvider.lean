/- Copyright (c) 2026 Sil. Apache-2.0.
Combines the proved small-source and large-source estimates to supply
actual_contrary_raw_side_provider.
-/
import Candidate.FourthPower.RepairedCombinedSideFromSmall
import Candidate.FourthPower.RepairedSmallContribution

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedActualSideProvider
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open RepairedRootParameters RepairedRawContext RepairedSourceSideSupply
open RepairedContributionContract RepairedCombinedSideFromSmall
open RepairedSmallContribution
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance (M : Id) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

/-- This is a proof of the exact former pending proposition, not an
assumption of it. All finite families and constants retain their order. -/
theorem actual_small_contribution : PendingSmallContribution := by
  intro hcontra ε hε α instα decα M instM H hH W hW hWs η η₀ Q instQ hQt hQ72 hQM hQη₀ N Kslot
  have hKslot : 1 ≤ Kslot := (RestoredRootSource.slotBound_spec W hW.continuous hWs).1
  have hβ := (RepairedRootParameters.contrary_inputs hcontra).1
  obtain ⟨J,S,h00,C,hC,hsmall⟩ := uniform_small_contribution (M:=M) (H:=H) (hH:=hH)
    (RootShape α) (fun k => RootSlot k) N (2*N) (fun k => root_slot_card k)
    ε hε W hW hWs Kslot hKslot hβ Q hQt hQ72 hQM η η₀ hQη₀
  refine ⟨J,S,h00,C,hC,hsmall.mono ?_⟩
  intro Z hZ k d f u hu hucap tp rows
  simpa only [contributionBound,amplitude] using hZ k d f u hu hucap tp rows

/-- Actual all-root supplier. ContraryRawSideProvider itself describes
the contrary branch; there is no additional energy/source premise. -/
theorem actual_contrary_raw_side_provider : ContraryRawSideProvider :=
  contrary_provider_of_pending_small actual_small_contribution

end
end Candidate.FourthPower.RepairedActualSideProvider
