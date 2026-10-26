/- Copyright (c) 2026 Sil. Apache-2.0.
Combines the large-source estimate with an explicit small-source input.
The large-source estimate is supplied internally.
-/
import Candidate.FourthPower.RepairedActualFrameSides

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedCombinedSideFromSmall
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open RepairedRootParameters RepairedRawContext RepairedSourceSideSupply
open RepairedContributionContract RepairedCombinedFinite RepairedActualFrameSides
open RepairedLargeContribution
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance (M : Id) [NeZero M] : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem contrary_provider_of_pending_small (hSmall : PendingSmallContribution) : ContraryRawSideProvider := by
  intro hcontra ε hε α instα decα M instM H hH W hW hWs bΦ hbΦ η η₀ Q instQ hQt hQ72 hQM hQη₀ N Kslot
  have hKslot : 1 ≤ Kslot := (RestoredRootSource.slotBound_spec W hW.continuous hWs).1
  have hβ := (contrary_inputs hcontra).1
  obtain ⟨JL,SL,h00L,CL,hCL,hLarge⟩ := uniform_large_contribution (M:=M) (H:=H) (hH:=hH)
    (RootShape α) (fun k => RootSlot k) N (2*N) (fun k => root_slot_card k)
    ε hε W hW hWs Kslot hKslot hβ Q hQt hQ72 hQM η η₀ hQη₀
  obtain ⟨JS,SS,h00S,CS,hCS,hSmall⟩ := hSmall hcontra ε hε α M H hH W hW hWs η η₀ Q hQt hQ72 hQM hQη₀
  refine ⟨max JL JS,SL∪SS,CL+CS,by linarith,Finset.mem_union_left _ h00L,?_⟩
  filter_upwards [hLarge,hSmall,eventually_ge_atTop (5:ℝ)] with Z hLargeZ hSmallZ hZ
  refine ⟨hZ,?_⟩
  intro k d hKroot
  have hL : ContributionFor d hε true JL SL CL := by
    intro f u hu hucap tp rows
    simpa only [contributionBound,amplitude] using hLargeZ k d f u hu hucap tp rows
  have hS : ContributionFor d hε false JS SS CS := hSmallZ k d
  have hraw := frame_raw_of_contributions d hε JL JS SL SS CL CS
    (zero_le_one.trans hCL) (zero_le_one.trans hCS) hL hS
  exact retained_of_frame_raw d (max JL JS) (SL∪SS) (CL+CS) hraw

end
end Candidate.FourthPower.RepairedCombinedSideFromSmall
