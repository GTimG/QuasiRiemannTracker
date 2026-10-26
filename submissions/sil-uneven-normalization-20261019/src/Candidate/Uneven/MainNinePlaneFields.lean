/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/
import Candidate.Uneven.MainAffineInput
import Candidate.Uneven.MainCountWindows
import Candidate.Target830.Physical.AffineFamily

set_option autoImplicit false
namespace OAI.SevenEighths.MainInitialTransport
noncomputable section
open HeckeFamily Cycle25ProbeFinalAssembly

/-- The inherited five source contracts are unchanged, with their plane names
embedded in the common nine-plane family. -/
theorem old_field_to_main {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (P : Target830.Count.Plane)
    (hin : Target830.Physical.InitialTransport.weighted_AffineFineInputAt P S) :
    weighted_AffineFineInputAt (MainCount.Plane.ofOld P) S := by
  cases P <;> exact hin


/-- The preliminary stage uses A2/C2 only; A/C are supplied after its bound.
The five inherited fields are available at both stages. -/
theorem stage_plane_fields {D : Cycle25.Weighted.MomentData} (S : WeightedSourceData D)
    (stage : MainCount.Stage)
    (hold : ∀ P : Target830.Count.Plane,
      Target830.Physical.InitialTransport.weighted_AffineFineInputAt P S)
    (hA : weighted_AffineFineInputAt stage.aPlane S)
    (hC : weighted_AffineFineInputAt stage.cPlane S) :
    ∀ P : MainCount.Plane, stage.Supports P → weighted_AffineFineInputAt P S := by
  intro P hP
  rcases hP with hP | hP | hP | hP | hP | hP | hP <;> subst P
  · exact old_field_to_main S .PR62 (hold .PR62)
  · exact old_field_to_main S .PR60 (hold .PR60)
  · exact old_field_to_main S .A (hold .A)
  · exact old_field_to_main S .C (hold .C)
  · exact old_field_to_main S .oldWeak (hold .oldWeak)
  · exact hA
  · exact hC

end
end OAI.SevenEighths.MainInitialTransport
