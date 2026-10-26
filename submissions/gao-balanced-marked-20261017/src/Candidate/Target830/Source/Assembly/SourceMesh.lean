import Candidate.Target830.Source.Assembly.Mesh
namespace OAI.SevenEighths.Target830.Source.Assembly
noncomputable section
/-- The fixed cap licenses the entire actual marked schedule. It is chosen
before the detector; final error monotonicity restores the requested error. -/
def cappedError (ε : ℝ) : ℝ := min ε (1/10000000000000000)
def sourceMesh (ε : ℝ) : ℝ := chosenMesh (cappedError ε)
theorem capped_error_bounds {ε : ℝ} (hε : 0<ε) :
    0<cappedError ε ∧ cappedError ε≤ε ∧
      cappedError ε≤1/10000000000000000 := by
  exact ⟨lt_min hε (by norm_num),min_le_left _ _,min_le_right _ _⟩
theorem source_mesh_pos {ε : ℝ} (hε : 0<ε) : 0<sourceMesh ε :=
  (chosen_mesh_admission (cappedError ε) (capped_error_bounds hε).1).1
end
end OAI.SevenEighths.Target830.Source.Assembly
#print axioms OAI.SevenEighths.Target830.Source.Assembly.source_mesh_pos
