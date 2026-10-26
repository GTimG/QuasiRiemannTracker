import Candidate.Target830.Source.CellGeometry

set_option autoImplicit false
namespace OAI.SevenEighths.Target830.Source.ErrorReconstruction
noncomputable section

theorem amplifier_bounds (P : SourcePlane) {b : ℝ}
    (hb : b ∈ Set.Icc widthLower widthUpper) :
    Source.amplifierMinimum≤P.amp b ∧ P.amp b≤1/75 := by
  have hh := Source.source_guards P hb
  exact ⟨hh.2.2.1,hh.2.2.2.1⟩

end
end OAI.SevenEighths.Target830.Source.ErrorReconstruction
#print axioms OAI.SevenEighths.Target830.Source.ErrorReconstruction.amplifier_bounds
