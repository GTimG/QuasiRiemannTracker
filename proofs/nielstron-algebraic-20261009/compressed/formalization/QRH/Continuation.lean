import QRH.Geometry
import OAI.NumberTheory.DirichletL.Supremum

namespace QRH
noncomputable section



/-- Positive common loss and the exact shared continuation boundary. -/
theorem continuation_parameters {B ω σ : ℝ}
    (hω : 0 < ω) (hωB : ω < B - tightTheta) (hσ : 0 < σ) :
    let ε := min (B - tightTheta - ω) σ
    0 < ε ∧ tightTheta < B - ε ∧ B - ε < B ∧
      ∀ offset : ℝ, max (tightTheta + offset + ω) (B + offset - σ) = B + offset - ε := by
  dsimp only
  have he : 0 < min (B - tightTheta - ω) σ := lt_min (by linarith) hσ
  refine ⟨he, ?_, by linarith, ?_⟩
  · have := min_le_left (B - tightTheta - ω) σ
    linarith
  · intro offset
    rcases le_total (B - tightTheta - ω) σ with hh | hh
    · rw [min_eq_left hh, max_eq_left (by linarith)]
      ring
    · rw [min_eq_right hh, max_eq_right (by linarith)]

end
end QRH
