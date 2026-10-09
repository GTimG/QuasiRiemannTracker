import QRH.Geometry
import OAI.NumberTheory.DirichletL.Supremum

namespace QRH
noncomputable section

/-- The order-theoretic part of continuation, with an arbitrary boundary.
The hypothesis still has to be proved for the actual analytic zero family. -/
theorem boundary_of_uniform_drop {S : Set ℝ} {a boundary : ℝ}
    (ha : a ≤ boundary)
    (hdrop : boundary < sSup (insert a S) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ S, x ≤ sSup (insert a S) - ε) :
    sSup (insert a S) ≤ boundary := by
  by_contra hle
  have hb : boundary < sSup (insert a S) := lt_of_not_ge hle
  obtain ⟨ε, hε, hx⟩ := hdrop hb
  have hu : sSup (insert a S) ≤ max boundary (sSup (insert a S) - ε) := by
    apply csSup_le (Set.insert_nonempty _ _)
    intro x hmem
    rcases Set.mem_insert_iff.mp hmem with rfl | hmem
    · exact ha.trans (le_max_left _ _)
    · exact (hx x hmem).trans (le_max_right _ _)
  have hv : max boundary (sSup (insert a S) - ε) < sSup (insert a S) :=
    max_lt hb (by linarith)
  exact (not_lt_of_ge hu) hv

/-- Positive common loss and the exact shared continuation boundary. -/
theorem continuation_parameters {B ω σ : ℝ}
    (hω : 0 < ω) (hωB : ω < B - theta) (hσ : 0 < σ) :
    let ε := min (B - theta - ω) σ
    0 < ε ∧ theta < B - ε ∧ B - ε < B ∧
      ∀ offset : ℝ, max (theta + offset + ω) (B + offset - σ) = B + offset - ε := by
  dsimp only
  have he : 0 < min (B - theta - ω) σ := lt_min (by linarith) hσ
  refine ⟨he, ?_, by linarith, ?_⟩
  · have := min_le_left (B - theta - ω) σ
    linarith
  · intro offset
    rcases le_total (B - theta - ω) σ with hh | hh
    · rw [min_eq_left hh, max_eq_left (by linarith)]
      ring
    · rw [min_eq_right hh, max_eq_right (by linarith)]

end
end QRH
