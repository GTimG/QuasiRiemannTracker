/- Copyright (c) 2026 Sil. Apache-2.0.
Ordinary-source interface for the analytic return.
The lemmas identify the source parameters and their numerical domains.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.Parameters
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract

set_option autoImplicit false

namespace Candidate.FourthPower.SourceContract
noncomputable section
open QRH.Record12518109Source QRH.Record12518109Existence

/-- Definitionally the fullSourceFace consumed by ReturnSourceFaces. -/
def face : SourceFace :=
  QRH.Record1252270103Source.globalFace sourceB sourceSlope sourceCap

theorem face_exact : face =
    QRH.Record1252270103Source.globalFace (99999/100000) (93/25) (3/50) := rfl

/-- No new source definition: this is the existing all-data uniform contract. -/
abbrev RequiredSource : Prop := UniformUnitFaceSource face

/-- In particular, the one mesh is selected before every ambient finite type. -/
theorem required_source_exact : RequiredSource ↔
    ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧
      UnitFaceSource
        (QRH.Record1252270103Source.globalFace (99999/100000) (93/25) (3/50))
        mesh ε := Iff.rfl

/-- The full source's individual plain cap is B, not the detector's 1/2. -/
theorem admissible_exact (m₁ m₂ S M : ℝ) :
    face.Admissible m₁ m₂ S M ↔
      0 ≤ m₁ ∧ m₁ ≤ (99999/100000 : ℝ)*M ∧
      0 ≤ m₂ ∧ m₂ ≤ (99999/100000 : ℝ)*M ∧
      0 ≤ S ∧ S ≤ (3/50 : ℝ)*M ∧
      m₁+m₂+(93/25 : ℝ)*S ≤ (99999/100000 : ℝ)*M := by
  simp only [face, QRH.Record1252270103Source.globalFace,
    SourceFace.Admissible, sourceB, sourceSlope, sourceCap, zero_mul]

end
end Candidate.FourthPower.SourceContract
