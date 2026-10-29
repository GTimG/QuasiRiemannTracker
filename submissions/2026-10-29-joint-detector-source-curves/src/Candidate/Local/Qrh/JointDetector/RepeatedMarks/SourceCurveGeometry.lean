/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CurvedGeometry

namespace Qrh.JointDetector.RepeatedMarks.CurvedSourceStep
noncomputable section
set_option autoImplicit false

/-- A linear reserve is strictly positive throughout the interval when both
endpoints are positive. Its middle Bernstein coefficient is their average. -/
theorem quadraticSigns_linear {a b V : ℝ} (ha : 0 < a) (hb : 0 < a+b*V) :
    QuadraticSigns a b 0 V := by
  unfold QuadraticSigns
  exact ⟨ha,by linarith,by simpa using hb⟩

/-- The retained-cap reserve is proved exactly at the vanishing-selection
boundary. All other linear geometry reserves reduce to strict endpoint tests. -/
theorem linear_same_cap_geometry {p : Params}
    (hD : p.D=0) (hc0 : p.c0=p.c) (hcap : p.c < 1/6)
    (hA : 0 < p.A) (hwidth : 0 < p.c-crossing p)
    (hstart : ∀ i : Fin 6, i ≠ 1 → 0 < geometryCoeff p i 0)
    (hend : ∀ i : Fin 6, i ≠ 1 →
      0 < geometryCoeff p i 0+geometryCoeff p i 1*(p.c-crossing p)) :
    GeometrySigns p := by
  intro i
  apply Or.inl
  have hz : geometryCoeff p i 2=0 := by
    fin_cases i <;> simp [geometryCoeff,hD]
  rw [hz]
  apply quadraticSigns_linear
  · by_cases hi : i=1
    · subst i
      simpa [geometryCoeff,hc0] using hwidth
    · exact hstart i hi
  · by_cases hi : i=1
    · subst i
      have he : geometryCoeff p 1 0+geometryCoeff p 1 1*(p.c-crossing p) =
          (1-6*p.c)*p.A*(p.c-crossing p) := by
        norm_num [geometryCoeff,hc0,hD]
        ring
      rw [he]
      have hc : 0 < 1-6*p.c := by linarith
      exact mul_pos (mul_pos hc hA) hwidth
    · exact hend i hi

end
end Qrh.JointDetector.RepeatedMarks.CurvedSourceStep
#print axioms Qrh.JointDetector.RepeatedMarks.CurvedSourceStep.linear_same_cap_geometry
