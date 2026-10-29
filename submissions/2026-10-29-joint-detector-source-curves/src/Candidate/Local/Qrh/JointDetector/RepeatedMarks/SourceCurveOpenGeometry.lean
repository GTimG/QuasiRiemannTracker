/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.CompactScalarGates
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveGeometry

namespace Qrh.JointDetector.RepeatedMarks.SourceCurveOpenGeometry
noncomputable section
set_option autoImplicit false
open CurvedSourceStep

/-- The strict endpoint gates except for retained cap, which is paid exactly
by the positive selector. The last four entries control the open scalar face. -/
def gate (B L s A c : ℝ) : Fin 14 → ℝ :=
 ![1/10-6*A*(c-s),
   1-B+(L-2)*s,
   1-B+(L-2)*c-9/2*A*(c-s),
   1/20+3/2*(1-B)+(3/2*L-5/2)*s,
   1/20+3/2*(1-B)+(3/2*L-5/2)*c-9/2*A*(c-s),
   1-B+(L-1)*s,
   1-B+(L-1)*c-4*A*(c-s),
   1/3-2*s,
   1/3-2*c-3*A*(c-s),
   1-A, s, c-s, L-1, B]

theorem geometrySigns {p : Params} (hD : p.D=0) (hc0 : p.c0=p.c)
    (hc : p.c < 1/6) (hA : 0 < p.A)
    (hg : ∀ i, 0 < gate p.B p.L (crossing p) p.A p.c i) : GeometrySigns p := by
  apply linear_same_cap_geometry hD hc0 hc hA
  · simpa [gate] using hg 11
  · intro i hi
    fin_cases i
    · simpa [gate,geometryCoeff] using hg 0 |>.trans_le (by
        have hV : 0 ≤ 6*p.A*(p.c-crossing p) := by
          have hw := hg 11
          simp only [gate,Matrix.cons_val_succ,Matrix.cons_val_zero] at hw
          positivity
        linarith)
    · exact (hi rfl).elim
    · simpa [gate,geometryCoeff] using hg 1
    · simpa [gate,geometryCoeff] using hg 3
    · simpa [gate,geometryCoeff] using hg 5
    · simpa [gate,geometryCoeff] using hg 7
  · intro i hi
    have hlin : ∀ i : Fin 6, i ≠ 1 →
        geometryCoeff p i 0+geometryCoeff p i 1*(p.c-crossing p) =
          gate p.B p.L (crossing p) p.A p.c (![0,0,2,4,6,8] i) := by
      intro j hj
      fin_cases j <;> first | exact (hj rfl).elim |
        (norm_num [geometryCoeff,gate,hD,hc0]; ring)
    rw [hlin i hi]
    exact hg _

abbrev Perturbation := (ℝ × ℝ) × (ℝ × ℝ)

def zeroPerturbation : Perturbation := ((0,0),(0,0))

/-- One radius preserves every endpoint gate, uniformly along a compact
parent curve. Source arithmetic data are absent from this compactness step. -/
theorem uniform_gates {α : Type*} [PseudoMetricSpace α] [CompactSpace α] [Nonempty α]
    (B L s : α → ℝ) (c : ℝ)
    (hB : Continuous B) (hL : Continuous L) (hs : Continuous s)
    (hpos : ∀ x i, 0 < gate (B x) (L x) (s x) 0 c i) :
    ∃ δ > 0, ∀ x (e : Perturbation), dist e zeroPerturbation ≤ δ →
      ∀ i, 0 < gate (B x+e.1.1) (L x+e.1.2) (s x+e.2.1) e.2.2 c i := by
  have hgate (i : Fin 14) : Continuous (fun z : α × Perturbation =>
      gate (B z.1+z.2.1.1) (L z.1+z.2.1.2) (s z.1+z.2.2.1) z.2.2.2 c i) := by
    fin_cases i <;> simp only [gate,Matrix.cons_val_succ,Matrix.cons_val_zero] <;> fun_prop
  have hex (i : Fin 14) := compact_positive_perturbation zeroPerturbation _ (hgate i)
    (fun x => by simpa [zeroPerturbation] using hpos x i)
  choose r hr hvalid using hex
  let rs := Finset.univ.image r
  have hne : rs.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  refine ⟨rs.min' hne,?_,?_⟩
  · obtain ⟨i,hi,he⟩ := Finset.mem_image.mp (Finset.min'_mem rs hne)
    rw [←he]
    exact hr i
  · intro x e he i
    apply hvalid i x e
    exact he.trans (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i,by simp,rfl⟩))

end
end Qrh.JointDetector.RepeatedMarks.SourceCurveOpenGeometry
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurveOpenGeometry.uniform_gates
