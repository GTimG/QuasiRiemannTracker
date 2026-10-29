/- Copyright (c) 2026 Joseph Bebel. -/
import Candidate.Local.Qrh.JointDetector.SlotHistogram
import Candidate.Local.Qrh.JointDetector.ActualSelectedNorm
import Candidate.Local.Qrh.JointDetector.PointwiseReturn

/-! Complete canonical consumer of the precise natural per-cell norm.
The remaining norm theorem is an explicit hypothesis, not an axiom. -/
namespace Qrh.JointDetector.CanonicalFromNorm
noncomputable section
set_option autoImplicit false

theorem actual_norm (h : NaturalSelectedCellNorm) : NaturalCount.ActualSelectedSlotNorm :=
  actualSelectedSlotNorm_of_aggregate
    (SlotHistogram.naturalAggregateSlotNorm_of_cell h)

theorem bound (h : NaturalSelectedCellNorm) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (87393871/100000000:ℝ) < s.re) (hpole : ¬ (χ=1 ∧ s=1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  PointwiseReturn.bound (actual_norm h) χ hs hpole

end
end Qrh.JointDetector.CanonicalFromNorm

#print axioms Qrh.JointDetector.CanonicalFromNorm.bound
