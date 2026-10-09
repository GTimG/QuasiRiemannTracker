import QRH.Geometry
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-! Frozen propositions, NOT proofs of nonvanishing. The final theorem witnesses
are absent until the complete analytic argument has been checked. -/
namespace QRH.Targets
open scoped _root_.DirichletCharacter

def AllDirichlet : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ},
    QRH.theta < s.re → ¬ (χ = 1 ∧ s = 1) →
    _root_.DirichletCharacter.LFunction χ s ≠ 0

def Zeta : Prop := ∀ {s : ℂ}, QRH.theta < s.re → riemannZeta s ≠ 0
end QRH.Targets
