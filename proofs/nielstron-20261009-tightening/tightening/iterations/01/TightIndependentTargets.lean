import Mathlib.NumberTheory.LSeries.DirichletContinuation
import OAI.NumberTheory.DirichletL.Hecke.IdealBridge

/-! Literal targets, compiled without importing QRH or its geometry. -/
namespace QRH.TightIndependent
open scoped _root_.DirichletCharacter

def allDirichlet : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ},
    (874957019420871 / 1000000000000000 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) →
    _root_.DirichletCharacter.LFunction χ s ≠ 0

def zeta : Prop := ∀ {s : ℂ},
  (874957019420871 / 1000000000000000 : ℝ) < s.re → _root_.riemannZeta s ≠ 0

def allHecke : Prop :=
  ∀ (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ),
    (874957019420871 / 1000000000000000 : ℝ) < s.re → (s ≠ 1 ∨ χ.residue ≠ 1) →
    OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0
end QRH.TightIndependent
