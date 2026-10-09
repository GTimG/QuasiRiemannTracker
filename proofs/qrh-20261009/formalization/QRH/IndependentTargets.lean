import Mathlib.NumberTheory.LSeries.DirichletContinuation
import OAI.NumberTheory.DirichletL.Hecke.IdealBridge

/-! Independent literal specifications. No import of QRH geometry, target aliases,
certificates, or proposed proofs. No new character or L-function definitions. -/
namespace QRH.Independent
open scoped _root_.DirichletCharacter

def allDirichlet : Prop :=
  ∀ {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ},
    (874957019421 / 1000000000000 : ℝ) < s.re →
    ¬ (χ = 1 ∧ s = 1) → _root_.DirichletCharacter.LFunction χ s ≠ 0

def zeta : Prop :=
  ∀ {s : ℂ}, (874957019421 / 1000000000000 : ℝ) < s.re → riemannZeta s ≠ 0

def allHecke : Prop :=
  ∀ (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ),
    (874957019421 / 1000000000000 : ℝ) < s.re →
    (s ≠ 1 ∨ χ.residue ≠ 1) → OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0
end QRH.Independent
