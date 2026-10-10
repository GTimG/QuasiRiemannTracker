import Mathlib.NumberTheory.LSeries.DirichletContinuation
import OAI.NumberTheory.DirichletL.Hecke.IdealBridge

namespace QRHBoundsPR6
open scoped _root_.DirichletCharacter

theorem allDirichlet {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (10499 / 12000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  sorry

theorem zeta {s : ℂ} (hs : (10499 / 12000 : ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  sorry

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : (10499 / 12000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  sorry
end QRHBoundsPR6
