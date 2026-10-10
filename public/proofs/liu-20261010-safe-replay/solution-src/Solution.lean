import RHZeroFreeExtension.CombinedPaperVerification
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace QRHBoundsPR3
open scoped _root_.DirichletCharacter

theorem allDirichlet {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : ((1507 - 2 * Real.sqrt 921) / 1653 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact CombinedPaper.algebraic_dirichlet_nonzero q (NeZero.ne q) χ s hs hpole

theorem zeta {s : ℂ} (hs : ((1507 - 2 * Real.sqrt 921) / 1653 : ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  by_cases h : s = 1
  · subst s
    exact riemannZeta_one_ne_zero
  · exact CombinedPaper.algebraic_zeta_nonzero s hs h

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : ((1507 - 2 * Real.sqrt 921) / 1653 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  exact CombinedPaper.algebraic_hecke_nonzero χ s hs hpole
end QRHBoundsPR3
