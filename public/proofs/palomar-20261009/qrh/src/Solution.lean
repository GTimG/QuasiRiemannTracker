import QRH.Nonvanishing

namespace QRHPalomar
open scoped _root_.DirichletCharacter

theorem allDirichlet {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hs : (874957019421 / 1000000000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) : _root_.DirichletCharacter.LFunction χ s ≠ 0 := by
  exact QRH.DirichletCharacter.LFunction_ne_zero_of_theta_lt_re χ hs hpole

theorem zeta {s : ℂ} (hs : (874957019421 / 1000000000000 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  exact QRH.riemannZeta_ne_zero_of_theta_lt_re hs

theorem allHecke (χ : OAI.SevenEighths.HeckeFamily.Character) (s : ℂ)
    (hs : (874957019421 / 1000000000000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : OAI.SevenEighths.HeckeFamily.LFunction χ s ≠ 0 := by
  exact QRH.Hecke.LFunction_ne_zero_of_theta_lt_re χ s hs hpole
end QRHPalomar
