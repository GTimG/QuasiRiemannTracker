import QRH.Nonvanishing

/-! Real-part bounds for zeros of the original L-functions. -/

namespace QRH
open scoped _root_.DirichletCharacter

/-- Every zero of Mathlib's total `riemannZeta` lies at or left of `theta`.
Its assigned value at `1` is nonzero, so no exception is needed. -/
theorem riemannZeta_zero_re_le {s : ℂ} (hz : riemannZeta s = 0) : s.re ≤ theta :=
  le_of_not_gt fun hs => riemannZeta_ne_zero_of_theta_lt_re hs hz

/-- A Dirichlet L-function zero lies at or left of `theta`, apart from the
excluded principal pole `(χ, s) = (1, 1)`. -/
theorem DirichletCharacter.zero_re_le_or_exception
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) {s : ℂ}
    (hz : _root_.DirichletCharacter.LFunction χ s = 0) :
    s.re ≤ theta ∨ (χ = 1 ∧ s = 1) := by
  by_cases hexc : χ = 1 ∧ s = 1
  · exact Or.inr hexc
  · exact Or.inl (le_of_not_gt fun hs =>
      DirichletCharacter.LFunction_ne_zero_of_theta_lt_re χ hs hexc hz)

/-- Nonprincipal Dirichlet characters have no pole exception. -/
theorem DirichletCharacter.zero_re_le
    {q : ℕ} [NeZero q] (χ : _root_.DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (hz : _root_.DirichletCharacter.LFunction χ s = 0) : s.re ≤ theta :=
  (DirichletCharacter.zero_re_le_or_exception χ hz).resolve_right fun h => hχ h.1

/-- For the finite-order Eisenstein Hecke family, zeros lie at or left of
`theta`, apart from the excluded pole `s = 1` with `χ.residue = 1`. -/
theorem Hecke.zero_re_le_or_exception
    (χ : OAI.SevenEighths.HeckeFamily.Character) {s : ℂ}
    (hz : OAI.SevenEighths.HeckeFamily.LFunction χ s = 0) :
    s.re ≤ theta ∨ (s = 1 ∧ χ.residue = 1) := by
  by_cases hpole : s = 1 ∧ χ.residue = 1
  · exact Or.inr hpole
  · exact Or.inl (le_of_not_gt fun hs =>
      Hecke.LFunction_ne_zero_of_theta_lt_re χ s hs (not_and_or.mp hpole) hz)

/-- Within the same Hecke family, `χ.residue ≠ 1` removes the pole exception. -/
theorem Hecke.zero_re_le
    (χ : OAI.SevenEighths.HeckeFamily.Character) (hχ : χ.residue ≠ 1) {s : ℂ}
    (hz : OAI.SevenEighths.HeckeFamily.LFunction χ s = 0) : s.re ≤ theta :=
  (Hecke.zero_re_le_or_exception χ hz).resolve_right fun h => hχ h.2

end QRH
